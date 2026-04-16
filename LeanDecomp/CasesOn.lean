import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.Helpers

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

/-- Peel off all applications from an expression to get the head and arguments.
    Returns (head, args) where args is in left-to-right order. -/
def peelArgs (e : Expr) : Expr × List Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × List Expr :=
    match e with
    | Expr.app f arg => go f (arg :: acc)
    | _ => (e, acc)
  go e []

/-- Information extracted from a casesOn application -/
structure CasesOnInfo where
  /-- The inductive type name -/
  indName : Name
  /-- The inductive type info -/
  indVal : InductiveVal
  /-- The discriminant expression (what we're matching on) -/
  discriminant : Expr
  /-- The motive (first arg to casesOn) -/
  motive : Expr
  /-- The case branches (one per constructor) -/
  caseBranches : List Expr
  /-- Arguments passed after the case branches (motive arguments like Eq.refl) -/
  motiveArgs : List Expr
  deriving Inhabited

/-- Try to extract casesOn information from an expression.
    Returns none if the expression is not a casesOn application. -/
def parseCasesOn (expr : Expr) : MetaM (Option CasesOnInfo) := do
  let (fn, args) := peelArgs expr
  let some constName := Expr.constName? fn
    | return none
  let nameStr := constName.toString
  if !nameStr.endsWith ".casesOn" then
    return none
  let some indName := constName.eraseSuffix? `casesOn
    | return none
  let some indInfo := (← getEnv).find? indName
    | return none
  let .inductInfo indVal := indInfo
    | return none
  -- casesOn arguments layout: [motive, params..., indices..., discriminant, cases..., motiveArgs...]
  let numParams := indVal.numParams
  let numIndices := indVal.numIndices
  let numCtors := indVal.ctors.length
  let discriminantIdx := 1 + numParams + numIndices
  let casesStartIdx := discriminantIdx + 1
  if args.length < casesStartIdx + numCtors then
    return none
  let motive := args[0]!
  let discriminant := args[discriminantIdx]!
  let caseBranches := (List.range numCtors).map fun i => args[casesStartIdx + i]!
  let motiveArgsStartIdx := casesStartIdx + numCtors
  let motiveArgs := args.drop motiveArgsStartIdx
  return some {
    indName := indName
    indVal := indVal
    discriminant := discriminant
    motive := motive
    caseBranches := caseBranches
    motiveArgs := motiveArgs
  }

/-- Check if the casesOn motive has equality parameters (from `cases h : disc`).
    A motive like `fun (t : T) => ∀ (h : disc = t), Goal` indicates generalized equations.
    For indexed families, there may be multiple: `∀ (h2 : s = a_1) (h3 : t = a_2) (h : HEq ...), Goal`.
    Returns (name of first eq binder, total count of eq/heq forall binders) if found. -/
private def motiveEqInfo (motive : Expr) : MetaM (Option (String × Nat)) := do
  lambdaTelescope motive fun _ body => do
    if body.isForall then
      forallTelescope body fun binders _ => do
        if binders.isEmpty then return none
        -- Check if the first binder is an Eq or HEq
        let firstBinderType ← inferType binders[0]!
        let (fn, _) := peelArgs firstBinderType
        if !(fn.isConstOf ``Eq || fn.isConstOf ``HEq) then return none
        let some fvarId := binders[0]!.fvarId?
          | return none
        let decl ← fvarId.getDecl
        let name := decl.userName.eraseMacroScopes.toString
        -- Count how many consecutive Eq/HEq binders there are
        let mut count := 0
        for b in binders do
          let bType ← inferType b
          let (bfn, _) := peelArgs bType
          if bfn.isConstOf ``Eq || bfn.isConstOf ``HEq then
            count := count + 1
          else
            break
        return some (name, count)
    else return none

/-- Substitute selected fvars in an expression. -/
private def substFVars (e : Expr) (substs : Array (FVarId × Expr)) : Expr :=
  substs.foldl (init := e) fun acc (fid, replacement) =>
    acc.replace fun t =>
      match t with
      | .fvar fid' => if fid' == fid then some replacement else none
      | _ => none

/-- Infer substitutions for constructor-local index fvars (e.g. `s_1`) by
    scanning Eq/HEq constraints in the branch body. -/
private def mkCtorIndexSubsts
    (ctorParamsAll : Array Expr) (body : Expr) : MetaM (Array (FVarId × Expr)) := do
  let mut ctorFVars : Array FVarId := #[]
  for p in ctorParamsAll do
    if let some fid := p.fvarId? then
      ctorFVars := ctorFVars.push fid

  let containsCtorFVar (fid : FVarId) : Bool :=
    ctorFVars.any (· == fid)

  let addIfCtorIndex (substs : Array (FVarId × Expr)) (lhs rhs : Expr) : Array (FVarId × Expr) :=
    match lhs.fvarId? with
    | some fid =>
        if containsCtorFVar fid && !substs.any (fun (fid', _) => fid' == fid) then
          substs.push (fid, rhs)
        else
          substs
    | none => substs

  let rec visit (e : Expr) (acc : Array (FVarId × Expr)) : Array (FVarId × Expr) :=
    let (fn, args) := peelArgs e
    let acc :=
      if fn.isConstOf ``Eq && args.length >= 3 then
        let lhs := args[1]!
        let rhs := args[2]!
        let acc := addIfCtorIndex acc lhs rhs
        addIfCtorIndex acc rhs lhs
      else if fn.isConstOf ``HEq && args.length >= 4 then
        let lhs := args[1]!
        let rhs := args[3]!
        let acc := addIfCtorIndex acc lhs rhs
        addIfCtorIndex acc rhs lhs
      else
        acc

    match e with
    | .app f a =>
        let acc := visit f acc
        visit a acc
    | .lam _ t b _ =>
        let acc := visit t acc
        visit b acc
    | .forallE _ t b _ =>
        let acc := visit t acc
        visit b acc
    | .letE _ t v b _ =>
        let acc := visit t acc
        let acc := visit v acc
        visit b acc
    | .mdata _ b =>
        visit b acc
    | .proj _ _ b =>
        visit b acc
    | _ =>
        acc

  return visit body #[]

/-- Get the user name of an fvar expression, if it is one. -/
private def getDiscriminantName (disc : Expr) (lctx : LocalContext) : Option String :=
  if let .fvar fvarId := disc then
    if let some decl := lctx.find? fvarId then
      let name := decl.userName.eraseMacroScopes.toString
      let lastSegment := (name.splitOn ".").reverse.headD name
      some lastSegment
    else none
  else none

/-- Detect if a branch body is a contradiction proof that should be omitted.
    In grind-generated proofs, impossible branches use patterns like:
    - `Lean.Grind.intro_with_eq` with an impossible equation
    - `False.casesOn` / `False.elim`
    - `noConfusion_of_Nat` with different constructors
    We detect this by checking if the body (or the body after stripping
    noConfusion wrappers) is a proof of False from contradictory constructor equalities. -/
private def isBranchContradiction (body : Expr) : MetaM Bool := do
  let (fn, _) := peelArgs body
  if let some constName := fn.constName? then
    -- Grind uses intro_with_eq for impossible branches
    if constName == ``Lean.Grind.intro_with_eq then
      return true
    -- Direct False elimination
    if constName == ``False.casesOn || constName == ``False.elim || constName == ``False.rec then
      return true
    -- absurd produces False.elim after unfolding
    if constName == ``absurd then
      return true
  -- After simplification, noConfusion may leave Eq.ndrec patterns.
  -- Check if the return type is provably False-based by trying headBeta.
  let mut reduced := body
  while reduced.isApp && reduced.getAppFn.isLambda do
    reduced := reduced.headBeta
  let (rfn, _) := peelArgs reduced
  if let some rname := rfn.constName? then
    if rname == ``False.casesOn || rname == ``False.elim || rname == ``False.rec || rname == ``absurd then
      return true
  return false

/-- Handle `*.casesOn` applications - generate a `cases` tactic.
    Detects when expr is an application of an inductive type's casesOn eliminator.
    Takes callbacks for decompileExpr and assignIntroNames to avoid circular dependencies.
  Supports generalized equality motives by rebinding branch-local equality
  parameters to the motive arguments and substituting constructor-local fvars. -/
def tryDecompCasesOn (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String)
    (decompileExpr : DecompileCallback)
    (assignIntroNames : AssignIntroNamesCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let some info ← parseCasesOn expr
      | return none
    -- If the discriminant's head is a grind-internal normalization helper
    -- (e.g. `Lean.Grind.of_eq_eq_true`, `Lean.Grind.or_of_and_eq_false`), defer
    -- to `tryDecompOmega` rather than emitting a `cases` with an unreadable
    -- scrutinee. We check only the head constant — checking transitively would
    -- falsely trigger on innocuous `Classical.em (prop-containing-grind-term)`.
    if let some n := info.discriminant.getAppFn.constName? then
      if n.toString.startsWith "Lean.Grind." then return none
    let ctorNames := info.indVal.ctors

    -- Check if the motive has equality parameters (generalized equation pattern)
    -- If so, get the name of the first equality binder and the count
    let eqInfo ← motiveEqInfo info.motive
    let hasEqMotive := eqInfo.isSome

    let mut alts : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
    let mut used := used

    for (ctorName, caseBranch) in ctorNames.zip info.caseBranches do
      let ctorShortName := ctorName.getString!
      let ctorIdent := mkIdent (Name.mkSimple ctorShortName)

      -- Check if this branch is a contradiction (impossible constructor).
      -- We enter the lambda telescope and check the body.
      let isContradiction ← Meta.lambdaTelescope caseBranch fun _xs body => do
        isBranchContradiction body

      if isContradiction then
        continue

      let (branchTactics, ctorParamNames, used') ← Meta.lambdaTelescope caseBranch fun xs body => do
        let telescopeLctx ← getLCtx
        let telescopeInsts ← getLocalInstances

        -- Separate constructor params from the trailing equality proof params.
        -- With generalized equations, the branch lambdas may have 1+ trailing
        -- equality params appended by the casesOn elaboration. We detect them
        -- by checking each trailing param's type for Eq/HEq.
        let mut numTrailingEq := 0
        if hasEqMotive then
          -- Count trailing Eq/HEq params from the end
          let mut i := xs.size
          while i > 0 do
            i := i - 1
            let paramType ← inferType xs[i]!
            let (fn, _) := peelArgs paramType
            if fn.isConstOf ``Eq || fn.isConstOf ``HEq then
              numTrailingEq := numTrailingEq + 1
            else
              break

        let ctorParamCount := xs.size - numTrailingEq
        let mut ctorParamsAll : Array Expr := #[]
        let mut ctorParams : Array Expr := #[]
        for i in List.range ctorParamCount do
          let x := xs[i]!
          ctorParamsAll := ctorParamsAll.push x
          let xDecl ← getFVarLocalDecl x
          if xDecl.binderInfo.isExplicit then
            ctorParams := ctorParams.push x

        let mut trailingEqParams : Array Expr := #[]
        for i in List.range numTrailingEq do
          trailingEqParams := trailingEqParams.push xs[ctorParamCount + i]!

        -- Assign names for constructor params and track them
        let (ctorParamNames, newLctx, usedAfterCtorParams) ←
          if ctorParams.size > 0 then
            assignIntroNames ctorParams used
          else
            pure ([], telescopeLctx, used)


        let ctorIndexSubsts ← mkCtorIndexSubsts ctorParamsAll body
        let bodyAfterCtorIndex := substFVars body ctorIndexSubsts

        -- Handle trailing Eq/HEq params from generalized equation motives.
        --
        -- When casesOn has a generalized equation motive (`cases h : disc`),
        -- each branch has trailing eq params (e.g., `h : s = Stmt.skip`) and
        -- the body may be wrapped in Eq.ndrec/Eq.rec for transport.
        --
        -- We substitute eq params with the corresponding motive args (e.g.,
        -- `Eq.refl s`), apply remaining motive args, then clean up any
        -- Eq.rec transport artifacts.
        --
        -- The substitution is type-incorrect at the Expr level (Eq.refl s
        -- has type s = s, not s = Stmt.skip), but downstream handlers
        -- (contradiction, noConfusion) consume these terms before
        -- re-elaboration. For cases where Eq.rec remains at the top level,
        -- we strip it when the base is a lambda (the generalized equation
        -- transport pattern), as opposed to noConfusion's Eq.rec which has
        -- a constant-headed base.
        let motiveArgCount := info.motiveArgs.length
        let bindableEqCount := Nat.min numTrailingEq motiveArgCount

        let mut innerBody : Expr := bodyAfterCtorIndex

        -- Substitute trailing eq params with corresponding motive args, then
        -- apply any remaining motive args as function arguments.
        let mut eqParamSubsts : Array (FVarId × Expr) := #[]
        for i in List.range bindableEqCount do
          let eqParam := trailingEqParams[i]!
          if let some fid := eqParam.fvarId? then
            eqParamSubsts := eqParamSubsts.push (fid, info.motiveArgs[i]!)
        innerBody := substFVars innerBody eqParamSubsts
        let remainingMotiveArgs := info.motiveArgs.drop bindableEqCount
        innerBody := remainingMotiveArgs.foldl (init := innerBody) fun acc arg =>
          mkApp acc arg

        -- Clean up Eq.ndrec/Eq.rec artifacts from the substitution.
        -- When a generalized equation motive produces `Eq.ndrec ... (Eq.symm h) h`,
        -- substituting `h ↦ Eq.refl s` yields a type-incorrect intermediate:
        --   `Eq.rec ... base ... (Eq.symm (Eq.refl s)) (Eq.refl s)`
        -- where base is a lambda. Beta-reduce to collapse inlined Eq.ndrec,
        -- then strip Eq.rec when the base is a lambda (the eq transport pattern).
        -- We do NOT strip Eq.rec with non-lambda bases (e.g. noConfusion internals).
        if bindableEqCount > 0 then
          while innerBody.isHeadBetaTarget do
            innerBody := innerBody.headBeta
          let mut stripping := true
          while stripping do
            let (topFn, topArgs) := peelArgs innerBody
            if let some cname := topFn.constName? then
              if (cname == ``Eq.ndrec || cname == ``Eq.rec) && topArgs.length >= 6 then
                let base := topArgs[3]!
                if base.isLambda then
                  let extraArgs := topArgs.drop 6
                  let result := extraArgs.foldl (init := base) fun acc arg => mkApp acc arg
                  let mut r := result
                  while r.isHeadBetaTarget do
                    r := r.headBeta
                  innerBody := r
                  continue
            stripping := false
          -- For indexed families, the inner body may still contain transport
          -- chains (T.casesOn + nested Eq.ndrec) from decomposing index
          -- equalities. If Eq.rec is still at the head after stripping, use
          -- whnf to computationally collapse these via iota-reduction.
          let (headFn, _) := peelArgs innerBody
          if let some cname := headFn.constName? then
            if cname == ``Eq.ndrec || cname == ``Eq.rec then
              innerBody ← Meta.whnf innerBody

        -- Recursively decompile the inner body
        let (bodyTactics, _usedInBranch) ← decompileExpr innerBody newLctx telescopeInsts usedAfterCtorParams
        return (bodyTactics, ctorParamNames, used)

      used := used'
      let branchTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$branchTactics]*)

      -- Start with quasi-quote pattern that has no binders
      let baseAlt ← `(Lean.Parser.Tactic.inductionAlt| | $ctorIdent => $branchTacticSeq)


      -- If we have parameter names, modify the syntax tree to insert them as plain identifiers
      -- This controls what names `cases` introduces (you were right!)
      let altStx := if ctorParamNames.isEmpty then
        baseAlt
      else
        -- Navigate into the AST and insert binder identifiers after the constructor group
        -- Working structure: inductionAltLHS[pipe, group[null[], ctorIdent], null[param1, param2, ...]]
        match baseAlt.raw with
        | .node info kind #[lhsWrapper, rhsWrapper] =>
            match lhsWrapper with
            | .node lhsInfo `null #[altLHS] =>
                match altLHS with
                | .node altLHSInfo `Lean.Parser.Tactic.inductionAltLHS children =>
                    -- children should be: #[pipe, group, emptyNull]
                    -- We need to replace emptyNull with: null[binders...]
                    if children.size >= 3 then
                      -- Get the source info from the group to use for the binders node
                      let sourceInfo := match children[1]! with
                        | .node info _ _ => info
                        | .atom info _ => info
                        | _ => SourceInfo.none

                      -- Create identifier syntax nodes for each parameter name
                      let binderIdents : Array Syntax := ctorParamNames.toArray.map fun name =>
                        let ident : Ident := mkIdent (Name.mkSimple name)
                        ident.raw

                      -- Create a null node containing the binder idents
                      let bindersNode := Syntax.node sourceInfo `null binderIdents

                      -- REPLACE the third child (empty null) with our binders null node
                      let newChildren := children.set! 2 bindersNode

                      let newAltLHS := Syntax.node altLHSInfo `Lean.Parser.Tactic.inductionAltLHS newChildren
                      let newLHSWrapper := Syntax.node lhsInfo `null #[newAltLHS]
                      let newAlt := Syntax.node info kind #[newLHSWrapper, rhsWrapper]
                      ⟨newAlt⟩
                    else
                      baseAlt
                | _ => baseAlt
            | _ => baseAlt
        | _ => baseAlt

      alts := alts.push altStx

    let discriminantStx ← delabToRefinableSyntax info.discriminant
    let casesTac ← if let some (eqName, _) := eqInfo then do
      let discName := getDiscriminantName info.discriminant lctx
      let eqBinderName :=
        if discName == some eqName then
          s!"{eqName}_eq"
        else
          eqName
      let hIdent : TSyntax `Lean.binderIdent ←
        `(Lean.binderIdent| $(mkIdent (Name.mkSimple eqBinderName)):ident)
      `(tactic| cases $hIdent : $discriminantStx:term with $[$alts:inductionAlt]*)
    else
      `(tactic| cases $discriminantStx:term with $[$alts:inductionAlt]*)

    return some (#[casesTac], used)

end LeanDecomp
