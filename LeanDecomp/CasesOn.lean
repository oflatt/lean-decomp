import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.Helpers

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

/-- Replace the (empty) binder list of an `inductionAltLHS` node with the given
    binder identifiers.  An `inductionAlt` parses to
    `node[pipe, ctorGroup, bindersNull]` wrapped in an outer LHS-wrapper
    `null` node and a `tacticSeq` RHS — so the surgery is: navigate
    `node[lhsWrapper, rhsWrapper]` → `node[null[altLHS]]` →
    `inductionAltLHS[…, …, emptyNull]` and replace the third child with a
    fresh `null` node carrying the binder idents.

    We do this raw rather than via the quasi-quote `(| ctor a b c => …)` form
    because `inductionAltLHS`'s binder slot is a plain identifier list, not
    a `term` antiquotation, so quasi-quote can't splice it.

    Returns the input unchanged if the AST shape doesn't match (defensive
    against future grammar changes). -/
private def setInductionAltBinders
    (alt : TSyntax ``Lean.Parser.Tactic.inductionAlt) (binderNames : Array String)
  : TSyntax ``Lean.Parser.Tactic.inductionAlt :=
  match alt.raw with
  | .node info kind #[lhsWrapper, rhsWrapper] =>
    match lhsWrapper with
    | .node lhsInfo `null #[altLHS] =>
      match altLHS with
      | .node altLHSInfo ``Lean.Parser.Tactic.inductionAltLHS children =>
        if children.size >= 3 then
          let sourceInfo := match children[1]! with
            | .node info _ _ => info
            | .atom info _ => info
            | _ => SourceInfo.none
          let binderIdents : Array Syntax := binderNames.map fun name =>
            (mkIdent (Name.mkSimple name)).raw
          let bindersNode := Syntax.node sourceInfo `null binderIdents
          let newChildren := children.set! 2 bindersNode
          let newAltLHS := Syntax.node altLHSInfo ``Lean.Parser.Tactic.inductionAltLHS newChildren
          let newLHSWrapper := Syntax.node lhsInfo `null #[newAltLHS]
          ⟨Syntax.node info kind #[newLHSWrapper, rhsWrapper]⟩
        else alt
      | _ => alt
    | _ => alt
  | _ => alt

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

/-- Run `MVarId.cases` on `expr`'s discriminant.  Allocates a fresh synthetic-
    opaque mvar of `expr`'s type, generalizes the discriminant if it's not
    already a fvar, then calls `mvarId.cases` to produce per-branch subgoals
    whose lctxs reflect the real `cases`-substituted state.

    Returns `none` when `MVarId.cases` fails (unusual goal shape, or the
    generalized-motive case where `mvarId.cases` doesn't reproduce the
    `heq : disc = ctor xs` hypothesis — see the README's "Generalized motives
    extension" item for what was tried).  The caller then falls back to the
    synthesized `lambdaTelescope` lctx. -/
private def runMVarIdCases (expr : Expr) (info : CasesOnInfo)
    : TacticM (Option (Array Meta.CasesSubgoal)) := do
  try
    let exprTy ← Meta.inferType expr
    let outerMvar ← Meta.mkFreshExprMVar (some exprTy) .syntheticOpaque
    let (majorFVarId, mvarAfterGen) ←
      if let some fid := info.discriminant.fvarId? then
        pure (fid, outerMvar.mvarId!)
      else
        let (newFvarIds, newMvarId) ← outerMvar.mvarId!.generalize
          #[{ expr := info.discriminant }]
        pure (newFvarIds[0]!, newMvarId)
    let subgoals ← mvarAfterGen.cases majorFVarId
    pure (some subgoals)
  catch _ =>
    pure none

/-- Substitute trailing eq-motive params with the corresponding motive args,
    then strip residual `Eq.ndrec` / `Eq.rec` transports whose base is a
    lambda.  This is the "generalized equation motive" cleanup.

    The substitution is type-incorrect at the Expr level (`Eq.refl s` has
    type `s = s`, not `s = Stmt.skip`), but downstream handlers
    (`contradiction`, `noConfusion`) consume the type-incorrect intermediate
    before re-elaboration.  Stripping is gated on `base.isLambda` so we don't
    erase `noConfusion`'s `Eq.rec` (whose base is const-headed).

    For indexed families a `T.casesOn + nested Eq.ndrec` chain may remain
    after the lambda strip; iota-reduce via `whnf` to collapse those. -/
private def cleanupEqMotiveTransport (innerBody : Expr) (motiveArgs : List Expr)
    (trailingEqParams : Array Expr) (numTrailingEq : Nat) : MetaM Expr := do
  let motiveArgCount := motiveArgs.length
  let bindableEqCount := Nat.min numTrailingEq motiveArgCount
  let mut innerBody := innerBody
  let mut eqParamSubsts : Array (FVarId × Expr) := #[]
  for i in List.range bindableEqCount do
    let eqParam := trailingEqParams[i]!
    if let some fid := eqParam.fvarId? then
      eqParamSubsts := eqParamSubsts.push (fid, motiveArgs[i]!)
  innerBody := substFVars innerBody eqParamSubsts
  let remainingMotiveArgs := motiveArgs.drop bindableEqCount
  innerBody := remainingMotiveArgs.foldl (init := innerBody) fun acc arg =>
    mkApp acc arg
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
    let (headFn, _) := peelArgs innerBody
    if let some cname := headFn.constName? then
      if cname == ``Eq.ndrec || cname == ``Eq.rec then
        innerBody ← Meta.whnf innerBody
  return innerBody

/-- Build the final `cases <disc> with | ctor₁ … => … | ctor₂ … => …` (or
    `cases h : <disc> with …` for generalized-equation motives) tactic from
    the discriminant term, optional eq-binder name, and the pre-built alt
    syntax. -/
private def mkCasesWithAltsTactic (discTerm : Term)
    (eqBinderName? : Option String)
    (alts : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt))
    : TermElabM (TSyntax `tactic) := do
  match eqBinderName? with
  | some eqName =>
    let hIdent : TSyntax `Lean.binderIdent ←
      `(Lean.binderIdent| $(mkIdent (Name.mkSimple eqName)):ident)
    `(tactic| cases $hIdent : $discTerm:term with $[$alts:inductionAlt]*)
  | none =>
    `(tactic| cases $discTerm:term with $[$alts:inductionAlt]*)

/-- Handle `*.casesOn` applications — generate a `cases` tactic.
    Detects when `expr` is an application of an inductive type's casesOn
    eliminator.  Takes callbacks for `decompileExpr` and `assignIntroNames`
    to avoid circular dependencies.  Supports generalized equality motives
    by rebinding branch-local equality parameters to the motive arguments
    and substituting constructor-local fvars.

    Implementation walks three phases per branch:
    1. Telescope the branch lambda, separate ctor params from trailing eq
       params, assign user names via `assignIntroNames`.
    2. `cleanupEqMotiveTransport`: substitute eq params with motive args and
       strip residual `Eq.rec` / `Eq.ndrec` transports (load-bearing for
       downstream `contradiction` / `noConfusion`).
    3. Recurse on the cleaned body — using the real substituted lctx from
       `runMVarIdCases`'s subgoal when available, falling back to the
       synthesized telescope lctx for generalized motives. -/
def tryDecompCasesOn (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances)
    (decompileExpr : DecompileCallback)
    (assignIntroNames : AssignIntroNamesCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let some info ← parseCasesOn expr
      | return none
    let ctorNames := info.indVal.ctors

    -- Check if the motive has equality parameters (generalized equation pattern)
    -- If so, get the name of the first equality binder and the count
    let eqInfo ← motiveEqInfo info.motive
    let hasEqMotive := eqInfo.isSome

    -- Decompile the discriminant up front when we'll need a `have hOr := ...`
    -- wrapper. If recursive decompilation throws (e.g. exact-fallback size
    -- guard on a giant chain), return `none` so dispatch can continue with
    -- another handler instead of propagating the error out.
    let useHaveWrapper := info.discriminant.isApp && info.discriminant.fvarId?.isNone
    let savedUsed ← getUsed
    let discBundle? : Option (Array (TSyntax `tactic)) ←
      if useHaveWrapper then
        try
          let tacs ← LeanDecomp.decompileOrExact info.discriminant lctx localInsts decompileExpr
          pure (some tacs)
        catch _ =>
          set savedUsed
          pure none
      else
        pure (some #[])
    let some discTacticsEarly := discBundle?
      | return none

    let mut alts : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]

    -- Set up a synthetic outer mvar and run `MVarId.cases` once.  This
    -- produces subgoals whose lctxs reflect the real cases substitution
    -- (the discriminant fvar is replaced by the constructor application
    -- throughout the lctx, just as the real `cases` tactic would do).
    -- Recursive per-branch decomp then runs in the real substituted lctx —
    -- matching the **decompiler invariant** that every recursive call sees
    -- the proof state the real run would produce.
    --
    -- Generalized motives (`cases h : disc with`) currently take the older
    -- Meta.lambdaTelescope path because `MVarId.cases` doesn't reproduce the
    -- trailing `heq : disc = ctor xs` hypothesis.  A naive extension that
    -- generalizes with `hName?` and substitutes the eq param with the real
    -- eq fvar broke `LeanDecomp.simple`: the old body's `Eq.rec` cleanup
    -- (substituting `heq → Eq.refl s` and stripping the resulting transport)
    -- is load-bearing for downstream handlers like `contradiction` and
    -- `noConfusion` — they consume the type-incorrect intermediate that the
    -- cleanup produces.  Improving this is documented in the README.
    let casesSubgoals : Option (Array Meta.CasesSubgoal) ←
      if hasEqMotive then pure none else runMVarIdCases expr info

    -- Track whether every branch's body is exactly the single tactic `lia`.
    -- When that holds for an `Or` cases-split with a `have hOr := by lia`
    -- wrapper (the Sum L55/L81 hot pattern), we attempt to collapse the
    -- entire `have hOr; cases hOr | inl _ => lia | inr _ => lia` to one bare
    -- `lia` — see the post-loop validation block below.
    let liaRef : TSyntax `tactic ← `(tactic| lia)
    let liaKind := liaRef.raw.getKind
    let mut allBranchesAreLia : Bool := info.indName == ``Or

    for (ctorName, caseBranch) in ctorNames.zip info.caseBranches do
      let ctorShortName := ctorName.getString!
      let ctorIdent := mkIdent (Name.mkSimple ctorShortName)

      -- Check if this branch is a contradiction (impossible constructor).
      -- We enter the lambda telescope and check the body.
      -- Only skip for multi-constructor types: for a single-constructor type
      -- like `And`, skipping the only branch leaves `cases hOr with` empty,
      -- which Lean rejects with "Alternative `intro` has not been provided".
      let isContradiction ← Meta.lambdaTelescope caseBranch fun _xs body => do
        isBranchContradiction body

      if isContradiction && ctorNames.length > 1 then
        continue

      -- Locate the matching subgoal from MVarId.cases (if we took that path).
      let matchingSubgoal? : Option Meta.CasesSubgoal :=
        casesSubgoals.bind fun subs =>
          subs.find? (fun s => s.ctorName == some ctorName)

      let (branchTactics, ctorParamNames) ← Meta.lambdaTelescope caseBranch fun xs body => do
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
        let (ctorParamNames, newLctx) ←
          if ctorParams.size > 0 then
            assignIntroNames ctorParams
          else
            pure ([], telescopeLctx)

        let ctorIndexSubsts ← mkCtorIndexSubsts ctorParamsAll body
        let bodyAfterCtorIndex := substFVars body ctorIndexSubsts

        -- Handle trailing Eq/HEq params from generalized equation motives.
        -- See `cleanupEqMotiveTransport` for the load-bearing details.
        let innerBody ← cleanupEqMotiveTransport bodyAfterCtorIndex
          info.motiveArgs trailingEqParams numTrailingEq

        -- Recurse on the branch body.  When `MVarId.cases` succeeded above,
        -- run the recursion in the subgoal's real (substituted) lctx —
        -- maintaining the decompiler invariant.  Otherwise (generalized
        -- motive, or `MVarId.cases` failed) fall back to the synthesized
        -- `newLctx` and let the outer replay catch errors.
        let bodyTactics ←
          match matchingSubgoal? with
          | some sub =>
              -- Map the telescope's `xs` to the subgoal's `fields` so the
              -- branch body references the real cases-introduced fvars
              -- (whose surrounding lctx has the discriminant substituted).
              let mut substs : Array (FVarId × Expr) := #[]
              for i in List.range (Nat.min ctorParamCount sub.fields.size) do
                if let some fid := xs[i]!.fvarId? then
                  substs := substs.push (fid, sub.fields[i]!)
              let innerBodyMapped := substFVars innerBody substs
              -- Rename the subgoal's constructor-arg fields to our chosen
              -- ctorParamNames so the recursive lctx exposes the names we'll
              -- emit in the alt syntax.
              let renamedSubgoal ← do
                let mut subLctx ← sub.mvarId.withContext getLCtx
                let mut nameIdx := 0
                for i in List.range ctorParamCount do
                  if let some fid := sub.fields[i]!.fvarId? then
                    if nameIdx < ctorParamNames.length then
                      subLctx := subLctx.setUserName fid (Name.mkSimple ctorParamNames[nameIdx]!)
                      nameIdx := nameIdx + 1
                pure subLctx
              let subInsts ← sub.mvarId.withContext getLocalInstances
              LeanDecomp.decompileOrExact innerBodyMapped renamedSubgoal subInsts decompileExpr
          | none =>
              if hasEqMotive then
                decompileExpr innerBody newLctx telescopeInsts
              else
                LeanDecomp.decompileOrExact innerBody newLctx telescopeInsts decompileExpr
        return (bodyTactics, ctorParamNames)

      if allBranchesAreLia then
        allBranchesAreLia := branchTactics.size == 1 &&
          branchTactics[0]!.raw.getKind == liaKind

      let branchTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$branchTactics]*)

      -- Start with quasi-quote pattern that has no binders
      let baseAlt ← `(Lean.Parser.Tactic.inductionAlt| | $ctorIdent => $branchTacticSeq)
      -- Insert the binder names by surgically replacing the LHS's empty
      -- binder-list `null` node with a populated one.  This is the path
      -- `cases` uses to learn what names to introduce for the constructor's
      -- arguments — the quasi-quote can't express it directly because the
      -- `inductionAltLHS` grammar treats binder names as plain identifiers
      -- (not `term` antiquotations), so we have to reach into the parsed AST.
      let altStx := if ctorParamNames.isEmpty then baseAlt
                    else setInductionAltBinders baseAlt ctorParamNames.toArray
      alts := alts.push altStx

    -- When the discriminant is a complex term application (not a local fvar),
    -- emit `have hOr : <type> := by <disc_tactics>; cases hOr with ...` so the
    -- big term is built tactically and the `cases` sees only a simple name.
    -- This avoids the re-elaboration failures we get when a giant `Eq.mp`
    -- chain is embedded inline in a `cases` position.
    let mut preTacs : Array (TSyntax `tactic) := #[]
    let discTerm : Term ← if useHaveWrapper then do
        let discType ← instantiateMVars (← Meta.inferType info.discriminant)
        -- Set pp.numericTypes so generated have-types like
        -- `(-1 : ℤ) * ↑a + ↑b ≤ 0` are unambiguous when re-elaborated. Without
        -- this, mixed ℕ/ℤ expressions can fail because `-1` requires `Neg`.
        let discTypeStx ← withOptions (fun o =>
            (o.setBool `pp.coercions.types true).setBool `pp.numericTypes true) <|
          delabToRefinableSyntax discType
        let discSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$discTacticsEarly]*)
        let hOrName := LeanDecomp.mkUniqueName "hOr" (← getUsed)
        addUsed hOrName
        let hOrIdent : Ident := ⟨mkIdent (Name.mkSimple hOrName) |>.raw.setInfo .none⟩
        let haveTac ← `(tactic| have $hOrIdent:ident : $discTypeStx := by $discSeq)
        preTacs := #[haveTac]
        `($hOrIdent:ident)
      else
        withOptions (fun o =>
          (o.setBool `pp.coercions.types true).setBool `pp.numericTypes true) <|
        delabToRefinableSyntax info.discriminant
    let eqBinderName? : Option String := eqInfo.map fun (eqName, _) =>
      let discName := getDiscriminantName info.discriminant lctx
      if discName == some eqName then s!"{eqName}_eq" else eqName
    let casesTac ← mkCasesWithAltsTactic discTerm eqBinderName? alts

    -- Stage-3 collapse: if this is an `Or` cases-split where the discriminant
    -- needed a `have hOr := by ...` wrapper AND every branch reduced to a
    -- single `lia`, attempt bare `lia` on the original goal.  `lia` (cutsat)
    -- can do internal disjunction case splits, so the `have hOr; cases hOr`
    -- scaffolding is often redundant.  Validation is the safety net: keep the
    -- cases form whenever bare `lia` does not close the goal.
    if useHaveWrapper && allBranchesAreLia then
      let exprTy ← instantiateMVars (← Meta.inferType expr)
      if ← LeanDecomp.candidateTacticsCloseGoal #[liaRef] exprTy lctx localInsts then
        return some #[liaRef]

    return some (preTacs ++ #[casesTac])

end LeanDecomp
