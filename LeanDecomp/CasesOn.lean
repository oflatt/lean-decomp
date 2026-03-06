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
        if binders.size < 1 then return none
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

/-- Try to strip `Eq.ndrec` / `Eq.rec` wrappers from a branch body.
    The casesOn generalized equation pattern produces:
      `@Eq.ndrec α ctor motive (fun (h : disc = ctor) => actual_body) disc (Eq.symm h_eq) (Eq.refl disc)`
    We want to extract `actual_body` from inside the inner lambda.
    The equality proof lambda parameter is not needed because `cases h:` already
    introduces the equality hypothesis. -/
private partial def stripEqRec (body : Expr) (eqProofFvar : Option Expr) : MetaM Expr := do
  let (fn, args) := peelArgs body
  if let some constName := fn.constName? then
    if (constName == ``Eq.ndrec || constName == ``Eq.rec) && args.length >= 4 then
      let innerTerm := args[3]!
      -- The body (args[3]) may be a lambda `fun h => actual_body`
      -- which takes the eq proof. We need to enter this lambda and extract the body.
      if innerTerm.isLambda then
        Meta.lambdaTelescope innerTerm fun _xs lambdaBody => do
          -- Recursively strip more Eq.ndrec wrappers
          stripEqRec lambdaBody eqProofFvar
      else
        stripEqRec innerTerm eqProofFvar
    else if constName == ``Eq.mpr && args.length >= 4 then
      stripEqRec args[3]! eqProofFvar
    else
      return body
  else
    return body

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
    if constName == ``False.casesOn || constName == ``False.elim then
      return true
  return false

/-- Handle `*.casesOn` applications - generate a `cases` tactic.
    Detects when expr is an application of an inductive type's casesOn eliminator.
    Takes callbacks for decompileExpr and assignIntroNames to avoid circular dependencies.
    
    NOTE: Works well for simple cases (constructors with no parameters).
    For indexed inductive types with constructor parameters, the generated tactics
    may fail because the proof term contains fvar references from the lambda telescope
    that don't match the fvars created by the `cases` tactic at runtime. Future work
    could address this by using explicit binders in case alternatives or generating
    intro tactics to rebind the parameters. -/
def tryDecompCasesOn (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String)
    (decompileExpr : DecompileCallback)
    (assignIntroNames : AssignIntroNamesCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let some info ← parseCasesOn expr
      | return none
    let ctorNames := info.indVal.ctors

    -- Check if the motive has equality parameters (generalized equation pattern)
    -- If so, get the name of the first equality binder and the count
    let eqInfo ← motiveEqInfo info.motive
    let hasEqMotive := eqInfo.isSome

    let mut alts : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
    let mut used := used
    let mut ctorIdx := 0

    for (ctorName, caseBranch) in ctorNames.zip info.caseBranches do
      let ctorShortName := ctorName.getString!
      let ctorIdent := mkIdent (Name.mkSimple ctorShortName)

      -- Check if this branch is a contradiction (impossible constructor).
      -- We enter the lambda telescope and check the body.
      let isContradiction ← Meta.lambdaTelescope caseBranch fun _xs body => do
        isBranchContradiction body

      if isContradiction then
        ctorIdx := ctorIdx + 1
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
        let mut ctorParams : Array Expr := #[]
        for i in List.range ctorParamCount do
          ctorParams := ctorParams.push xs[i]!

        -- Assign names for constructor params and track them
        let (ctorParamNames, newLctx, usedAfterCtorParams) ←
          if ctorParams.size > 0 then
            assignIntroNames ctorParams used
          else
            pure ([], telescopeLctx, used)

        dbg_trace s!"[casesOn] branch {ctorShortName}: ctorParams={ctorParamCount}, trailingEq={numTrailingEq}, names={ctorParamNames}"

        -- Strip the Eq.ndrec/Eq.rec wrapper if present (the `cases` tactic
        -- handles the substitution automatically, so we extract the inner body)
        let innerBody ← if hasEqMotive then stripEqRec body none else pure body

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
        -- Navigate into the AST and insert binder identifiers after the constructor ident
        -- Structure: inductionAlt[null[inductionAltLHS[pipe, group[...]]],null[arrow, tacSeq]]
        match baseAlt.raw with
        | .node info kind #[lhsWrapper, rhsWrapper] =>
            match lhsWrapper with
            | .node lhsInfo `null #[altLHS] =>
                match altLHS with
                | .node altLHSInfo `Lean.Parser.Tactic.inductionAltLHS children =>
                    if children.size >= 2 then
                      let group := children[1]!
                      match group with
                      | .node groupInfo `group groupChildren =>
                          -- Insert binders after existing children
                          -- Original: [null[], ident]  → Target: [null[], ident, param1, param2, ...]
                          if groupChildren.size >= 2 then 
                            let binderIdents := ctorParamNames.toArray.map fun name =>
                              (mkIdent (Name.mkSimple name)).raw
                            dbg_trace s!"[DEBUG] {ctorShortName}: Adding {binderIdents.size} binders: {ctorParamNames}"
                            let newGroupChildren := groupChildren ++ binderIdents
                            dbg_trace s!"[DEBUG] Group before: {groupChildren.size} children, after: {newGroupChildren.size} children"
                            let newGroup := Syntax.node groupInfo `group newGroupChildren
                            let newAltLHS := Syntax.node altLHSInfo `Lean.Parser.Tactic.inductionAltLHS (children.set! 1 newGroup)
                            let newLHSWrapper := Syntax.node lhsInfo `null #[newAltLHS]
                            let newAlt := Syntax.node info kind #[newLHSWrapper, rhsWrapper]
                            ⟨newAlt⟩
                          else
                            baseAlt
                      | _ => baseAlt
                    else
                      baseAlt
                | _ => baseAlt
            | _ => baseAlt
        | _ => baseAlt
      
      alts := alts.push altStx
      ctorIdx := ctorIdx + 1

    let discriminantStx ← delabToRefinableSyntax info.discriminant
    let casesTac ← if let some (eqName, _) := eqInfo then do
      let hIdent : TSyntax `Lean.binderIdent ←
        `(Lean.binderIdent| $(mkIdent (Name.mkSimple eqName)):ident)
      `(tactic| cases $hIdent : $discriminantStx:term with $[$alts:inductionAlt]*)
    else
      `(tactic| cases $discriminantStx:term with $[$alts:inductionAlt]*)

    return some (#[casesTac], used)

end LeanDecomp
