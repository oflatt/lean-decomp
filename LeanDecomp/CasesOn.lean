import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter

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
  /-- The case branches (one per constructor) -/
  caseBranches : List Expr
  deriving Inhabited

/-- Try to extract casesOn information from an expression.
    Returns none if the expression is not a casesOn application. -/
def parseCasesOn (expr : Expr) : MetaM (Option CasesOnInfo) := do
  let (fn, args) := peelArgs expr
  -- Check if the head is a constant ending in `.casesOn`
  let some constName := Expr.constName? fn
    | return none
  let nameStr := constName.toString
  if !nameStr.endsWith ".casesOn" then
    return none
  -- Get information about the inductive type
  let some indName := constName.eraseSuffix? `casesOn
    | return none
  let some indInfo := (← getEnv).find? indName
    | return none
  let .inductInfo indVal := indInfo
    | return none
  -- casesOn arguments layout: [motive, params..., indices..., discriminant, cases...]
  let numParams := indVal.numParams
  let numIndices := indVal.numIndices
  let numCtors := indVal.ctors.length
  if args.length < 2 + numCtors then
    return none
  let discriminantIdx := 1 + numParams + numIndices
  let casesStartIdx := discriminantIdx + 1
  if args.length < casesStartIdx + numCtors then
    return none
  let discriminant := args[discriminantIdx]!
  let caseBranches := (List.range numCtors).map fun i => args[casesStartIdx + i]!
  return some {
    indName := indName
    indVal := indVal
    discriminant := discriminant
    caseBranches := caseBranches
  }

/-- Check if a constructor could possibly match the discriminant by comparing
    the constructor's result type indices with the discriminant's type indices.
    Returns false if the indices have incompatible head constructors. -/
def couldConstructorMatch (ctorName : Name) (discriminantType : Expr) : MetaM Bool := do
  -- Get constructor info
  let some ctorInfo := (← getEnv).find? ctorName
    | return true  -- If we can't find info, assume it could match
  let .ctorInfo _ := ctorInfo
    | return true
  -- Get the constructor's result type by applying it to fresh mvars
  let ctorType ← inferType (mkConst ctorName)
  -- The constructor type is a telescope ending in the inductive type applied to indices
  -- We need to instantiate all the arguments to get the result type
  forallTelescope ctorType fun _ resultType => do
    -- resultType should be like `BigStep stmt s t` for BigStep constructors
    -- discriminantType is also like `BigStep stmt' s' t'`
    let (_, ctorIndices) := resultType.getAppFnArgs
    let (_, discIndices) := discriminantType.getAppFnArgs
    -- Compare indices pairwise - if any have incompatible head constructors, return false
    for (ctorIdx, discIdx) in ctorIndices.zip discIndices do
      -- Get the head of each index (after reducing)
      let ctorIdxHead := ctorIdx.getAppFn
      let discIdxHead := discIdx.getAppFn
      -- If both are constructors of the same inductive but different constructors, impossible
      if let (.const ctorIdxName _, .const discIdxName _) := (ctorIdxHead, discIdxHead) then
        -- Check if they're both constructors
        if let (some (.ctorInfo ctorIdxInfo), some (.ctorInfo discIdxInfo)) :=
            ((← getEnv).find? ctorIdxName, (← getEnv).find? discIdxName) then
          -- Same inductive type but different constructors = impossible
          if ctorIdxInfo.induct == discIdxInfo.induct && ctorIdxName != discIdxName then
            return false
    return true

/-- Type alias for the decompileExpr callback to avoid repetition -/
abbrev DecompileCallback := Expr → LocalContext → LocalInstances → List String →
    MetaM (Array (TSyntax `tactic) × List String)

/-- Type alias for the assignIntroNames callback -/
abbrev AssignIntroNamesCallback := Array Expr → List String →
    MetaM (List String × LocalContext × List String)

/-- Convert intro names to identifier syntax -/
private def namesToIdents (names : List String) : Array Ident :=
  names.toArray.map (fun n => mkIdent (Name.mkSimple n))

/-- Handle `*.casesOn` applications - generate a `cases` tactic.
    Detects when expr is an application of an inductive type's casesOn eliminator.
    Takes callbacks for decompileExpr and assignIntroNames to avoid circular dependencies. -/
def tryDecompCasesOn (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String)
    (decompileExpr : DecompileCallback)
    (assignIntroNames : AssignIntroNamesCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let some info ← parseCasesOn expr
      | return none
    let ctorNames := info.indVal.ctors
    -- Get the discriminant's type to determine which constructors could match
    let discriminantType ← inferType info.discriminant
    -- Get the discriminant as syntax (should be an fvar in most cases)
    let discriminantStx ← delabToRefinableSyntax info.discriminant
    -- Build the cases tactic with named alternatives
    let mut alts : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
    let mut used := used
    for (ctorName, caseBranch) in ctorNames.zip info.caseBranches do
      -- Check if this constructor could possibly match the discriminant
      let couldMatch ← couldConstructorMatch ctorName discriminantType
      if !couldMatch then
        continue
      -- Extract just the constructor name (last component)
      let ctorShortName := ctorName.getString!
      let ctorIdent := mkIdent (Name.mkSimple ctorShortName)
      -- Each case branch is a lambda - use lambdaTelescope to enter it
      -- and recursively decompile the body
      let (branchTactics, used') ← Meta.lambdaTelescope caseBranch fun xs body => do
        if xs.size > 0 then
          let _telescopeLctx ← getLCtx
          let telescopeInsts ← getLocalInstances
          -- Assign names to the introduced variables
          let (introNames, newLctx, used') ← assignIntroNames xs used
          -- Recursively decompile the body
          let (bodyTactics, used'') ← decompileExpr body newLctx telescopeInsts used'
          -- Build intro tactic for the case arguments
          let introTac ← if introNames.isEmpty then
              pure #[]
            else
              let idents := namesToIdents introNames
              let tac ← `(tactic| intro $[$idents]*)
              pure #[tac]
          return (introTac ++ bodyTactics, used'')
        else
          decompileExpr body lctx localInsts used
      used := used'
      -- Build the case alternative
      let branchTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$branchTactics]*)
      let altStx ← `(Lean.Parser.Tactic.inductionAlt| | $ctorIdent => $branchTacticSeq)
      alts := alts.push altStx
    let casesTac ← `(tactic| cases $discriminantStx:term with $[$alts:inductionAlt]*)
    return some (#[casesTac], used)

end LeanDecomp
