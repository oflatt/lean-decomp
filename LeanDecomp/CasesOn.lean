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
  /-- Arguments passed after the case branches (motive arguments) -/
  motiveArgs : List Expr
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
  -- Extract motive arguments (everything after the case branches)
  let motiveArgsStartIdx := casesStartIdx + numCtors
  let motiveArgs := args.drop motiveArgsStartIdx
  return some {
    indName := indName
    indVal := indVal
    discriminant := discriminant
    caseBranches := caseBranches
    motiveArgs := motiveArgs
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

/-- Extract the value from an Eq.refl or HEq.refl term.
    For `@Eq.refl T val`, returns `val`.
    For `@HEq.refl T val`, returns `val`. -/
private def extractReflValue (e : Expr) : Option Expr := do
  let (fn, args) := peelArgs e
  let some constName := Expr.constName? fn | none
  if constName == ``Eq.refl || constName == ``HEq.refl then
    -- Eq.refl has args: [type, value]
    -- HEq.refl has args: [type, value]
    args.getLast?
  else
    none

/-- Try to extract constructor arguments from an expression.
    For example, from `ifThenElse B S T`, extract `[B, S, T]`. -/
private def extractConstructorArgs (e : Expr) : List Expr :=
  let (_, args) := peelArgs e
  args

/-- Find the value for an implicit parameter by matching it against index values.
    Given an implicit param and the index expressions from the motive, try to find
    the corresponding value by unification or pattern matching.
    Uses a greedy left-to-right matching to avoid reusing the same value. -/
private def findImplicitParamValue (param : Expr) (indexValues : List Expr) (usedIndices : List Nat) : MetaM (Option (Expr × Nat)) := do
  let paramType ← inferType param

  -- Try to find a matching index value by type (skip already used indices)
  for indexIdx in List.range indexValues.length do
    if usedIndices.contains indexIdx then
      continue

    let indexValue := indexValues[indexIdx]!
    let indexType ← inferType indexValue
    -- If the types match exactly, use this value
    if ← isDefEq paramType indexType then
      return some (indexValue, indexIdx)

    -- If the index is a constructor application, check if any of its args match
    let ctorArgs := extractConstructorArgs indexValue
    for arg in ctorArgs do
      let argType ← inferType arg
      if ← isDefEq paramType argType then
        return some (arg, indexIdx)

  return none/-- Handle `*.casesOn` applications - generate a `cases` tactic.
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
    -- Get the discriminant as syntax (should be an fvar in most cases)
    let discriminantStx ← delabToRefinableSyntax info.discriminant
    -- Build the cases tactic with named alternatives
    let mut alts : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
    let mut used := used


    -- TODO find actual name
    let discriminantNameOpt : Option String := some "h"
    let some discriminantName := discriminantNameOpt | return none

    for (ctorName, caseBranch) in ctorNames.zip info.caseBranches do
      -- Extract just the constructor name (last component)
      let ctorShortName := ctorName.getString!
      let ctorIdent := mkIdent (Name.mkSimple ctorShortName)

      -- Each case branch is a lambda - use lambdaTelescope to enter it
      -- and recursively decompile the body
      let (branchTactics, used') ← Meta.lambdaTelescope caseBranch fun xs body => do
        if xs.size > 0 then
          let telescopeInsts ← getLocalInstances

          -- Count implicit and explicit parameters
          let mut implicitParams : Array Expr := #[]
          let mut explicitParams : Array Expr := #[]

          for x in xs do
            let some fvarId := x.fvarId?
              | throwError "Unexpected non-fvar in case branch parameter"
            let decl ← fvarId.getDecl
            match decl.binderInfo with
            | .implicit | .instImplicit | .strictImplicit =>
                implicitParams := implicitParams.push x
            | .default =>
                explicitParams := explicitParams.push x

          -- First assign names for implicit params to track used names
          let (implicitNames, lctxAfterImplicit, usedAfterImplicit) ←
            if implicitParams.size > 0 then
              assignIntroNames implicitParams used
            else
              pure ([], ← getLCtx, used)

          -- Generate let bindings for implicit parameters
          -- Extract index values from motive arguments and match them to params
          let indexValues ← info.motiveArgs.mapM fun arg => do
            if let some val := extractReflValue arg then
              return val
            else
              return arg  -- Fallback to the arg itself

          let mut usedIndices : List Nat := []
          let mut letTactics : List (TSyntax `tactic) := []

          for idx in List.range implicitParams.size do
            let param := implicitParams[idx]!
            let name := implicitNames[idx]!
            let ident := mkIdent (Name.mkSimple name)

            -- Try to find the value for this parameter by matching types
            if let some (value, usedIdx) ← findImplicitParamValue param indexValues usedIndices then
              usedIndices := usedIdx :: usedIndices
              let valueStx ← delabToRefinableSyntax value
              letTactics := letTactics ++ [← `(tactic| let $ident := $valueStx)]
            else
              -- Fallback: use wildcard with type annotation
              let typeStx ← delabToRefinableSyntax (← inferType param)
              letTactics := letTactics ++ [← `(tactic| let $ident : $typeStx := _)]

          -- The explicit parameters are already introduced by the `cases` tactic,
          -- so we don't need to intro them again. We just need to track their names as used.
          let (_, newLctx, usedFinal) ←
            if explicitParams.size > 0 then
              withLCtx lctxAfterImplicit telescopeInsts do
                assignIntroNames explicitParams usedAfterImplicit
            else
              pure ([], lctxAfterImplicit, usedAfterImplicit)

          -- Recursively decompile the body (no intro needed for explicit params)
          let (bodyTactics, usedResult) ← decompileExpr body newLctx telescopeInsts usedFinal

          return (Array.mk letTactics ++ bodyTactics, usedResult)
        else
          decompileExpr body lctx localInsts used
      used := used'
      -- Build the case alternative
      let branchTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$branchTactics]*)
      let altStx ← `(Lean.Parser.Tactic.inductionAlt| | $ctorIdent => $branchTacticSeq)
      alts := alts.push altStx
    let hIdent : TSyntax `Lean.binderIdent ← `(Lean.binderIdent| $(mkIdent (Name.mkSimple discriminantName)):ident)
    let casesTac ← `(tactic| cases $hIdent : $discriminantStx:term with $[$alts:inductionAlt]*)
    return some (#[casesTac], used)

end LeanDecomp
