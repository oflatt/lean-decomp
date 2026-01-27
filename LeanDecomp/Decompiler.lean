import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.CasesOn

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

private def binderBaseName (idx : Nat) (name : Name) : String :=
  let raw := name.eraseMacroScopes.toString
  let lastSegment := (raw.splitOn ".").reverse.headD raw
  let cleaned := lastSegment.replace "'" ""
  if cleaned = "" || cleaned = "_" then s!"x{idx + 1}" else cleaned

private def mkUniqueName (base : String) (used : List String) : String :=
  if !(used.contains base) then base
  else
    let rec loop (suffix remaining : Nat) : String :=
      let candidate := s!"{base}_{suffix}"
      match remaining with
      | 0 => candidate
      | Nat.succ remaining' =>
          if used.contains candidate then
            loop (suffix + 1) remaining'
          else
            candidate
    loop 1 (used.length + 1)

private def chooseIntroName (idx : Nat) (userName : Name) (used : List String) : (String × List String) :=
  let base := binderBaseName idx userName
  let introName := mkUniqueName base used
  (introName, introName :: used)

private def assignIntroNames (xs : Array Expr) (used0 : List String) : MetaM (List String × LocalContext × List String) := do
  let mut used : List String := used0
  let mut idx := 0
  let mut names : List String := []
  let mut lctx ← getLCtx
  for x in xs do
    let some fvarId := x.fvarId?
      | throwError "Unexpected non-fvar binder in proof term"
    let decl ← fvarId.getDecl
    let (introName, used') := chooseIntroName idx decl.userName used
    used := used'
    names := introName :: names
    let newName := Name.mkSimple introName
    lctx := lctx.setUserName fvarId newName
    idx := idx + 1
  return (names.reverse, lctx, used)

/-- Convert intro names to identifier syntax -/
private def namesToIdents (names : List String) : Array Ident :=
  names.toArray.map (fun n => mkIdent (Name.mkSimple n))

/-- Build a tacticSeq from an array of tactics -/
private def mkTacticSeq (tacs : Array (TSyntax `tactic)) : CoreM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  `(Lean.Parser.Tactic.tacticSeq| $[$tacs]*)

/-- Flatten nested arrays of tactics -/
private def flattenTactics (tacss : List (Array (TSyntax `tactic))) : Array (TSyntax `tactic) :=
  tacss.foldl (· ++ ·) #[]

/-- Try a list of computations in order, returning the first `some` result. -/
private def firstSomeM [Monad m] (xs : List (m (Option α))) : m (Option α) := do
  for x in xs do
    if let some res ← x then
      return some res
  return none

mutual

  /-- Convert a proof term expression into tactic syntax. -/
  partial def decompileExpr (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Array (TSyntax `tactic) × List String) := do
    withLCtx lctx localInsts do
      Meta.lambdaTelescope expr fun xs body => do
        if xs.size > 0 then
          -- Use the current local context from inside lambdaTelescope
          let telescopeLctx ← getLCtx
          let telescopeInsts ← getLocalInstances
          tryDecompIntro xs body telescopeLctx telescopeInsts used
        else
          let specialized? ← firstSomeM [
            tryDecompByContradiction expr lctx localInsts used,
            tryDecompCasesOn expr lctx localInsts used,
            tryDecompBetaRedex expr lctx localInsts used,
            tryDecompId expr lctx localInsts used
          ]
          match specialized? with
          | some res => pure res
          | none => do
              let termStx ← delabToRefinableSyntax expr
              let tac ← `(tactic| exact $termStx)
              return (#[tac], used)

  private partial def tryDecompIntro (xs : Array Expr) (body : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Array (TSyntax `tactic) × List String) := do
    withLCtx lctx localInsts do
      let (introNames, newLctx, used') ← assignIntroNames xs used
      let newLocalInsts ← getLocalInstances
      let (bodyTactics, used'') ← decompileExpr body newLctx newLocalInsts used'
      let introTac ← if introNames.isEmpty then
          pure #[]
        else
          let idents := namesToIdents introNames
          let tac ← `(tactic| intro $[$idents]*)
          pure #[tac]
      return (introTac ++ bodyTactics, used'')

  private partial def tryDecompByContradiction (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, args) := peelArgs expr
      let some constName := Expr.constName? fn
        | return none
      if constName != ``Classical.byContradiction then
        return none
      let some handler := args.getLast?
        | return none
      let handlerType ← Meta.inferType handler
      Meta.forallTelescope handlerType fun binders _ => do
        if binders.size = 1 then
          let binder := binders[0]!
          let lctxWithBinder ← getLCtx
          let some fvarId := binder.fvarId?
            | throwError "Unexpected non-fvar binder in byContradiction handler"
          let decl ← fvarId.getDecl
          let (binderName, used') := chooseIntroName used.length decl.userName used
          let renamedBinderLctx := lctxWithBinder.setUserName fvarId (Name.mkSimple binderName)
          let binderLocalInsts ← getLocalInstances
          let applied := Expr.app handler binder
          let (bodyTactics, used'') ← decompileExpr applied renamedBinderLctx binderLocalInsts used'
          let binderIdent := mkIdent (Name.mkSimple binderName)
          -- Use mkIdent with no info to avoid hygiene marks (✝) in pretty-printed output
          let byContradictionIdent : Ident := ⟨mkIdent ``Classical.byContradiction |>.raw.setInfo .none⟩
          let applyTac ← `(tactic| apply $byContradictionIdent:ident)
          let introTac ← `(tactic| intro $binderIdent:ident)
          return some (#[applyTac, introTac] ++ bodyTactics, used'')
        else
          return none

  /-- Handle `*.casesOn` applications - generate a `cases` tactic.
      Detects when expr is an application of an inductive type's casesOn eliminator. -/
  private partial def tryDecompCasesOn (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let some info ← parseCasesOn expr
        | return none
      let ctorNames := info.indVal.ctors
      -- Get the discriminant as syntax (should be an fvar in most cases)
      let discriminantStx ← delabToRefinableSyntax info.discriminant
      -- Build the cases tactic with named alternatives
      let mut alts : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
      let mut used := used
      for (ctorName, caseBranch) in ctorNames.zip info.caseBranches do
        -- Extract just the constructor name (last component)
        let ctorShortName := ctorName.getString!
        let ctorIdent := mkIdent (Name.mkSimple ctorShortName)
        -- Each case branch is a lambda - use lambdaTelescope to enter it
        -- and recursively decompile the body
        let (branchTactics, used') ← Meta.lambdaTelescope caseBranch fun xs body => do
          if xs.size > 0 then
            let telescopeLctx ← getLCtx
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

  /-- Handle beta redex: `(fun x => body) arg` where arg is an fvar.
      Transform to `let x := arg; body` to avoid immediate application in output. -/
  private partial def tryDecompBetaRedex (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      -- Check if expr is `(fun x => body) arg` where arg is an fvar
      let .app fn arg := expr | return none
      let .lam binderName binderType body _binderInfo := fn | return none
      let some argFvarId := arg.fvarId? | return none
      -- Get the name of the argument variable
      let argDecl ← argFvarId.getDecl
      let argName := argDecl.userName
      -- Use the lambda's binder name for the let binding (it will shadow)
      let letBinderName := binderBaseName used.length binderName
      let letBinderId := FVarId.mk (← mkFreshId)
      -- Add the let declaration to the local context
      let newLctx := lctx.mkLetDecl letBinderId (Name.mkSimple letBinderName) binderType arg
      let newLocalInsts ← getLocalInstances
      -- Mark the let binder name as used for future naming
      let used' := letBinderName :: used
      -- Substitute the new fvar for the bound variable in body
      let newBody := body.instantiate1 (Expr.fvar letBinderId)
      -- Recursively render the body
      let (bodyTactics, used'') ← decompileExpr newBody newLctx newLocalInsts used'
      -- Build the let tactic: `let letBinderName := argName`
      let letBinderIdent := mkIdent (Name.mkSimple letBinderName)
      let argIdent := mkIdent argName
      let letTac ← `(tactic| let $letBinderIdent := $argIdent)
      return some (#[letTac] ++ bodyTactics, used'')

  /-- Handle `@id T body` - extract the body into a let binding with type annotation.
      Transform `@id T body` into `let prf : T := by <decompiled body>; exact prf` -/
  private partial def tryDecompId (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      -- Check if expr is `@id T body`
      let .app fn body := expr | return none
      let .app idConst typeArg := fn | return none
      let some constName := idConst.constName? | return none
      if constName != ``id then return none
      -- Decompile the body
      let (bodyTactics, used') ← decompileExpr body lctx localInsts used
      -- Create a fresh name for the proof
      let (prfName, used'') := chooseIntroName used'.length `prf used'
      let prfIdent := mkIdent (Name.mkSimple prfName)
      -- Delaborate the type
      let typeStx ← delabToRefinableSyntax typeArg
      -- Build: let prf : T := by <bodyTactics>
      let bodyTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$bodyTactics]*)
      let letTac ← `(tactic| let $prfIdent : $typeStx := by $bodyTacticSeq)
      -- Build: exact prf
      let exactTac ← `(tactic| exact $prfIdent)
      return some (#[letTac, exactTac], used'')

end

end LeanDecomp
