import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.Helpers
import LeanDecomp.CasesOn
import LeanDecomp.EqDecomp

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

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
            tryDecompCasesOn expr lctx localInsts used decompileExpr assignIntroNames,
            tryDecompNoConfusion expr lctx localInsts used,
            LeanDecomp.tryDecompCongr expr lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompCongrArg expr lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqSymm expr lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqTrans expr lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqMp expr lctx localInsts used decompileExpr,
            tryDecompIntroWithEq expr lctx localInsts used,
            tryDecompFalseRec expr lctx localInsts used,
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

  /-- Handle `*.noConfusion` applications by reducing them first.
      This turns constructor-equality eliminators into simpler branch terms,
      which usually decompile much better. -/
  private partial def tryDecompNoConfusion (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, _) := peelArgs expr
      let some constName := Expr.constName? fn
        | return none
      if !constName.toString.endsWith ".noConfusion" then
        return none

      -- Try weak-head reduction first; this is enough for typical
      -- `noConfusion (Eq.refl ...) ...` terms.
      let reduced ← Meta.whnf expr
      if reduced != expr then
        let (tactics, used') ← decompileExpr reduced lctx localInsts used
        return some (tactics, used')

      return none

  /-- Handle `Lean.Grind.intro_with_eq` and `Lean.Grind.intro_with_eq'` by
      unfolding and reducing them, then recursively decompiling the result.
      `intro_with_eq p p' q he k hp` reduces to `k (Eq.mp he hp)`.
      We perform this reduction manually to avoid `whnf` over-reducing
      inner terms like `Or.casesOn` into `Or.rec`. -/
  private partial def tryDecompIntroWithEq (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, args) := peelArgs expr
      let some constName := Expr.constName? fn
        | return none
      if constName != ``Lean.Grind.intro_with_eq && constName != ``Lean.Grind.intro_with_eq' then
        return none
      -- args layout: [p, p', q, he, k] (partial) or [p, p', q, he, k, hp] (full)
      if args.length == 6 then
        -- Fully applied: intro_with_eq p p' q he k hp ↝ k (Eq.mp he hp)
        let p := args[0]!
        let p' := args[1]!
        let he := args[3]!
        let k := args[4]!
        let hp := args[5]!
        let eqMpApp := mkApp4 (mkConst ``Eq.mp [Level.zero]) p p' he hp
        let result := Expr.app k eqMpApp
        -- Beta-reduce if k is a lambda
        let result := result.headBeta
        let (tactics, used') ← decompileExpr result lctx localInsts used
        return some (tactics, used')
      else if args.length == 5 then
        -- Partially applied: returns p → q, construct lambda manually
        let p := args[0]!
        let p' := args[1]!
        let he := args[3]!
        let k := args[4]!
        let body := Expr.lam `hp p
          (Expr.app (k.liftLooseBVars 0 1)
            (mkApp4 (mkConst ``Eq.mp [Level.zero])
              (p.liftLooseBVars 0 1) (p'.liftLooseBVars 0 1)
              (he.liftLooseBVars 0 1) (.bvar 0)))
          .default
        let (tactics, used') ← decompileExpr body lctx localInsts used
        return some (tactics, used')
      return none

  /-- Handle `False.rec` terms.
      For this decompiler path we only need the primitive recursor used in the
      current example. -/
  private partial def tryDecompFalseRec (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, args) := peelArgs expr
      let some constName := Expr.constName? fn
        | return none
      if constName != ``False.rec then
        return none

      let falseTy := mkConst ``False
      let rec findFalseArg (xs : List Expr) : MetaM (Option Expr) := do
        match xs with
        | [] => return none
        | x :: xs' =>
            let xTy ← Meta.inferType x
            if (← Meta.isDefEq xTy falseTy) then
              return some x
            else
              findFalseArg xs'

      let some falseArg ← findFalseArg args
        | return none

      -- Best case: contradiction hypothesis is already a local variable.
      if let some falseFVarId := falseArg.fvarId? then
        let decl ← falseFVarId.getDecl
        let hFalseTarget : TSyntax `Lean.Parser.Tactic.elimTarget ←
          `(Lean.Parser.Tactic.elimTarget| $(mkIdent decl.userName):ident)
        let casesTac ← `(tactic| cases $hFalseTarget)
        return some (#[casesTac], used)

      -- Otherwise, name the contradiction proof and eliminate it.
      let (prfFalseName, used') := chooseIntroName used.length `hFalse used
      let prfFalseIdent := mkIdent (Name.mkSimple prfFalseName)
      let (falseTactics, used'') ← decompileExpr falseArg lctx localInsts used'
      let falseTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$falseTactics]*)
      let letTac ← `(tactic| let $prfFalseIdent : $(mkIdent ``False) := by $falseTacticSeq)
      let exactTac ← `(tactic| exact $(mkIdent ``False.elim) $prfFalseIdent)
      return some (#[letTac, exactTac], used'')

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
