import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import Lean.Elab.Tactic.Omega.Frontend
import LeanDecomp.Helpers
import LeanDecomp.CasesOn
import LeanDecomp.EqDecomp
import LeanDecomp.Simplify

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
          -- Pure beta reduction for lambda-headed applications.
          -- lambdaTelescope's whnfD also does delta reduction (unfolding casesOn to rec),
          -- so we reduce only beta-redexes here to preserve structure.
          let mut body := body
          while body.isApp && body.getAppFn.isLambda do
            body := body.headBeta
          let specialized? ← firstSomeM [
            tryDecompByContradiction body lctx localInsts used,
            tryDecompCasesOn body lctx localInsts used decompileExpr assignIntroNames,
            tryDecompEqMpGrindCast body lctx localInsts used,
            tryDecompOmega body lctx localInsts used,
            LeanDecomp.tryDecompCongr body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompCongrArg body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqSymm body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqTrans body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqMp body lctx localInsts used decompileExpr,
            tryDecompFalseRec body lctx localInsts used,
            tryDecompFalseType body lctx localInsts used,
            tryDecompBetaRedex body lctx localInsts used,
            tryDecompDecide body lctx localInsts used
          ]
          match specialized? with
          | some res => pure res
          | none => decompExact body used

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

  /-- Handle beta redex: `(fun x => body) arg`.
      For fvar arguments, emit a let binding for readability.
      For non-fvar arguments, beta-reduce and recurse. -/
  private partial def tryDecompBetaRedex (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let .app fn arg := expr | return none
      let .lam binderName binderType body _binderInfo := fn | return none
      if let some argFvarId := arg.fvarId? then
        let argDecl ← argFvarId.getDecl
        let argName := argDecl.userName
        let letBinderName := binderBaseName used.length binderName
        let letBinderId := FVarId.mk (← mkFreshId)
        let newLctx := lctx.mkLetDecl letBinderId (Name.mkSimple letBinderName) binderType arg
        let newLocalInsts ← getLocalInstances
        let used' := letBinderName :: used
        let newBody := body.instantiate1 (Expr.fvar letBinderId)
        let (bodyTactics, used'') ← decompileExpr newBody newLctx newLocalInsts used'
        let letBinderIdent := mkIdent (Name.mkSimple letBinderName)
        let argIdent := mkIdent argName
        let letTac ← `(tactic| let $letBinderIdent := $argIdent)
        return some (#[letTac] ++ bodyTactics, used'')
      else
        let reduced := body.instantiate1 arg
        let (tactics, used') ← decompileExpr reduced lctx localInsts used
        return some (tactics, used')

  /-- Handle `False.rec`, `False.elim`, and `False.casesOn` terms. -/
  private partial def tryDecompFalseRec (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, args) := peelArgs expr
      let some constName := Expr.constName? fn
        | return none
      if constName != ``False.rec && constName != ``False.elim && constName != ``False.casesOn then
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

      -- Try to simplify: detect `Eq.mp (eq_true h ... eq_false h') True.intro`
      -- and replace with `exact absurd h h'`. This works at tactic level because
      -- casesOn branches unify the types that differ at the Expr level.
      if let some (h, h') := extractContradiction falseArg then
        let hStx ← delabToRefinableSyntax h
        let h'Stx ← delabToRefinableSyntax h'
        let absurdId := mkIdent ``absurd
        let tac ← `(tactic| exact $absurdId $hStx $h'Stx)
        return some (#[tac], used)

      -- Best case: contradiction hypothesis is already a local variable.
      if let some falseFVarId := falseArg.fvarId? then
        let decl ← falseFVarId.getDecl
        let hFalseTarget : TSyntax `Lean.Parser.Tactic.elimTarget ←
          `(Lean.Parser.Tactic.elimTarget| $(mkIdent decl.userName):ident)
        let casesTac ← `(tactic| cases $hFalseTarget)
        return some (#[casesTac], used)

      -- For complex proofs of False (e.g., noConfusion-derived Eq.ndrec),
      -- use `contradiction` which handles noConfusion automatically.
      let contradictionTac ← `(tactic| contradiction)
      return some (#[contradictionTac], used)

  /-- Handle `of_decide_eq_true` — emit `decide`.
      `decide` elaborates to `of_decide_eq_true <proof>`, so we recognize
      this pattern and replace the entire term with the `decide` tactic. -/
  private partial def tryDecompDecide (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, _) := peelArgs expr
      let some constName := fn.constName? | return none
      if constName != ``of_decide_eq_true then return none
      let tac ← `(tactic| decide)
      return some (#[tac], used)

  /-- Strip `Eq.mp <cast> inner` when the cast contains grind internals.
      Grind wraps proof terms in type-normalization casts that are logically
      transparent — the inner term proves something defEq to the goal.
      We skip the cast and recurse on the inner proof. -/
  private partial def tryDecompEqMpGrindCast (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    let (fn, args) := peelArgs expr
    let some cname := fn.constName? | return none
    if cname != ``Eq.mp then return none
    if args.length < 4 then return none
    let eqProof := args[2]!
    let inner := args[3]!
    -- Only strip when the cast itself is grind normalization junk
    if !containsGrindInternals eqProof then return none
    -- When inner is True.intro, the meaningful content is in the equality chain,
    -- not the inner term. Let tryDecompEqMp handle these structurally.
    let (innerFn, _) := peelArgs inner
    if innerFn.isConstOf ``True.intro then return none
    -- Reconstruct the inner expression with any extra args (over-application)
    let innerWithArgs := (args.drop 4).foldl (init := inner) fun acc arg => mkApp acc arg
    withLCtx lctx localInsts do
      let goalType ← Meta.inferType expr
      let innerType ← Meta.inferType innerWithArgs
      -- If types match, just recurse on inner
      if ← Meta.isDefEq goalType innerType then
        let (tactics, used') ← decompileExpr innerWithArgs lctx localInsts used
        return some (tactics, used')
      -- Types differ (grind normalization). Introduce inner as `have`, close with `omega`.
      let (haveName, used') := chooseIntroName used.length `fact used
      let haveNameIdent := mkIdent (Name.mkSimple haveName)
      let typeStx ← PrettyPrinter.delab innerType
      let (proofTactics, used'') ← decompileExpr innerWithArgs lctx localInsts used'
      let proofTacSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$proofTactics]*)
      let haveTac ← `(tactic| have $haveNameIdent : $typeStx := by $proofTacSeq)
      let closingTac ← `(tactic| omega)
      return some (#[haveTac, closingTac], used'')

  /-- Try replacing grind-internal proof terms with `omega`.
      When the expression contains grind/linear-arithmetic internals, try `omega`
      (verified via API). This avoids decomposing huge internal terms that
      `omega` can handle directly. -/
  private partial def tryDecompOmega (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    -- Only try if the expression contains grind internals
    if !containsGrindInternals expr then return none
    withLCtx lctx localInsts do
      let goalType ← Meta.inferType expr
      -- Collect all hypothesis expressions from the local context
      let mut facts : List Expr := []
      for decl in lctx do
        if decl.isImplementationDetail then continue
        facts := (.fvar decl.fvarId) :: facts
      -- Try omega
      try
        let mvar ← Meta.mkFreshExprMVar (some goalType) .syntheticOpaque
        Lean.Elab.Tactic.Omega.omega facts mvar.mvarId!
        let tac ← `(tactic| omega)
        return some (#[tac], used)
      catch _ => pure ()
      -- Omega failed — fall through to other handlers to keep unwrapping
      return none

  /-- The final exact fallback. Try without pp.all first for smaller output,
      fall back to pp.all if needed. -/
  private partial def decompExact (body : Expr) (used : List String) :
      MetaM (Array (TSyntax `tactic) × List String) := do
    let termStx ← delabToRefinableSyntax body
    let tac ← `(tactic| exact $termStx)
    return (#[tac], used)

  /-- Handle any expression whose type is `False` — emit `contradiction`.
      Only fires when the local context contains an obvious contradiction
      (a `False` hypothesis, or `h : P` and `h' : ¬P`). This avoids emitting
      `contradiction` for complex proof terms where it can't close the goal. -/
  private partial def tryDecompFalseType (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let exprTy ← Meta.inferType expr
      if !exprTy.isConstOf ``False then return none
      -- Check if the local context has an obvious contradiction
      let mut hasFalse := false
      let mut posHyps : Array Expr := #[]  -- hypotheses of type P
      let mut negHyps : Array Expr := #[]  -- hypotheses of type ¬P (inner P)
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty := decl.type
        if ty.isConstOf ``False then
          hasFalse := true
          break
        let (fn, args) := peelArgs ty
        if fn.isConstOf ``Not && args.length >= 1 then
          negHyps := negHyps.push args[0]!
        else if ty.isForall && !ty.isArrow then
          -- skip universals
          pure ()
        else if let .forallE _ dom body _ := ty then
          -- P → False is ¬P
          if body.isConstOf ``False then
            negHyps := negHyps.push dom
          else
            posHyps := posHyps.push ty
        else if !ty.isSort then
          posHyps := posHyps.push ty
      if hasFalse then
        let contradictionTac ← `(tactic| contradiction)
        return some (#[contradictionTac], used)
      -- Check for P/¬P pair
      for neg in negHyps do
        for pos in posHyps do
          if (← Meta.isDefEq pos neg) then
            let contradictionTac ← `(tactic| contradiction)
            return some (#[contradictionTac], used)
      return none

end

end LeanDecomp
