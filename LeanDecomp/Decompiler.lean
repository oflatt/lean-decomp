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

/-- Try to unify a fresh instance of an Iff lemma against a hypothesis type.
    Uses `forallMetaTelescope` so matching is robust to grind normalization.
    Returns `(appliedLemma, lhs, rhs)` on success. -/
private def tryMatchIff (name : Name) (hypTy : Expr) (forward : Bool)
    : MetaM (Option (Expr × Expr × Expr)) := do
  let c ← Meta.mkConstWithFreshMVarLevels name
  let cType ← Meta.inferType c
  let (mvars, _, body) ← Meta.forallMetaTelescope cType
  let body ← Meta.whnf body
  let (hd, args) := peelArgs body
  if !hd.isConstOf ``Iff || args.length < 2 then return none
  let src := if forward then args[0]! else args[1]!
  if !(← Meta.isDefEq src hypTy) then return none
  let lhs ← instantiateMVars args[0]!
  let rhs ← instantiateMVars args[1]!
  if lhs.hasMVar || rhs.hasMVar then return none
  let applied ← instantiateMVars (mkAppN c mvars)
  return some (applied, lhs, rhs)

/-- If `ty` is `¬P` or `P → False`, return `P`. -/
private def negatedProp? (ty : Expr) : Option Expr := do
  let (hd, args) := peelArgs ty
  if hd.isConstOf ``Not && args.length >= 1 then return args[0]!
  if ty.isArrow && ty.bindingBody!.isConstOf ``False then return ty.bindingDomain!
  failure

/-- Accumulated facts state for omega derivation. -/
private structure OmegaFactState where
  derivedFacts : Array (Expr × Expr × TSyntax `term) := #[]
  used : List String
  factNames : Array Name := #[]

/-- Try to add a derived fact if it's clean and non-duplicate. -/
private def OmegaFactState.addFact (s : OmegaFactState)
    (proofExpr : Expr) (propType : Expr) (proofStx : TSyntax `term)
    : MetaM OmegaFactState := do
  if containsGrindInternals propType then return s
  let isDup ← s.derivedFacts.anyM fun x =>
    try Meta.isDefEq propType x.2.1 catch _ => pure false
  if isDup then return s
  let (n, used') := chooseIntroName s.used.length `fact s.used
  return {
    derivedFacts := s.derivedFacts.push (proofExpr, propType, proofStx)
    used := used'
    factNames := s.factNames.push (Name.mkSimple n)
  }

/-- Resolve an expression to its syntax name (context fvar or derived fact). -/
private def resolveFactStx (e : Expr) (hypNameMap : Std.HashMap FVarId Name)
    (s : OmegaFactState) : Option Ident :=
  if e.isFVar then hypNameMap.get? e.fvarId! |>.map mkIdent
  else (s.derivedFacts.findIdx? fun x => x.1 == e).bind fun idx =>
    s.factNames[idx]?.map mkIdent

/-- Try omega with just context hypotheses. -/
private def tryOmegaWithContext (goalType : Expr) (lctx : LocalContext) :
    MetaM Bool := do
  let mut ctxFacts : List Expr := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    ctxFacts := (.fvar decl.fvarId) :: ctxFacts
  try
    let mvar ← Meta.mkFreshExprMVar (some goalType) .syntheticOpaque
    Lean.Elab.Tactic.Omega.omega ctxFacts mvar.mvarId!
    return true
  catch _ => return false

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
      -- Types differ (grind normalization). First try omega with just context.
      if ← tryOmegaWithContext goalType lctx then
        return some (#[← `(tactic| omega)], used)
      -- Omega alone failed. Introduce inner as `have`, then close with `omega`.
      let (haveName, used') := chooseIntroName used.length `fact used
      let haveNameIdent := mkIdent (Name.mkSimple haveName)
      let typeStx ← PrettyPrinter.delab innerType
      let (proofTactics, used'') ← decompileExpr innerWithArgs lctx localInsts used'
      let proofTacSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$proofTactics]*)
      let haveTac ← `(tactic| have $haveNameIdent : $typeStx := by $proofTacSeq)
      let closingTac ← `(tactic| omega)
      return some (#[haveTac, closingTac], used'')

  /-- Try replacing grind-internal proof terms with `omega`.
      Extracts Iff-typed facts from the proof term, matches them against
      context hypotheses to derive concrete facts, then tries `omega`.
      Uses a fixed-point loop since chained Iff lemmas may require
      multiple rounds (round 1 derives fact_1, round 2 uses it). -/
  private partial def tryDecompOmega (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    if !containsGrindInternals expr then return none
    withLCtx lctx localInsts do
      let goalType ← Meta.inferType expr
      -- Try omega with just context hypotheses
      if ← tryOmegaWithContext goalType lctx then
        return some (#[← `(tactic| omega)], used)
      let lemmaNames := extractGrindLemmaNames expr
      if lemmaNames.isEmpty then return none
      -- Context hypotheses and name map
      let mut ctxHyps : Array (Expr × Expr) := #[]
      let mut hypNameMap : Std.HashMap FVarId Name := {}
      for decl in lctx do
        if decl.isImplementationDetail then continue
        ctxHyps := ctxHyps.push (.fvar decl.fvarId, decl.type)
        hypNameMap := hypNameMap.insert decl.fvarId decl.userName
      let mut s : OmegaFactState := { used }
      -- Iteratively derive facts from Iff lemmas + context hypotheses
      for _ in [:3] do
        let prevSize := s.derivedFacts.size
        let allHyps := ctxHyps ++ (s.derivedFacts.map fun x => (x.1, x.2.1))
        for lname in lemmaNames do
          let lemmaStx := mkIdent lname
          for (hypExpr, hypTy) in allHyps do
            let some hypStx := resolveFactStx hypExpr hypNameMap s | continue
            -- Iff.mp — lhs matches hyp type
            if let some (lemmaExpr, lhs, rhs) ← try tryMatchIff lname hypTy true catch _ => pure none then
              let mpExpr := mkApp4 (mkConst ``Iff.mp) lhs rhs lemmaExpr hypExpr
              let mpStx ← `($(mkIdent ``Iff.mp) $lemmaStx $hypStx)
              let prevFactSize := s.derivedFacts.size
              s ← s.addFact mpExpr rhs mpStx
              -- Split And results
              if s.derivedFacts.size > prevFactSize then
                let parentIdx := s.derivedFacts.size - 1
                let (andFn, andArgs) := peelArgs rhs
                if andFn.isConstOf ``And && andArgs.length >= 2 then
                  let p := andArgs[0]!; let q := andArgs[1]!
                  let parentStx := mkIdent s.factNames[parentIdx]!
                  s ← s.addFact (mkApp3 (mkConst ``And.left) p q mpExpr) p (← `(($parentStx).1))
                  s ← s.addFact (mkApp3 (mkConst ``And.right) p q mpExpr) q (← `(($parentStx).2))
            -- mt Iff.mpr — hyp is ¬P, where P matches lhs
            if let some innerTy := negatedProp? hypTy then
              if let some (lemmaExpr, lhs, rhs) ← try tryMatchIff lname innerTy true catch _ => pure none then
                let mprFn := mkApp3 (mkConst ``Iff.mpr) lhs rhs lemmaExpr
                let mtResult := mkApp4 (mkConst ``mt) rhs lhs mprFn hypExpr
                let mtTy := mkApp (mkConst ``Not) rhs
                let mtStx ← `($(mkIdent ``mt) ($(mkIdent ``Iff.mpr) $lemmaStx) $hypStx)
                s ← s.addFact mtResult mtTy mtStx
        -- Specialize ∀-quantified context hypotheses with derived facts
        for (hypExpr, hypTy) in ctxHyps do
          if !hypTy.isForall then continue
          let some hypName := hypNameMap.get? hypExpr.fvarId! | continue
          let derivedPairs := s.derivedFacts.map fun x => (x.1, x.2.1)
          for (valExpr, valTy) in ctxHyps ++ derivedPairs do
            if valTy.isForall then continue
            if ← try Meta.isProp valTy catch _ => pure true then continue
            let some valStx := resolveFactStx valExpr hypNameMap s | continue
            let specialized := mkApp hypExpr valExpr
            let specializedTy ← try Meta.inferType specialized catch _ => continue
            let mut cur := specialized
            let mut curTy := specializedTy
            let mut curStx ← `($(mkIdent hypName) $valStx)
            for _ in [:5] do
              if !curTy.isArrow then break
              let dom := curTy.bindingDomain!
              let mut applied := false
              let derivedPairs' := s.derivedFacts.map fun x => (x.1, x.2.1)
              for (argExpr, argTy) in derivedPairs' ++ ctxHyps do
                if ← try Meta.isDefEq argTy dom catch _ => pure false then
                  let some argStx := resolveFactStx argExpr hypNameMap s | break
                  cur := mkApp cur argExpr
                  curTy ← try Meta.inferType cur catch _ => break
                  curStx ← `($curStx $argStx)
                  applied := true; break
              if !applied then break
            if (← try Meta.isProp curTy catch _ => pure false) && !curTy.isForall then
              s ← s.addFact cur curTy curStx
        if s.derivedFacts.size == prevSize then break  -- fixpoint
      if s.derivedFacts.isEmpty then return none
      -- Emit have statements + omega
      let mut haveTacs : Array (TSyntax `tactic) := #[]
      for i in [:s.derivedFacts.size] do
        let (_, _, proofStx) := s.derivedFacts[i]!
        haveTacs := haveTacs.push (← `(tactic| have $(mkIdent s.factNames[i]!) := $proofStx))
      return some (haveTacs.push (← `(tactic| omega)), s.used)

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
