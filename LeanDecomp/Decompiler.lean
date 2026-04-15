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
  falseFactName? : Option Name := none

/-- Try to add a derived fact if it's clean and non-duplicate. -/
private def OmegaFactState.addFact (s : OmegaFactState)
    (proofExpr : Expr) (propType : Expr) (proofStx : TSyntax `term)
    : MetaM OmegaFactState := do
  if containsGrindInternals propType then return s
  let isDup ← s.derivedFacts.anyM fun x =>
    try Meta.isDefEq propType x.2.1 catch _ => pure false
  if isDup then return s
  let (n, used') := chooseIntroName s.used.length `fact s.used
  let newName := Name.mkSimple n
  let isFalse ← try (do let ty ← Meta.whnf propType; pure (ty.isConstOf ``False)) catch _ => pure false
  -- When the fact is a False proof, use the full delab of the proof expression so the
  -- have-statement re-elaborates correctly (the syntactic shorthand may not type-check as False).
  -- Skip if the proof expression itself contains grind internals (would produce unreadable syntax).
  let effectiveStx ← if isFalse then
    if containsGrindInternals proofExpr then return s
    else try delabToRefinableSyntax proofExpr catch _ => pure proofStx
  else
    pure proofStx
  -- Skip if the rendered syntax contains grind-internal identifiers.
  let stxStr := toString (← PrettyPrinter.ppTerm effectiveStx)
  if stxStr.contains "Int.Linear." || stxStr.contains "Lean.RArray."
      || stxStr.contains "Lean.Grind." || stxStr.contains "eagerReduce" then
    return s
  return {
    derivedFacts := s.derivedFacts.push (proofExpr, propType, effectiveStx)
    used := used'
    factNames := s.factNames.push newName
    falseFactName? := if isFalse then some newName else s.falseFactName?
  }

/-- Resolve an expression to its syntax name (context fvar or derived fact). -/
private def resolveFactStx (e : Expr) (hypNameMap : Std.HashMap FVarId Name)
    (s : OmegaFactState) : Option Ident :=
  if e.isFVar then hypNameMap.get? e.fvarId! |>.map mkIdent
  else (s.derivedFacts.findIdx? fun x => x.1 == e).bind fun idx =>
    s.factNames[idx]?.map mkIdent

/-- Find an already-derived fact name by proposition type. -/
private def findFactByType (s : OmegaFactState) (ty : Expr) : MetaM (Option Ident) := do
  for i in [:s.derivedFacts.size] do
    let (_, propTy, _) := s.derivedFacts[i]!
    if ← try Meta.isDefEq propTy ty catch _ => pure false then
      return some (mkIdent s.factNames[i]!)
  return none

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

/-- Strip chains of grind-generated `Eq.mp` casts around proof terms. -/
private partial def stripGrindCasts : Expr → Expr
  | e =>
    let (fn, args) := peelArgs e
    if fn.constName? == some ``Eq.mp && args.length >= 4 && containsGrindInternals args[2]! then
      stripGrindCasts args[3]!
    else e

/-- Also strip Eq.rec casts (type transports). -/
private partial def stripAllGrindCasts (e : Expr) : Expr :=
  let e := stripGrindCasts e
  let (fn, args) := peelArgs e
  -- Strip Eq.rec: Eq.rec takes 6 args, the actual proof is args[3]
  if fn.constName? == some ``Eq.rec && args.length >= 6 then
    stripAllGrindCasts args[3]!
  -- Strip Eq.ndrec similarly
  else if fn.constName? == some ``Eq.ndrec && args.length >= 5 then
    stripAllGrindCasts args[3]!
  else e

/-- If `ty` reduces to `Iff lhs rhs`, return `(lhs, rhs)`. -/
private def iffSides? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← Meta.whnf ty
  let (hd, args) := peelArgs ty
  if hd.isConstOf ``Iff && args.length >= 2 then
    return some (args[0]!, args[1]!)
  return none

/-- Build a term syntax for applying an `Iff` proof to a hypothesis syntax.
    For inline `Iff.intro` proofs, simplify directly to the forward/backward function. -/
private def mkIffApplyStx (iffProof : Expr) (hypStx : TSyntax `term) (forward : Bool) : MetaM (TSyntax `term) := do
  let iffProof := stripGrindCasts iffProof
  let (fn, args) := peelArgs iffProof
  if fn.constName? == some ``Iff.intro && args.length >= 4 then
    let dirFn := if forward then args[2]! else args[3]!
    let dirFnStx ← delabToRefinableSyntax dirFn
    `($dirFnStx $hypStx)
  else
    let iffStx ← delabToRefinableSyntax iffProof
    if forward then
      `($(mkIdent ``Iff.mp) $iffStx $hypStx)
    else
      `($(mkIdent ``Iff.mpr) $iffStx $hypStx)

/-- Decompile a proof expression into a term syntax, using derived fact names,
    context hypothesis names, and `by omega` for grind-internal arithmetic leaves.
    Returns `none` if the expression cannot be cleanly decompiled. -/
private partial def buildTermFromProof (e : Expr) (hypNameMap : Std.HashMap FVarId Name)
    (s : OmegaFactState) (depth : Nat := 0) : MetaM (Option (TSyntax `term)) := do
  if depth > 30 then return none
  let e := stripAllGrindCasts e
  -- Known derived fact or hypothesis → resolve to name
  if let some ident := resolveFactStx e hypNameMap s then
    return some ident
  -- Clean expression (no grind internals) → just delab
  if !containsGrindInternals e then
    let stx ← try delabToRefinableSyntax e catch _ => return none
    return some stx
  let (fn, args) := peelArgs e
  let cname := fn.constName?
  -- And.intro: build ⟨left, right⟩
  if cname == some ``And.intro && args.length >= 4 then
    let left := args[2]!
    let right := args[3]!
    let some leftStx ← buildTermFromProof left hypNameMap s (depth + 1) | return none
    let some rightStx ← buildTermFromProof right hypNameMap s (depth + 1) | return none
    return some (← `(⟨$leftStx, $rightStx⟩))
  -- And.left / And.right (3-arg, non-over-applied)
  if (cname == some ``And.left || cname == some ``And.right) && args.length == 3 then
    let pairProof := args[2]!
    let some pairStx ← buildTermFromProof pairProof hypNameMap s (depth + 1) | return none
    if cname == some ``And.left then
      return some (← `(($pairStx).1))
    else
      return some (← `(($pairStx).2))
  -- Iff.mp / Iff.mpr: use mkIffApplyStx
  if cname == some ``Iff.mp && args.length >= 4 then
    let iffProof := stripGrindCasts args[2]!
    let hypProof := args[3]!
    let some hypStx ← buildTermFromProof hypProof hypNameMap s (depth + 1) | return none
    return some (← mkIffApplyStx iffProof hypStx true)
  if cname == some ``Iff.mpr && args.length >= 4 then
    let iffProof := stripGrindCasts args[2]!
    let hypProof := args[3]!
    let some hypStx ← buildTermFromProof hypProof hypNameMap s (depth + 1) | return none
    return some (← mkIffApplyStx iffProof hypStx false)
  -- General function application: try to decompose f(a)
  if let .app f a := e then
    let some fStx ← buildTermFromProof f hypNameMap s (depth + 1) | return none
    let some aStx ← buildTermFromProof a hypNameMap s (depth + 1) | return none
    return some (← `($fStx $aStx))
  -- Grind-internal leaf with clean type: replace with (by omega : T)
  let eTy ← try Meta.inferType e catch _ => return none
  if containsGrindInternals eTy then return none
  let tyStx ← try PrettyPrinter.delab eTy catch _ => return none
  return some (← `((by omega : $tyStx)))

/-- Walk a proof term and derive omega-relevant facts from explicit structure.
    This is a direct, single-pass extraction (no lemma search, no fixed-point). -/
private partial def walkProofForFacts (e : Expr) (hypNameMap : Std.HashMap FVarId Name)
    (s0 : OmegaFactState) : MetaM (Option Ident × OmegaFactState) := do
  let e := stripGrindCasts e
  if e.isFVar then
    return (hypNameMap.get? e.fvarId! |>.map mkIdent, s0)

  let (fn, args) := peelArgs e
  let mut s := s0
  for arg in args do
    let (_, s') ← walkProofForFacts arg hypNameMap s
    s := s'

  let cname := fn.constName?

  if cname == some ``Iff.mp && args.length >= 4 then
    let iffProof := stripGrindCasts args[2]!
    let hypProof := stripGrindCasts args[3]!
    let hypStx : TSyntax `term ←
      if let some h := resolveFactStx hypProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax hypProof
    let some (_, rhs) ← iffSides? (← Meta.inferType iffProof) | return (none, s)
    let mpStx ← mkIffApplyStx iffProof hypStx true
    let prevSize := s.derivedFacts.size
    s ← s.addFact e rhs mpStx
    let mut curName? : Option Ident := none
    if s.derivedFacts.size > prevSize then
      let parentIdx := s.derivedFacts.size - 1
      let parentStx := mkIdent s.factNames[parentIdx]!
      curName? := some parentStx
      let (andFn, andArgs) := peelArgs rhs
      if andFn.isConstOf ``And && andArgs.length >= 2 then
        let p := andArgs[0]!
        let q := andArgs[1]!
        s ← s.addFact (mkApp3 (mkConst ``And.left) p q e) p (← `(($parentStx).1))
        s ← s.addFact (mkApp3 (mkConst ``And.right) p q e) q (← `(($parentStx).2))
    else
      curName? ← findFactByType s rhs
    return (curName?, s)

  if cname == some ``Iff.mpr && args.length >= 4 then
    let iffProof := stripGrindCasts args[2]!
    let hypProof := stripGrindCasts args[3]!
    let hypStx : TSyntax `term ←
      if let some h := resolveFactStx hypProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax hypProof
    let some (lhs, _) ← iffSides? (← Meta.inferType iffProof) | return (none, s)
    let mprStx ← mkIffApplyStx iffProof hypStx false
    let prevSize := s.derivedFacts.size
    s ← s.addFact e lhs mprStx
    if s.derivedFacts.size > prevSize then
      return (some (mkIdent s.factNames.back!), s)
    return (← findFactByType s lhs, s)

  if cname == some ``mt && args.length >= 4 then
    let fnProof := stripGrindCasts args[2]!
    let hypProof := stripGrindCasts args[3]!
    let hypStx : TSyntax `term ←
      if let some h := resolveFactStx hypProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax hypProof
    let fnStx ← delabToRefinableSyntax fnProof
    let mtTy ← try Meta.inferType e catch _ => return (none, s)
    let mtStx ← `($(mkIdent ``mt) $fnStx $hypStx)
    let prevSize := s.derivedFacts.size
    s ← s.addFact e mtTy mtStx
    if s.derivedFacts.size > prevSize then
      return (some (mkIdent s.factNames.back!), s)
    return (← findFactByType s mtTy, s)

  if (cname == some ``And.left || cname == some ``And.right) && args.length >= 3 then
    let pairProof := stripGrindCasts args[2]!
    let pairStx : TSyntax `term ←
      if let some h := resolveFactStx pairProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax pairProof
    let projTy ← try Meta.inferType e catch _ => return (none, s)
    let projStx ← if cname == some ``And.left then
      `(($pairStx).1)
    else
      `(($pairStx).2)
    let prevSize := s.derivedFacts.size
    s ← s.addFact e projTy projStx
    if s.derivedFacts.size > prevSize then
      return (some (mkIdent s.factNames.back!), s)
    return (← findFactByType s projTy, s)

  return (resolveFactStx e hypNameMap s, s)

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
      Extracts facts directly from the low-level proof term structure,
      then tries `omega` with those explicit facts. -/
  private partial def tryDecompOmega (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
    if !containsGrindInternals expr then return none
    withLCtx lctx localInsts do
      let goalType ← Meta.inferType expr
      -- Try omega with just context hypotheses
      if ← tryOmegaWithContext goalType lctx then
        return some (#[← `(tactic| omega)], used)
      -- Context hypotheses and name map
      let mut ctxHyps : Array (Expr × Expr) := #[]
      let mut hypNameMap : Std.HashMap FVarId Name := {}
      for decl in lctx do
        if decl.isImplementationDetail then continue
        ctxHyps := ctxHyps.push (.fvar decl.fvarId, decl.type)
        hypNameMap := hypNameMap.insert decl.fvarId decl.userName
      let mut s : OmegaFactState := { used }
      let (_, s') ← walkProofForFacts expr hypNameMap s
      s := s'
      -- Single specialization pass for ∀-quantified context hypotheses.
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
          if s.derivedFacts.isEmpty then return none
      -- Emit have statements and close.
      let mut haveTacs : Array (TSyntax `tactic) := #[]
      for i in [:s.derivedFacts.size] do
        let (_, _, proofStx) := s.derivedFacts[i]!
        haveTacs := haveTacs.push (← `(tactic| have $(mkIdent s.factNames[i]!) := $proofStx))
      let closingTac ← match s.falseFactName? with
        | some n =>
            let falseElim := Lean.mkCIdent ``False.elim
            `(tactic| exact $falseElim $(mkIdent n))
        | none   => do
            -- Try interval membership closing: exact factI (Iff.mpr mem_X ⟨by omega, by omega⟩)
            -- This handles the common pattern where a negation fact ¬(x ∈ Ioc a b) blocks omega.
            let mut memberClosing? : Option (TSyntax `tactic) := none
            for i in [:s.derivedFacts.size] do
              if memberClosing?.isSome then break
              let (factExpr, factTy, _) := s.derivedFacts[i]!
              if negatedProp? factTy |>.isNone then continue
              for memLemma in [`Finset.mem_Ioc, `Finset.mem_Ico, `Finset.mem_Icc, `Finset.mem_Ioo,
                               `Set.mem_Ioc, `Set.mem_Ico, `Set.mem_Icc, `Set.mem_Ioo] do
                let matched ← try
                    let iffConst ← Meta.mkConstWithFreshMVarLevels memLemma
                    let iffTy ← Meta.inferType iffConst
                    let (mvars, _, _) ← Meta.forallMetaTelescope iffTy
                    let iffApplied := mkAppN iffConst mvars
                    let mprExpr ← Meta.mkAppM ``Iff.mpr #[iffApplied]
                    let fTy ← Meta.inferType mprExpr
                    let B := fTy.bindingBody!
                    let factExprTy ← Meta.inferType factExpr
                    let notB := mkApp (mkConst ``Not) B
                    guard (← Meta.isDefEq factExprTy notB)
                    pure true
                catch _ => pure false
                if !matched then continue
                let factIdent := mkIdent s.factNames[i]!
                let lemmaIdent := mkIdent memLemma
                let iffMpr := mkIdent ``Iff.mpr
                memberClosing? := some (← `(tactic| exact $factIdent ($iffMpr $lemmaIdent ⟨by omega, by omega⟩)))
                break
            match memberClosing? with
            | some stx => pure stx
            | none =>
              match ← buildTermFromProof expr hypNameMap s with
              | some termStx => `(tactic| exact $termStx)
              | none => `(tactic| omega)
      return some (haveTacs.push closingTac, s.used)

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
