import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.Helpers

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

/-- Some proposition-equality proof terms delaborate into anonymous structure
    literals like `{ mp := ..., mpr := ... }`, which are fragile in calc steps
    because the expected structure type is often not inferable there. Route
    these through recursive tactic generation instead of raw term reuse. -/
private def shouldRecursivelyDecompileCalcProof (proof : Expr) : Bool :=
  containsEagerReduce proof ||
    containsAutomationInternals proof ||
    containsConstName proof ``propext ||
    containsConstName proof ``Iff.intro

private def mkCleanIdent (name : Name) : Ident :=
  let raw := name.eraseMacroScopes.toString.toRawSubstring
  TSyntax.mk (Syntax.ident SourceInfo.none raw name.eraseMacroScopes [])

private def inferEqType? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← Meta.inferType e
  let (fn, args) := peelArgs ty
  if fn.isConstOf ``Eq && args.length >= 3 then
    return some (args[0]!, args[1]!, args[2]!)
  return none

/-- Smart `Eq.trans` that right-associates and drops `Eq.refl` sides. -/
private partial def mkEqTrans' (p1 p2 : Expr) : MetaM Expr := do
  -- Drop refl on either side
  match_expr p1 with
  | Eq.refl _ _ => return p2
  | _ => pure ()
  match_expr p2 with
  | Eq.refl _ _ => return p1
  | _ => pure ()
  -- Right-associate
  match_expr p1 with
  | Eq.trans _ _ _ _ p11 p12 => mkEqTrans' p11 (← mkEqTrans' p12 p2)
  | _ => mkAppM ``Eq.trans #[p1, p2]

/-- Smart `congrArg` that collapses trivial cases and pushes through trans. -/
private partial def mkCongrArg' (f p : Expr) : MetaM Expr := do
  -- Constant function ⇒ refl
  if let .lam _ _ b _ := f then
    if !b.hasLooseBVars then
      return ← mkEqRefl b
  -- Identity function ⇒ the proof itself
  if let .lam _ _ (.bvar 0) _ := f then
    return p
  -- Push through transitivity
  match_expr p with
  | Eq.trans _ _ _ _ p1 p2 =>
    return ← mkEqTrans' (← mkCongrArg' f p1) (← mkCongrArg' f p2)
  | _ => mkCongrArg f p

/-- Smart `congrFun`: congrFun h x = congrArg (fun f => f x) h -/
private def mkCongrFun' (h x : Expr) : MetaM Expr := do
  let some (α, _f1, _f2) := (← inferType h).eq?
    | throwError "Expected proof of equality"
  mkCongrArg' (.lam `f α (.app (.bvar 0) x) .default) h

/-- Smart `congr`: decompose into congrFun + congrArg composed via trans. -/
private def mkCongr' (x1 f2 : Expr) (p1 p2 : Expr) : MetaM Expr := do
  mkEqTrans' (← mkCongrFun' p1 x1) (← mkCongrArg' f2 p2)

/-- Smart `Eq.symm` that cancels refl/double-symm, pushes through trans and congrArg. -/
private partial def mkEqSymm' (h : Expr) : MetaM Expr := do
  match_expr h with
  | Eq.refl _ _ => return h
  | Eq.symm _ _ _ h => return h
  | Eq.trans _ _ _ _ p1 p2 =>
    mkEqTrans' (← mkEqSymm' p2) (← mkEqSymm' p1)
  | congrArg _ _ _ _ f p1 =>
    mkCongrArg' f (← mkEqSymm' p1)
  | _ => mkEqSymm h

/-- Simplify an Eq proof term using calcify-style smart constructors. -/
private partial def simplifyEqProof (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match_expr e with
  | Eq.trans _ _ _ _ p1 p2 =>
    mkEqTrans' (← simplifyEqProof p1) (← simplifyEqProof p2)
  | Eq.symm _ _ _ h =>
    mkEqSymm' (← simplifyEqProof h)
  | congrArg _ _ _ _ f p =>
    mkCongrArg' f (← simplifyEqProof p)
  | congr _ _ _ _ _ _ p1 p2 => do
    -- congr α β f₁ f₂ a₁ a₂ h₁ h₂
    let args := e.getAppArgs
    let x1 := args[4]!  -- a₁ (first value argument)
    let f2 := args[3]!  -- f₂ (second function)
    mkCongr' x1 f2 (← simplifyEqProof p1) (← simplifyEqProof p2)
  | congrFun _ _ _ _ p1 x =>
    mkCongrFun' (← simplifyEqProof p1) x
  | eq_of_heq _ _ _ h => do
    let h ← simplifyHEqProof h
    match_expr h with
    | HEq.refl _ x => mkEqRefl x
    | heq_of_eq _ _ _ h => return h
    | _ => mkEqOfHEq h
  | Eq.refl _ _ => return e
  | _ =>
    -- Handle Eq.ndrec: if the equality is Eq.refl, reduce to just the value
    if e.isAppOf ``Eq.ndrec && e.getAppNumArgs ≥ 6 then
      let args := e.getAppArgs
      let m := args[3]!     -- base value
      let h := args[5]!     -- equality proof
      let h ← simplifyEqProof h
      match_expr h with
      | Eq.refl _ _ =>
        -- Eq.ndrec m (Eq.refl a) = m, apply any extra args
        let extra := args[6:]
        return mkAppN m extra
      | _ =>
        -- Still an Eq.ndrec but with simplified equality; rebuild
        return e
    else
      return e
where
  /-- Simplify HEq proofs enough that eq_of_heq can collapse them. -/
  simplifyHEqProof (e : Expr) : MetaM Expr := do
    let e := e.headBeta
    match_expr e with
    | HEq.refl _ _ => return e
    | heq_of_eq _ _ _ h => do
      let h ← simplifyEqProof h
      match_expr h with
      | Eq.refl _ x => mkHEqRefl x
      | _ => mkAppM ``heq_of_eq #[h]
    | _ =>
      -- Handle HEq built via Eq.ndrec of HEq.refl
      if e.isAppOf ``Eq.ndrec && e.getAppNumArgs ≥ 6 then
        let args := e.getAppArgs
        let m := args[3]!
        let h := args[5]!
        let h ← simplifyEqProof h
        match_expr h with
        | Eq.refl _ _ => return mkAppN m args[6:]
        | _ => return e
      else
        return e

/-- Handle `congr` by naming function/argument equalities and recombining them. -/
def tryDecompCongr (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let some args := matchConstApp? expr ``congr 2 | return none
    let hEqFn := args[args.length - 2]!
    let hEqArg := args[args.length - 1]!
    let some _ ← inferEqType? hEqFn | return none
    let some _ ← inferEqType? hEqArg | return none
    let refineTac ← `(tactic| refine $(mkIdent ``congr) ?_ ?_)
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[hEqFn, hEqArg] lctx localInsts decompileExpr
    return some result

/-- Handle `congrArg` by naming the input equality and applying `congrArg`. -/
def tryDecompCongrArg (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let some args := matchConstApp? expr ``congrArg 2 | return none
    let f := args[args.length - 2]!
    let hEq := args[args.length - 1]!
    let some _ ← inferEqType? hEq | return none
    let fStx ← delabToRefinableSyntax f
    let refineTac ← `(tactic| refine $(mkIdent ``congrArg) $fStx ?_)
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[hEq] lctx localInsts decompileExpr
    return some result

/-- Render a single calc step proof as a term (calcify-style).

    For automation-heavy proof terms, prefer a term-level `by` block driven by
    recursive decompilation instead of re-elaborating the full raw term.
    This avoids brittle `eagerReduce` certificates and anonymous `Iff`
    structure literals that do not survive a plain delab/re-elab roundtrip. -/
private partial def getCalcProof (proof : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
    : DecompM Term := do
  match_expr proof with
  | Eq.symm _ _ _ h => do
    let h ← getCalcProof h lctx localInsts decompileExpr
    `(term| ($(h)).$(mkIdent `symm))
  | _ => do
    if shouldRecursivelyDecompileCalcProof proof then
      let proofTactics ← LeanDecomp.decompileOrExact proof lctx localInsts decompileExpr
      `(term| by $proofTactics:tactic*)
    else
      let termStx ← delabToRefinableSyntax proof
      pure termStx

/-- Walk a normalized `Eq.trans` chain collecting `calcStep` syntax nodes.
    Skips `Eq.refl` steps since they are no-ops. -/
private partial def getCalcSteps (proof : Expr) (acc : Array (TSyntax ``calcStep))
    (lctx : LocalContext) (localInsts : LocalInstances)
    (decompileExpr : DecompileCallback) : DecompM (Array (TSyntax ``calcStep)) :=
  match_expr proof with
  | Eq.trans _ _ rhs _ p1 p2 => do
    match_expr p1 with
    | Eq.refl _ _ => getCalcSteps p2 acc lctx localInsts decompileExpr  -- skip refl steps
    | _ =>
      let proofStx ← getCalcProof p1 lctx localInsts decompileExpr
      let step ← `(calcStep| _ = $(← delabToRefinableSyntax rhs) := $proofStx)
      getCalcSteps p2 (acc.push step) lctx localInsts decompileExpr
  | Eq.refl _ _ => return acc  -- skip trailing refl
  | _ => do
    let type ← whnf (← Meta.inferType proof)
    let some (_, _, rhs) := type.eq?
      | throwError "Expected proof of equality, got {type}"
    let proofStx ← getCalcProof proof lctx localInsts decompileExpr
    let step ← `(calcStep| _ = $(← delabToRefinableSyntax rhs) := $proofStx)
    return acc.push step

/-- Handle `Eq.symm` by naming the input equality and reusing `Eq.symm`. -/
def tryDecompEqSymm (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let some args := matchConstApp? expr ``Eq.symm 1 | return none
    let some inEq := args.getLast? | return none
    let some (_α, _lhs, _rhs) ← inferEqType? inEq | return none
    let refineTac ← `(tactic| refine $(mkIdent ``Eq.symm) ?_)
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[inEq] lctx localInsts decompileExpr
    return some result

/-- Handle `Eq.trans` by normalizing (calcify-style) and emitting a `calc` block. -/
def tryDecompEqTrans (expr : Expr) (lctx : LocalContext)
  (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let some _args := matchConstApp? expr ``Eq.trans 2 | return none

    let exprNorm ← simplifyEqProof expr
    let type ← whnf (← Meta.inferType exprNorm)
    let some (_, lhs, _) := type.eq?
      | return none

    -- After normalization, the expr may no longer be Eq.trans (e.g. collapsed to single step)
    match_expr exprNorm with
    | Eq.refl _ _ => do
      let tac ← `(tactic| rfl)
      return some #[tac]
    | Eq.trans _ _ _ _ _ _ => do
      let stepStx ← getCalcSteps exprNorm #[] lctx localInsts decompileExpr
      let calcTac ← `(tactic| calc
            $(← delabToRefinableSyntax lhs):term
            $stepStx*)
      return some #[calcTac]
    | _ => do
      -- Single-step result after normalization; just delaborate it
      let proofStx ← delabToRefinableSyntax exprNorm
      let tac ← `(tactic| exact $proofStx)
      return some #[tac]

/-- Handle proposition-valued `Eq.rec`/`Eq.ndrec` transports by converting them
    back into an explicit `Eq.mp` step. `convert` often leaves these wrappers
    around a large theorem application; exposing the transport and base proof as
    separate subgoals gives the decompiler a chance to recurse structurally. -/
def tryDecompEqRecPropTransport (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some constName := Expr.constName? fn | return none
    if constName != ``Eq.rec && constName != ``Eq.ndrec then
      return none
    if args.length < 6 then
      return none

    let motive := args[2]!
    let base := args[3]!
    let hEq := args[5]!
    let baseWithArgs := (args.drop 6).foldl (init := base) fun acc arg => mkApp acc arg

    let sourceTy ← instantiateMVars (← Meta.inferType baseWithArgs)
    let targetTy ← instantiateMVars (← Meta.inferType expr)
    if !(← Meta.isProp sourceTy) || !(← Meta.isProp targetTy) then
      return none

    let hEqNorm ← simplifyEqProof hEq

    -- Expanded definition of `Eq.mp` / proposition transport:
    --   Eq.rec base target (fun x h => x) hEq
    -- Collapse it back to an explicit cast so the existing Eq.mp handler can recurse.
    let motiveShape ← Meta.lambdaTelescope motive fun xs body => do
      pure (xs.size, xs.size == 2 && body == xs[0]!)
    if motiveShape.2 then
      let some (_, lhs, rhs) ← inferEqType? hEqNorm
        | return none
      let transportEq ←
        if (← Meta.isDefEq lhs sourceTy) && (← Meta.isDefEq rhs targetTy) then
          pure hEqNorm
        else if (← Meta.isDefEq lhs targetTy) && (← Meta.isDefEq rhs sourceTy) then
          mkEqSymm' hEqNorm
        else
          return none
      let sourceTyStx ← delabToRefinableSyntax sourceTy
      let targetTyStx ← delabToRefinableSyntax targetTy
      let eqMpIdent := mkCleanIdent ``Eq.mp
      let refineTac ← `(tactic| refine @$eqMpIdent:ident $sourceTyStx $targetTyStx ?_ ?_)
      let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[transportEq, baseWithArgs] lctx localInsts decompileExpr
      return some result

    -- Only handle the ordinary nondependent transport case where the motive is
    -- a single-argument proposition-valued function. Truly dependent motives
    -- require a different reconstruction than `congrArg motive hEq`.
    let motiveInfo ← Meta.lambdaTelescope motive fun xs body => do
      let body ← instantiateMVars body
      pure (xs.size, body.hasLooseBVars)
    if motiveInfo.1 != 1 || motiveInfo.2 then
      return none

    let transportEq ← mkCongrArg' motive hEqNorm
    let sourceTyStx ← delabToRefinableSyntax sourceTy
    let targetTyStx ← delabToRefinableSyntax targetTy
    let eqMpIdent := mkCleanIdent ``Eq.mp
    let refineTac ← `(tactic| refine @$eqMpIdent:ident $sourceTyStx $targetTyStx ?_ ?_)
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[transportEq, baseWithArgs] lctx localInsts decompileExpr
    return some result

/-- Handle `Eq.mp` casts structurally by refining with holes for the transport
  equality and transported proof, then recursively decompiling both sides.
  This avoids raw delab/re-elab of arithmetic certificate terms. -/
def tryDecompEqMp (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``Eq.mp then
      return none

    let mut eqProofArg? : Option Expr := none
    let mut sourceTy? : Option Expr := none
    for a in args do
      let aTy ← Meta.inferType a
      let (tyFn, tyArgs) := peelArgs aTy
      if tyFn.isConstOf ``Eq && tyArgs.length >= 3 then
        let lhs := tyArgs[1]!
        eqProofArg? := some a
        sourceTy? := some lhs
        break

    let some eqProofArg := eqProofArg?
      | return none
    let some sourceTy := sourceTy?
      | return none

    let mut sourceProofArg? : Option Expr := none
    for a in args do
      if a == eqProofArg then
        continue
      let aTy ← Meta.inferType a
      if (← Meta.isDefEq aTy sourceTy) then
        sourceProofArg? := some a
        break

    let some sourceProofArg := sourceProofArg?
      | return none

    let targetTy ← Meta.inferType expr
    let eqProofNorm ← simplifyEqProof eqProofArg
    let sourceTyStx ← delabToRefinableSyntax sourceTy
    let targetTyStx ← delabToRefinableSyntax targetTy
    let eqMpIdent := mkCleanIdent ``Eq.mp
    let refineTac ← `(tactic| refine @$eqMpIdent:ident $sourceTyStx $targetTyStx ?_ ?_)
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[eqProofNorm, sourceProofArg] lctx localInsts decompileExpr
    return some result

/-- Common tail for the `forall_congr` / `implies_congr` peelers.  Given a
    "post-intro" lctx (possibly equal to the outer lctx if no intro is needed),
    a witness expression for `have h := <ev>`, and an inner `Eq` proof, emit:

      <introTacs>; have h := <ev>; <fast-path lia | recurse on Eq.mp eqProof h>

    `tryFastPath` is `true` for the *instantiated* sub-cases where the goal at
    the peel point is already a specific arithmetic statement and `lia` may
    close from the user-form hypothesis directly (the L70 / L36 win).  For
    the *universal* sub-cases the goal is still a `∀` after the intro, so the
    fast-path attempt is a near-certain miss; skip it to avoid burning
    heartbeats on a doomed `lia`. -/
private def emitHavePeel
    (introTacs : Array (TSyntax `tactic))
    (postIntroLctx : LocalContext) (postIntroInsts : LocalInstances)
    (witness : Expr) (hName : String)
    (innerEqProof : Expr) (remainingArgs : List Expr)
    (outerExprTy : Expr) (tryFastPath : Bool)
    (decompileExpr : DecompileCallback)
  : DecompM (Array (TSyntax `tactic)) := do
  let witnessTy ← withLCtx postIntroLctx postIntroInsts (Meta.inferType witness)
  let hFvarId := FVarId.mk (← mkFreshId)
  let lctxWithH := postIntroLctx.mkLocalDecl hFvarId (Name.mkSimple hName) witnessTy
  let hInsts ← withLCtx lctxWithH postIntroInsts getLocalInstances
  let witnessStx ← withLCtx postIntroLctx postIntroInsts (delabToRefinableSyntax witness)
  let hIdent := mkIdent (Name.mkSimple hName)
  let haveTac ← `(tactic| have $hIdent:ident := $witnessStx)
  let prefixTacs := introTacs.push haveTac
  if tryFastPath then
    let liaTac ← `(tactic| lia)
    if ← LeanDecomp.candidateTacticsCloseGoal #[liaTac] outerExprTy lctxWithH hInsts then
      return prefixTacs.push liaTac
    let unfoldLiaTac ← `(tactic| with_unfolding_all lia)
    if ← LeanDecomp.candidateTacticsCloseGoal #[unfoldLiaTac] outerExprTy lctxWithH hInsts then
      return prefixTacs.push unfoldLiaTac
  let innerCore ← withLCtx lctxWithH hInsts do
    Meta.mkAppM ``Eq.mp #[innerEqProof, Expr.fvar hFvarId]
  let innerTerm := remainingArgs.foldl (init := innerCore) fun acc a => mkApp acc a
  let innerTactics ← decompileExpr innerTerm lctxWithH hInsts
  return prefixTacs ++ innerTactics

/-- Handle `Eq.mp (forall_congr <body>) <evidence>` (with optional trailing
    applications) where `evidence : ∀ a, p a` transports to `∀ a, q a`.

    Two cases based on whether the proof has trailing args after `evidence`:

    - **Universal** (no trailing args, goal is `∀ a, q a`): emit `intro x; have
      h_user := <evidence> x; <recurse>` where the recursion target is
      `Eq.mp (<body> x) h_user` of type `q x`.  The `have` puts the user-form
      hypothesis in the lctx so downstream `lia` can find it.

    - **Instantiated** (trailing args `x_spec, …`, goal is `q x_spec …`):
      construct the inner term directly with the specific instantiation —
      `Eq.mp (<body> x_spec) (<evidence> x_spec)` then apply remaining args.
      No intro needed; the recursion runs in the existing lctx.

    `forall_congr` is a stdlib lemma used by any tactic that transports a
    `∀`-typed value through pointwise equalities — not grind-specific.  The
    grind-specific leaf certificates inside `<body>` (e.g. `Int.Linear.norm_le`)
    are handled by `Specialized/Grind.lean` after this peel exposes them. -/
def tryDecompEqMpForallCongr (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let some args := matchConstApp? expr ``Eq.mp 4 | return none
    let eqProof := args[2]!
    let evidence := args[3]!
    let trailingArgs := args.drop 4
    let some eqArgs := matchConstApp? eqProof ``forall_congr 4 | return none
    let body := eqArgs[3]!
    let outerExprTy ← Meta.inferType expr
    if h : trailingArgs.length > 0 then
      -- Instantiated case: trailingArgs[0] specializes the universal binder.
      let xSpec := trailingArgs[0]
      let remaining := trailingArgs.drop 1
      let bodyAtX ← Meta.whnf (mkApp body xSpec)
      let evidenceAtX := mkApp evidence xSpec
      let hName ← LeanDecomp.chooseIntroName (← LeanDecomp.getUsed).length `h
      let result ← emitHavePeel #[] lctx localInsts evidenceAtX hName
        bodyAtX remaining outerExprTy true decompileExpr
      return some result
    -- Universal case: telescope the body lambda, intro a fresh fvar, have the evidence.
    Meta.lambdaTelescope body fun bodyXs bodyResult => do
      if bodyXs.size != 1 then return none
      let xFvar := bodyXs[0]!
      let some xFvarId := xFvar.fvarId? | return none
      let xDecl ← xFvarId.getDecl
      let xName ← LeanDecomp.chooseIntroName (← LeanDecomp.getUsed).length xDecl.userName
      let lctxWithX := (← getLCtx).setUserName xFvarId (Name.mkSimple xName)
      let xInsts ← getLocalInstances
      let evidenceAtX := mkApp evidence xFvar
      let hName ← LeanDecomp.chooseIntroName (← LeanDecomp.getUsed).length `h
      let xIdent := mkIdent (Name.mkSimple xName)
      let introTac ← `(tactic| intro $xIdent:ident)
      let result ← emitHavePeel #[introTac] lctxWithX xInsts evidenceAtX hName
        bodyResult [] outerExprTy false decompileExpr
      return some result

/-- Handle `Eq.mp (implies_congr p_eq q_eq) <evidence>` (with optional trailing
    applications) where `evidence : p → q` transports to `p' → q'`.

    Only the case `p_eq = Eq.refl _` (so `p = p'`) is handled — the common
    shape grind emits, e.g. `implies_congr Eq.refl (Int.Linear.norm_le ...)`
    to rewrite the conclusion of an implication while the premise stays fixed.

    Two sub-cases:
    - **Premise applied** (one trailing arg `hp_spec : p`): construct
      `Eq.mp q_eq (<evidence> hp_spec)` and recurse.
    - **No trailing arg** (goal is `p' → q'`): emit `intro hp; have h_user :=
      <evidence> hp; <recurse>` with target `Eq.mp q_eq h_user`.

    The harder case `p_eq ≠ Eq.refl` would need to additionally transport
    `hp` backward (`Eq.mpr p_eq hp`) before applying the evidence — deferred. -/
def tryDecompEqMpImpliesCongr (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
  : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let some args := matchConstApp? expr ``Eq.mp 4 | return none
    let eqProof := args[2]!
    let evidence := args[3]!
    let trailingArgs := args.drop 4
    let some eqArgs := matchConstApp? eqProof ``implies_congr 6 | return none
    let pEq := eqArgs[4]!
    let qEq := eqArgs[5]!
    let some _ := matchConstApp? pEq ``Eq.refl 0 | return none
    let outerExprTy ← Meta.inferType expr
    if h : trailingArgs.length > 0 then
      -- Premise-applied case.
      let hpSpec := trailingArgs[0]
      let remaining := trailingArgs.drop 1
      let evidenceAtHp := mkApp evidence hpSpec
      let hName ← LeanDecomp.chooseIntroName (← LeanDecomp.getUsed).length `h
      let result ← emitHavePeel #[] lctx localInsts evidenceAtHp hName
        qEq remaining outerExprTy true decompileExpr
      return some result
    -- Universal case.
    let p2 := eqArgs[1]!
    let hpName ← LeanDecomp.chooseIntroName (← LeanDecomp.getUsed).length `hp
    let hpFvarId := FVarId.mk (← mkFreshId)
    let lctxWithHp := lctx.mkLocalDecl hpFvarId (Name.mkSimple hpName) p2
    let hpInsts ← withLCtx lctxWithHp localInsts getLocalInstances
    let evidenceAtHp := mkApp evidence (Expr.fvar hpFvarId)
    let hUserName ← LeanDecomp.chooseIntroName (← LeanDecomp.getUsed).length `h
    let hpIdent := mkIdent (Name.mkSimple hpName)
    let introTac ← `(tactic| intro $hpIdent:ident)
    let result ← emitHavePeel #[introTac] lctxWithHp hpInsts evidenceAtHp hUserName
      qEq [] outerExprTy false decompileExpr
    return some result

end LeanDecomp
