import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.Helpers

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

private def mkCleanIdent (name : Name) : Ident :=
  let raw := name.eraseMacroScopes.toString.toRawSubstring
  TSyntax.mk (Syntax.ident SourceInfo.none raw name.eraseMacroScopes [])

/-- Local argument peeler to avoid cross-module utility coupling. -/
private def peelApps (e : Expr) : Expr × List Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × List Expr :=
    match e with
    | Expr.app f arg => go f (arg :: acc)
    | _ => (e, acc)
  go e []

private def inferEqType? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← Meta.inferType e
  let (fn, args) := peelApps ty
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
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``congr then
      return none
    if args.length < 2 then
      return none

    let hEqFn := args[args.length - 2]!
    let hEqArg := args[args.length - 1]!
    let some _ ← inferEqType? hEqFn
      | return none
    let some _ ← inferEqType? hEqArg
      | return none

    let (eqFnTactics, used1) ← decompileExpr hEqFn lctx localInsts used
    let (eqFnName, used2) := chooseIntroName used1.length `hEqFn used1
    let eqFnIdent := mkIdent (Name.mkSimple eqFnName)
    let eqFnTyStx ← delabToRefinableSyntax (← Meta.inferType hEqFn)
    let eqFnSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqFnTactics]*)
    let letEqFnTac ← `(tactic| let $eqFnIdent : $eqFnTyStx := by $eqFnSeq)

    let (eqArgTactics, used3) ← decompileExpr hEqArg lctx localInsts used2
    let (eqArgName, used4) := chooseIntroName used3.length `hEqArg used3
    let eqArgIdent := mkIdent (Name.mkSimple eqArgName)
    let eqArgTyStx ← delabToRefinableSyntax (← Meta.inferType hEqArg)
    let eqArgSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqArgTactics]*)
    let letEqArgTac ← `(tactic| let $eqArgIdent : $eqArgTyStx := by $eqArgSeq)

    let exactTac ← `(tactic| exact $(mkIdent ``congr) $eqFnIdent $eqArgIdent)
    return some (#[letEqFnTac, letEqArgTac, exactTac], used4)

/-- Handle `congrArg` by naming the input equality and applying `congrArg`. -/
def tryDecompCongrArg (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``congrArg then
      return none
    if args.length < 2 then
      return none

    let f := args[args.length - 2]!
    let hEq := args[args.length - 1]!
    let some _ ← inferEqType? hEq
      | return none

    let (eqTactics, used1) ← decompileExpr hEq lctx localInsts used
    let (eqName, used2) := chooseIntroName used1.length `hEq used1
    let eqIdent := mkIdent (Name.mkSimple eqName)
    let eqTyStx ← delabToRefinableSyntax (← Meta.inferType hEq)
    let eqSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqTactics]*)
    let letEqTac ← `(tactic| let $eqIdent : $eqTyStx := by $eqSeq)

    let fStx ← delabToRefinableSyntax f
    let exactTac ← `(tactic| exact $(mkIdent ``congrArg) $fStx $eqIdent)
    return some (#[letEqTac, exactTac], used2)

/-- Render a single calc step proof as a term (calcify-style). -/
private partial def getCalcProof (proof : Expr) : MetaM Term :=
  match_expr proof with
  | Eq.symm _ _ _ h => do
    let h ← getCalcProof h
    `($(h).$(mkIdent `symm))
  | _ => delabToRefinableSyntax proof

/-- Walk a normalized `Eq.trans` chain collecting `calcStep` syntax nodes.
    Skips `Eq.refl` steps since they are no-ops. -/
private partial def getCalcSteps (proof : Expr) (acc : Array (TSyntax ``calcStep))
    : MetaM (Array (TSyntax ``calcStep)) :=
  match_expr proof with
  | Eq.trans _ _ rhs _ p1 p2 => do
    match_expr p1 with
    | Eq.refl _ _ => getCalcSteps p2 acc  -- skip refl steps
    | _ =>
      let step ← `(calcStep| _ = $(← delabToRefinableSyntax rhs) := $(← getCalcProof p1))
      getCalcSteps p2 (acc.push step)
  | Eq.refl _ _ => return acc  -- skip trailing refl
  | _ => do
    let type ← whnf (← Meta.inferType proof)
    let some (_, _, rhs) := type.eq?
      | throwError "Expected proof of equality, got {type}"
    let step ← `(calcStep| _ = $(← delabToRefinableSyntax rhs) := $(← getCalcProof proof))
    return acc.push step

/-- Handle `Eq.symm` by naming the input equality and reusing `Eq.symm`. -/
def tryDecompEqSymm (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``Eq.symm then
      return none

    let some inEq := args.getLast?
      | return none
    let some (_α, _lhs, _rhs) ← inferEqType? inEq
      | return none

    let (eqTactics, used') ← decompileExpr inEq lctx localInsts used
    let (eqName, used'') := chooseIntroName used'.length `hEq used'
    let eqIdent := mkIdent (Name.mkSimple eqName)
    let eqTyStx ← delabToRefinableSyntax (← Meta.inferType inEq)
    let eqTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqTactics]*)
    let letEqTac ← `(tactic| let $eqIdent : $eqTyStx := by $eqTacticSeq)

    let exactTac ← `(tactic| exact $(mkIdent ``Eq.symm) $eqIdent)
    return some (#[letEqTac, exactTac], used'')

/-- Handle `Eq.trans` by normalizing (calcify-style) and emitting a `calc` block. -/
def tryDecompEqTrans (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (_decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``Eq.trans then
      return none
    if args.length < 2 then
      return none

    let exprNorm ← simplifyEqProof expr
    let type ← whnf (← Meta.inferType exprNorm)
    let some (_, lhs, _) := type.eq?
      | return none

    -- After normalization, the expr may no longer be Eq.trans (e.g. collapsed to single step)
    match_expr exprNorm with
    | Eq.refl _ _ => do
      let tac ← `(tactic| rfl)
      return some (#[tac], used)
    | Eq.trans _ _ _ _ _ _ => do
      let stepStx ← getCalcSteps exprNorm #[]
      let calcTac ← `(tactic| calc
            $(← delabToRefinableSyntax lhs):term
            $stepStx*)
      return some (#[calcTac], used)
    | _ => do
      -- Single-step result after normalization; just delaborate it
      let proofStx ← delabToRefinableSyntax exprNorm
      let tac ← `(tactic| exact $proofStx)
      return some (#[tac], used)

/-- Handle `Eq.mp` casts structurally by refining with holes for the transport
  equality and transported proof, then recursively decompiling both sides.
  This avoids raw delab/re-elab of arithmetic certificate terms. -/
def tryDecompEqMp (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``Eq.mp then
      return none

    let mut eqProofArg? : Option Expr := none
    let mut sourceTy? : Option Expr := none
    for a in args do
      let aTy ← Meta.inferType a
      let (tyFn, tyArgs) := peelApps aTy
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
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[eqProofNorm, sourceProofArg] lctx localInsts used decompileExpr
    return some result

end LeanDecomp
