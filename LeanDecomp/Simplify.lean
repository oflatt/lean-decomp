import Lean
import LeanDecomp.CasesOn

/-! # Proof term simplification pass

This module provides a recursive simplification pass over proof term `Expr`s
*before* the decompiler converts them to tactic syntax. Each simplification
rewrites a proof term into a simpler, logically equivalent term so that the
decompiler can produce cleaner output.

Note: some simplifications (like contradiction detection in casesOn branches)
require tactic-level context and live in the decompiler instead — the types
only match after `cases` unification.
-/

namespace LeanDecomp
open Lean Meta

-- ═══════════════════════════════════════════════════════
-- Analysis helpers (exported for use by the decompiler)
-- ═══════════════════════════════════════════════════════

/-- Extract a contradiction pair from an `Eq.mp (eq_true/eq_false chain) True.intro`
    proof of `False`. Returns `some (h, h')` where `h : P` and `h' : ¬P`. -/
def extractContradiction (falseProof : Expr) : Option (Expr × Expr) := do
  let (fn, args) := peelArgs falseProof
  let cname ← fn.constName?
  guard (cname == ``Eq.mp)
  guard (args.length == 4)
  let he := args[2]!
  let witness := args[3]!
  let (witFn, _) := peelArgs witness
  let witName ← witFn.constName?
  guard (witName == ``True.intro)
  let mut eqTrueArg : Option Expr := none
  let mut eqFalseArg : Option Expr := none
  let mut worklist := [he]
  while !worklist.isEmpty do
    let e := worklist.head!
    worklist := worklist.tail!
    let (efn, eargs) := peelArgs e
    if let some ename := efn.constName? then
      if ename == ``Eq.trans then
        if eargs.length >= 6 then
          worklist := eargs[4]! :: eargs[5]! :: worklist
      else if ename == ``Eq.symm then
        if eargs.length >= 4 then
          worklist := eargs[3]! :: worklist
      else if ename == ``eq_true then
        if eargs.length >= 2 then
          eqTrueArg := some eargs[1]!
      else if ename == ``eq_false then
        if eargs.length >= 2 then
          eqFalseArg := some eargs[1]!
      else if ename == ``eq_false' then
        if eargs.length >= 2 then
          eqFalseArg := some eargs[1]!
  let h ← eqTrueArg
  let h' ← eqFalseArg
  return (h, h')

-- ═══════════════════════════════════════════════════════
-- Individual simplification rules (Expr → Option Expr)
-- ═══════════════════════════════════════════════════════

/-- Simplify `False.rec/False.elim/False.casesOn (Eq.mp eq_chain True.intro)`
    into `absurd h h'` when the types are definitionally equal. -/
private def simplifyFalseElim (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``False.rec && cname != ``False.elim && cname != ``False.casesOn then
    return none
  let some falseArg := args.findSome? (fun arg =>
    let (afn, _) := peelArgs arg
    if afn.constName? == some ``Eq.mp then some arg else none) | return none
  let some (h, h') := extractContradiction falseArg | return none
  try
    let result ← mkAppM ``absurd #[h, h']
    return some result
  catch _ =>
    return none


/-- Strip `@id T body` → `body`. -/
private def simplifyId (e : Expr) : Option Expr := do
  let .app fn body := e | failure
  let .app idConst _typeArg := fn | failure
  let cname ← idConst.constName?
  guard (cname == ``id)
  return body

/-- Unfold grind marker wrappers that are just identity functions.
    `Lean.Grind.alreadyNorm p` → `p` (it's `def alreadyNorm (p : Prop) : Prop := p`)
    `Lean.Grind.nestedProof p h` → `h` (it's `def nestedProof (p : Prop) {h : p} : p := h`)
    `Lean.Grind.Marker a` → `a` (it's `@[inline] def Marker {α} (a : α) : α := a`)
    `Lean.Grind.em p` → `Classical.em p` (it's `theorem em (p) : alreadyNorm p ∨ alreadyNorm (¬ p) := Classical.em p`) -/
private def simplifyGrindWrappers (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname == ``Lean.Grind.alreadyNorm then
    -- alreadyNorm p := p, so just delta-expand
    let reduced ← Meta.deltaExpand e (· == ``Lean.Grind.alreadyNorm)
    if reduced != e then return some reduced
    return none
  if cname == ``Lean.Grind.nestedProof then
    let reduced ← Meta.deltaExpand e (· == ``Lean.Grind.nestedProof)
    if reduced != e then return some reduced
    return none
  if cname == ``Lean.Grind.Marker then
    let reduced ← Meta.deltaExpand e (· == ``Lean.Grind.Marker)
    if reduced != e then return some reduced
    return none
  if cname == ``Lean.Grind.em then
    -- em p : alreadyNorm p ∨ alreadyNorm (¬ p) := Classical.em p
    -- After unfolding alreadyNorm, this is just Classical.em p
    if args.length >= 1 then
      let p := args[0]!
      return some (mkApp (mkConst ``Classical.em []) p)
    return none
  return none

-- ═══════════════════════════════════════════════════════
-- Grind combinator simplification
-- ═══════════════════════════════════════════════════════

/-- Build `Eq.mpr h True.intro` for `h : src = True`. -/
private def mkMprTrue (src h : Expr) : Expr :=
  mkApp4 (mkConst ``Eq.mpr [Level.zero]) src (mkConst ``True) h (mkConst ``True.intro)

/-- Build `propext (Iff.intro fwd bwd) : lhs = rhs`. -/
private def mkPropextIff (lhs rhs fwd bwd : Expr) : Expr :=
  mkApp3 (mkConst ``propext) lhs rhs
    (mkApp4 (mkConst ``Iff.intro) lhs rhs fwd bwd)

/-- Simplify `Lean.Grind.*` theorem-based combinator applications to standard-library
    equivalents (`eq_true`, `eq_false'`, `propext`).  These standard forms are then
    handled by `simplifyPropCast` on re-traversal. -/
private def simplifyGrindCombinators (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  match cname with
  -- ═══ And ═══
  | ``Lean.Grind.eq_true_of_and_eq_true_left =>
    -- {a b} (h : (a ∧ b) = True) : a = True
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let pair := mkMprTrue (mkApp2 (mkConst ``And) a b) h
    return some (mkApp2 (mkConst ``eq_true) a (mkApp3 (mkConst ``And.left) a b pair))
  | ``Lean.Grind.eq_true_of_and_eq_true_right =>
    -- {a b} (h : (a ∧ b) = True) : b = True
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let pair := mkMprTrue (mkApp2 (mkConst ``And) a b) h
    return some (mkApp2 (mkConst ``eq_true) b (mkApp3 (mkConst ``And.right) a b pair))
  | ``Lean.Grind.and_eq_of_eq_true_left =>
    -- {a b} (h : a = True) : (a ∧ b) = b
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let fwd := Expr.lam `h andAB (mkApp3 (mkConst ``And.right) a b (.bvar 0)) .default
    let bwd := Expr.lam `h b (mkApp4 (mkConst ``And.intro) a b (mkMprTrue a h) (.bvar 0)) .default
    return some (mkPropextIff andAB b fwd bwd)
  | ``Lean.Grind.and_eq_of_eq_true_right =>
    -- {a b} (h : b = True) : (a ∧ b) = a
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let fwd := Expr.lam `h andAB (mkApp3 (mkConst ``And.left) a b (.bvar 0)) .default
    let bwd := Expr.lam `h a (mkApp4 (mkConst ``And.intro) a b (.bvar 0) (mkMprTrue b h)) .default
    return some (mkPropextIff andAB a fwd bwd)
  | ``Lean.Grind.and_eq_of_eq_false_left =>
    -- {a b} (h : a = False) : (a ∧ b) = False
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h)
      (mkApp3 (mkConst ``And.left) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') andAB (Expr.lam `h andAB body .default))
  | ``Lean.Grind.and_eq_of_eq_false_right =>
    -- {a b} (h : b = False) : (a ∧ b) = False
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) b (mkConst ``False) h)
      (mkApp3 (mkConst ``And.right) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') andAB (Expr.lam `h andAB body .default))
  -- ═══ Or ═══
  | ``Lean.Grind.eq_false_of_or_eq_false_left =>
    -- {a b} (h : (a ∨ b) = False) : a = False
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) orAB (mkConst ``False) h)
      (mkApp3 (mkConst ``Or.inl) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') a (Expr.lam `h a body .default))
  | ``Lean.Grind.eq_false_of_or_eq_false_right =>
    -- {a b} (h : (a ∨ b) = False) : b = False
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) orAB (mkConst ``False) h)
      (mkApp3 (mkConst ``Or.inr) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') b (Expr.lam `h b body .default))
  | ``Lean.Grind.or_eq_of_eq_true_left =>
    -- {a b} (h : a = True) : (a ∨ b) = True
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    return some (mkApp2 (mkConst ``eq_true) orAB (mkApp3 (mkConst ``Or.inl) a b (mkMprTrue a h)))
  | ``Lean.Grind.or_eq_of_eq_true_right =>
    -- {a b} (h : b = True) : (a ∨ b) = True
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    return some (mkApp2 (mkConst ``eq_true) orAB (mkApp3 (mkConst ``Or.inr) a b (mkMprTrue b h)))
  | ``Lean.Grind.or_eq_of_eq_false_left =>
    -- {a b} (h : a = False) : (a ∨ b) = b
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    -- fwd: fun hab => Or.elim hab (fun ha => False.elim (Eq.mp h ha)) (fun hb => hb)
    let leftBr := Expr.lam `h a
      (mkApp2 (mkConst ``False.elim [Level.zero]) b
        (mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h) (.bvar 0))) .default
    let rightBr := Expr.lam `h b (.bvar 0) .default
    let fwd := Expr.lam `h orAB
      (mkAppN (mkConst ``Or.elim) #[a, b, b, .bvar 0, leftBr, rightBr]) .default
    let bwd := Expr.lam `h b (mkApp3 (mkConst ``Or.inr) a b (.bvar 0)) .default
    return some (mkPropextIff orAB b fwd bwd)
  | ``Lean.Grind.or_eq_of_eq_false_right =>
    -- {a b} (h : b = False) : (a ∨ b) = a
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    let leftBr := Expr.lam `h a (.bvar 0) .default
    let rightBr := Expr.lam `h b
      (mkApp2 (mkConst ``False.elim [Level.zero]) a
        (mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) b (mkConst ``False) h) (.bvar 0))) .default
    let fwd := Expr.lam `h orAB
      (mkAppN (mkConst ``Or.elim) #[a, b, a, .bvar 0, leftBr, rightBr]) .default
    let bwd := Expr.lam `h a (mkApp3 (mkConst ``Or.inl) a b (.bvar 0)) .default
    return some (mkPropextIff orAB a fwd bwd)
  -- ═══ Not ═══
  | ``Lean.Grind.eq_false_of_not_eq_true =>
    -- {a} (h : (¬a) = True) : a = False
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    -- Eq.mpr h True.intro : ¬a ≡ a → False
    return some (mkApp2 (mkConst ``eq_false') a (mkMprTrue (mkApp (mkConst ``Not) a) h))
  | ``Lean.Grind.eq_true_of_not_eq_false =>
    -- {a} (h : (¬a) = False) : a = True
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    let notA := mkApp (mkConst ``Not) a
    -- Eq.mp h : ¬a → False;  byContradiction (Eq.mp h) : a
    let mp := mkApp3 (mkConst ``Eq.mp [Level.zero]) notA (mkConst ``False) h
    return some (mkApp2 (mkConst ``eq_true) a (mkApp2 (mkConst ``Classical.byContradiction) a mp))
  | ``Lean.Grind.not_eq_of_eq_true =>
    -- {a} (h : a = True) : (¬a) = False
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    let notA := mkApp (mkConst ``Not) a
    -- fun hna : ¬a => hna (Eq.mpr h True.intro)
    let body := mkApp (.bvar 0) (mkMprTrue a h)
    return some (mkApp2 (mkConst ``eq_false') notA (Expr.lam `h notA body .default))
  | ``Lean.Grind.not_eq_of_eq_false =>
    -- {a} (h : a = False) : (¬a) = True
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    let notA := mkApp (mkConst ``Not) a
    -- Eq.mp h : a → False ≡ ¬a
    return some (mkApp2 (mkConst ``eq_true) notA (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h))
  -- ═══ Implies ═══
  | ``Lean.Grind.imp_eq_of_eq_false_left =>
    -- {a b} (h : a = False) : (a → b) = True
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    -- fun ha : a => False.elim (Eq.mp h ha)
    let body := mkApp2 (mkConst ``False.elim [Level.zero]) b
      (mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h) (.bvar 0))
    return some (mkApp2 (mkConst ``eq_true) impAB (Expr.lam `h a body .default))
  | ``Lean.Grind.imp_eq_of_eq_true_right =>
    -- {a b} (h : b = True) : (a → b) = True
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    return some (mkApp2 (mkConst ``eq_true) impAB (Expr.lam `_ a (mkMprTrue b h) .default))
  | ``Lean.Grind.imp_eq_of_eq_true_left =>
    -- {a b} (h : a = True) : (a → b) = b
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    let fwd := Expr.lam `f impAB (mkApp (.bvar 0) (mkMprTrue a h)) .default
    -- bwd: fun hb : b => fun _ : a => hb  (de Bruijn: bvar 1 = hb)
    let bwd := Expr.lam `h b (Expr.lam `_ a (.bvar 1) .default) .default
    return some (mkPropextIff impAB b fwd bwd)
  | ``Lean.Grind.eq_true_of_imp_eq_false =>
    -- {a b} (h : (a → b) = False) : a = True
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    -- byContradiction (fun hna : ¬a => Eq.mp h (fun ha : a => False.elim (hna ha)))
    -- inner: fun ha : a => False.elim b (bvar 1 bvar 0)  [bvar 1=hna, bvar 0=ha]
    let innerBody := mkApp2 (mkConst ``False.elim [Level.zero]) b (mkApp (.bvar 1) (.bvar 0))
    let vacuousF := Expr.lam `h a innerBody .default
    let byContraBody := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) impAB (mkConst ``False) h)
      vacuousF
    let notA := mkApp (mkConst ``Not) a
    let lam := Expr.lam `h notA byContraBody .default
    return some (mkApp2 (mkConst ``eq_true) a (mkApp2 (mkConst ``Classical.byContradiction) a lam))
  | ``Lean.Grind.eq_false_of_imp_eq_false =>
    -- {a b} (h : (a → b) = False) : b = False
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    -- fun hb : b => Eq.mp h (fun _ : a => hb)  [inner bvar 1=hb]
    let constF := Expr.lam `_ a (.bvar 1) .default
    let body := mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) impAB (mkConst ``False) h) constF
    return some (mkApp2 (mkConst ``eq_false') b (Expr.lam `h b body .default))
  | ``Lean.Grind.eq_false_of_imp_eq_true =>
    -- {a b} (h₁ : (a → b) = True) (h₂ : b = False) : a = False
    if args.length < 4 then return none
    let a := args[0]!; let b := args[1]!; let h₁ := args[2]!; let h₂ := args[3]!
    let impAB := Expr.forallE `_ a b .default
    -- fun ha : a => Eq.mp h₂ ((Eq.mpr h₁ True.intro) ha)
    let f := mkMprTrue impAB h₁
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) b (mkConst ``False) h₂)
      (mkApp f (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') a (Expr.lam `h a body .default))
  -- ═══ Prop Eq ═══
  | ``Lean.Grind.eq_eq_of_eq_true_left =>
    -- {a b : Prop} (h : a = True) : (a = b) = b
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let prop := mkSort Level.zero
    let eqAB := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) prop a b
    let aVal := mkMprTrue a h
    -- fwd: fun hab : a = b => Eq.mp hab aVal
    let fwd := Expr.lam `h eqAB
      (mkApp4 (mkConst ``Eq.mp [Level.zero]) a b (.bvar 0) aVal) .default
    -- bwd: fun hb : b => propext ⟨fun _ : a => hb, fun _ : b => aVal⟩
    let iffFwd := Expr.lam `_ a (.bvar 1) .default  -- bvar 1 = hb
    let iffBwd := Expr.lam `_ b aVal .default
    let bwd := Expr.lam `h b
      (mkApp3 (mkConst ``propext) a b (mkApp4 (mkConst ``Iff.intro) a b iffFwd iffBwd)) .default
    return some (mkPropextIff eqAB b fwd bwd)
  | ``Lean.Grind.eq_eq_of_eq_true_right =>
    -- {a b : Prop} (h : b = True) : (a = b) = a
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let prop := mkSort Level.zero
    let eqAB := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) prop a b
    let bVal := mkMprTrue b h
    -- fwd: fun hab : a = b => Eq.mpr hab bVal
    let fwd := Expr.lam `h eqAB
      (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a b (.bvar 0) bVal) .default
    -- bwd: fun ha : a => propext ⟨fun _ : a => bVal, fun _ : b => ha⟩
    let iffFwd := Expr.lam `_ a bVal .default
    let iffBwd := Expr.lam `_ b (.bvar 1) .default  -- bvar 1 = ha
    let bwd := Expr.lam `h a
      (mkApp3 (mkConst ``propext) a b (mkApp4 (mkConst ``Iff.intro) a b iffFwd iffBwd)) .default
    return some (mkPropextIff eqAB a fwd bwd)
  | _ => return none

/-- Reduce `intro_with_eq p p' q he k hp` → `k (Eq.mp he hp)` (or `k hp` when p ≡ p'). -/
private def simplifyIntroWithEq (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Lean.Grind.intro_with_eq && cname != ``Lean.Grind.intro_with_eq' then
    return none
  if args.length == 6 then
    -- Fully applied: intro_with_eq p p' q he k hp
    let p := args[0]!; let p' := args[1]!; let k := args[4]!; let hp := args[5]!
    let arg ← if (← Meta.withDefault <| Meta.isDefEq p p') then
      pure hp
    else
      let he := args[3]!
      pure (mkApp4 (mkConst ``Eq.mp [Level.zero]) p p' he hp)
    return some (Expr.app k arg).headBeta
  else if args.length == 5 then
    -- Partially applied: returns p → q, construct lambda
    let p := args[0]!; let p' := args[1]!; let k := args[4]!
    let body ← if (← Meta.withDefault <| Meta.isDefEq p p') then
      pure (Expr.lam `hp p
        (Expr.app (k.liftLooseBVars 0 1) (.bvar 0))
        .default)
    else
      let he := args[3]!
      pure (Expr.lam `hp p
        (Expr.app (k.liftLooseBVars 0 1)
          (mkApp4 (mkConst ``Eq.mp [Level.zero])
            (p.liftLooseBVars 0 1) (p'.liftLooseBVars 0 1)
            (he.liftLooseBVars 0 1) (.bvar 0)))
        .default)
    return some body
  return none

/-- Reduce `*.noConfusion` applications via whnf. -/
private def simplifyNoConfusion (e : Expr) : MetaM (Option Expr) := do
  let (fn, _) := peelArgs e
  let some cname := fn.constName? | return none
  if !cname.toString.endsWith ".noConfusion" then return none
  let reduced ← Meta.whnf e
  if reduced != e then return some reduced
  return none

/-- Reduce `Eq.ndrec`/`Eq.rec` applications where the eq proof computes to `Eq.refl`.
    This handles the common pattern from generalized equation motives in casesOn:
    `Eq.ndrec motive base (Eq.symm (Eq.refl a)) (Eq.refl a)` reduces to `base (Eq.refl a)`.
    We use whnf to perform the reduction. -/
private def simplifyEqRec (e : Expr) : MetaM (Option Expr) := do
  let (fn, _) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.ndrec && cname != ``Eq.rec && cname != ``Eq.mpr then return none
  let reduced ← Meta.whnf e
  if reduced != e then return some reduced
  return none

/-- Collapse `Eq.mp (Eq.refl _) body → body` (identity transport).
    This is common in grind proofs where normalization produces
    `Eq.mp (Eq.refl T) x` which is just `x`. -/
private def simplifyEqMpRefl (e : Expr) : Option Expr := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | failure
  guard (cname == ``Eq.mp || cname == ``Eq.mpr)
  guard (args.length == 4)
  let eqProof := args[2]!
  let body := args[3]!
  let (eqFn, _) := peelArgs eqProof
  let some eqName := eqFn.constName? | failure
  guard (eqName == ``Eq.refl)
  return body

-- ═══════════════════════════════════════════════════════
-- Propositional cast simplification (congr-chain interpreter)
-- ═══════════════════════════════════════════════════════

/-- Handle `Eq.mp (congrArg f h) evidence` for known Prop connectives.
    f : Prop → Prop, h : a₁ = a₂, evidence : f a₁ → result : f a₂ -/
private def simplifyCongrArgTransport (a₁ a₂ f h evidence : Expr)
    : MetaM (Option Expr) := do
  -- f is a lambda: fun x => body
  if let .lam _ _ body _ := f then
    if !body.hasLooseBVars then return some evidence  -- constant function
    if body == .bvar 0 then  -- identity
      return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h evidence)
    let (bodyFn, bodyArgs) := peelArgs body
    -- fun x => x ∧ Q  (And on left)
    if bodyFn.isConstOf ``And && bodyArgs.length == 2
        && bodyArgs[0]! == .bvar 0 && !bodyArgs[1]!.hasLooseBVars then
      let Q := bodyArgs[1]!
      let left := mkApp3 (mkConst ``And.left) a₁ Q evidence
      let right := mkApp3 (mkConst ``And.right) a₁ Q evidence
      let newLeft := mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h left
      return some (mkApp4 (mkConst ``And.intro) a₂ Q newLeft right)
    -- fun x => P ∧ x  (And on right)
    if bodyFn.isConstOf ``And && bodyArgs.length == 2
        && bodyArgs[1]! == .bvar 0 && !bodyArgs[0]!.hasLooseBVars then
      let P := bodyArgs[0]!
      let left := mkApp3 (mkConst ``And.left) P a₁ evidence
      let right := mkApp3 (mkConst ``And.right) P a₁ evidence
      let newRight := mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h right
      return some (mkApp4 (mkConst ``And.intro) P a₂ left newRight)
    -- fun x => ¬x  (Not)
    if bodyFn.isConstOf ``Not && bodyArgs.length == 1
        && bodyArgs[0]! == .bvar 0 then
      let mprFn := mkApp3 (mkConst ``Eq.mpr [Level.zero]) a₁ a₂ h
      return some (mkApp4 (mkConst ``mt) a₂ a₁ mprFn evidence)
    return none
  -- f = Not (not a lambda, bare constant)
  if f.isConstOf ``Not then
    let mprFn := mkApp3 (mkConst ``Eq.mpr [Level.zero]) a₁ a₂ h
    return some (mkApp4 (mkConst ``mt) a₂ a₁ mprFn evidence)
  -- f = And P (partially applied)
  let fHead := f.getAppFn
  let fArgs := f.getAppArgs
  if fHead.isConstOf ``And && fArgs.size == 1 then
    let P := fArgs[0]!
    let left := mkApp3 (mkConst ``And.left) P a₁ evidence
    let right := mkApp3 (mkConst ``And.right) P a₁ evidence
    let newRight := mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h right
    return some (mkApp4 (mkConst ``And.intro) P a₂ left newRight)
  return none

/-- Simplify propositional casts: `Eq.mp`/`Eq.mpr` with propext, Eq.trans, congr chains.
    Converts grind's equality-based propositional transport into Iff-based operations.
    Inspired by lean-calcify's approach of flattening congruence chains. -/
private def simplifyPropCast (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp && cname != ``Eq.mpr then return none
  if args.length != 4 then return none
  unless fn.isConst do return none
  let levels := fn.constLevels!
  let isForward := (cname == ``Eq.mp)
  let eqProof := args[2]!
  let evidence := args[3]!
  let (eqFn, eqArgs) := peelArgs eqProof
  let some eqName := eqFn.constName? | return none
  -- Handle Eq.mp.{1} (iff_eq p q) iff_proof → propext iff_proof
  -- iff_eq : (p ↔ q) = (p = q) at Sort 1 level
  if eqName == ``Lean.Grind.iff_eq then
    if eqArgs.length < 2 then return none
    if isForward then
      return some (mkApp3 (mkConst ``propext) eqArgs[0]! eqArgs[1]! evidence)
    else return none
  -- All remaining cases require Prop-level transport (u = 0)
  match levels with
  | [Level.zero] => pure ()
  | _ => return none
  match eqName with
  | ``propext =>
    if eqArgs.length < 3 then return none
    let iff := eqArgs[2]!
    if isForward
    then return some (mkApp4 (mkConst ``Iff.mp) eqArgs[0]! eqArgs[1]! iff evidence)
    else return some (mkApp4 (mkConst ``Iff.mpr) eqArgs[0]! eqArgs[1]! iff evidence)
  | ``Eq.trans =>
    if eqArgs.length < 6 then return none
    -- args of @Eq.trans.{u} {α} {a b c} h₁ h₂: [α, a, b, c, h₁, h₂]
    let a := eqArgs[1]!; let b := eqArgs[2]!; let c := eqArgs[3]!
    let eq1 := eqArgs[4]!; let eq2 := eqArgs[5]!
    if isForward then
      let inner := mkApp4 (mkConst ``Eq.mp [Level.zero]) a b eq1 evidence
      return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) b c eq2 inner)
    else
      let inner := mkApp4 (mkConst ``Eq.mpr [Level.zero]) b c eq2 evidence
      return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a b eq1 inner)
  | ``Eq.symm =>
    if eqArgs.length < 4 then return none
    -- @Eq.symm.{u} {α} {a b} h: [α, a, b, h]
    let a := eqArgs[1]!; let b := eqArgs[2]!; let h := eqArgs[3]!
    if isForward
    then return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a b h evidence)
    else return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) a b h evidence)
  | ``eq_true =>
    if eqArgs.length < 2 then return none
    if isForward then return some (mkConst ``True.intro)
    else return some eqArgs[1]!
  | ``eq_false | ``eq_false' =>
    if eqArgs.length < 2 then return none
    if isForward then return some (mkApp eqArgs[1]! evidence)
    else return some (mkApp2 (mkConst ``False.elim [Level.zero]) args[0]! evidence)
  | ``congr =>
    -- @congr.{u,v} {α β} {f₁ f₂} {a₁ a₂} h₁ h₂: [α, β, f₁, f₂, a₁, a₂, h₁, h₂]
    if eqArgs.length < 8 then return none
    if !isForward then return none
    let f₂ := eqArgs[3]!; let a₁ := eqArgs[4]!
    let h₁ := eqArgs[6]!; let h₂ := eqArgs[7]!
    -- Decompose: Eq.mp (congr h₁ h₂) e
    --   → Eq.mp (congrArg f₂ h₂) (Eq.mp (congrFun' h₁ a₁) e)
    let levels := eqFn.constLevels!
    -- @congrFun'.{u,v} {α β f g} h a — same universe params as congr
    let step1 := mkAppN (mkConst ``congrFun' levels)
      #[eqArgs[0]!, eqArgs[1]!, eqArgs[2]!, eqArgs[3]!, h₁, a₁]
    -- @congrArg.{u,v} {α β a₁ a₂} f h
    let step2 := mkAppN (mkConst ``congrArg levels)
      #[eqArgs[0]!, eqArgs[1]!, eqArgs[4]!, eqArgs[5]!, f₂, h₂]
    let midType := mkApp f₂ a₁
    let inner := mkApp4 (mkConst ``Eq.mp [Level.zero]) args[0]! midType step1 evidence
    return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) midType args[1]! step2 inner)
  | ``congrArg =>
    -- @congrArg.{u,v} {α β} {a₁ a₂} f h: [α, β, a₁, a₂, f, h]
    if eqArgs.length < 6 then return none
    if !isForward then return none
    simplifyCongrArgTransport eqArgs[2]! eqArgs[3]! eqArgs[4]! eqArgs[5]! evidence
  | ``congrFun' | ``congrFun =>
    -- @congrFun'.{u,v} {α β} {f g} h a: [α, β, f, g, h, a]
    if eqArgs.length < 6 then return none
    if !isForward then return none
    let h := eqArgs[4]!; let a := eqArgs[5]!
    -- If h = congrArg bigF innerEq, convert congrFun'(congrArg bigF innerEq, a)
    --   to congrArg (fun x => bigF x a) innerEq
    let (hFn, hArgs) := peelArgs h
    if hFn.constName? == some ``congrArg && hArgs.length >= 6 then
      let innerA₁ := hArgs[2]!; let innerA₂ := hArgs[3]!
      let bigF := hArgs[4]!; let innerEq := hArgs[5]!
      -- Handle And specifically: congrFun' (congrArg And innerEq) a → congrArg (fun x => x ∧ a) innerEq
      if bigF.isConstOf ``And then
        let prop := mkSort Level.zero  -- Prop
        let newF := Expr.lam `x prop
          (mkApp2 (mkConst ``And) (.bvar 0) (a.liftLooseBVars 0 1)) .default
        -- @congrArg.{1,1} Prop Prop a₁ a₂ newF innerEq (Prop : Sort 1)
        let one := Level.succ Level.zero
        let newEqProof := mkAppN (mkConst ``congrArg [one, one])
          #[prop, prop, innerA₁, innerA₂, newF, innerEq]
        let srcType := mkApp2 (mkConst ``And) innerA₁ a
        let dstType := mkApp2 (mkConst ``And) innerA₂ a
        return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) srcType dstType newEqProof evidence)
    return none
  | _ => return none

-- ═══════════════════════════════════════════════════════
-- Main traversal
-- ═══════════════════════════════════════════════════════

/-- Pre-step: cheap pure rewrites applied before recursing into children.
    Returns `.visit` to re-traverse after rewriting, `.continue` to recurse normally. -/
private def simplifyPre (e : Expr) : MetaM TransformStep := do
  -- Beta reduction (all beta redexes, not just fvar args)
  if e.isHeadBetaTarget then return .visit e.headBeta
  -- Strip `@id T body`
  if let some r := simplifyId e then return .visit r
  -- Collapse Eq.mp/Eq.mpr (Eq.refl _) body → body
  if let some r := simplifyEqMpRefl e then return .visit r
  -- Simplify propositional casts (propext/congr chains → Iff operations)
  if let some r ← simplifyPropCast e then return .visit r
  return .continue

/-- Post-step: MetaM rewrites applied after children are simplified.
    Returns `.visit` to re-traverse after rewriting, `.done` to keep as-is. -/
private def simplifyPost (e : Expr) : MetaM TransformStep := do
  -- Convert grind theorem-based combinators to standard eq_true/eq_false/propext forms.
  if let some r ← simplifyGrindCombinators e then return .visit r
  -- Re-check propositional casts: child simplification may have revealed
  -- handleable eq proof heads (e.g. iff_eq → propext in children).
  if let some r ← simplifyPropCast e then return .visit r
  if let some r ← simplifyGrindWrappers e then return .visit r
  if let some r ← simplifyIntroWithEq e then return .visit r
  if let some r ← simplifyNoConfusion e then return .visit r
  if let some r ← simplifyEqRec e then return .visit r
  if let some r ← simplifyFalseElim e then return .visit r
  return .done e

/-- Recursively simplify a proof term bottom-up using `Meta.transform`.
    Uses `withLocalDecl` internally (not `lambdaTelescope`) so definitions
    like `intro_with_eq` are not unfolded during binder opening. -/
def simplifyProofTerm (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := simplifyPre) (post := simplifyPost)

end LeanDecomp
