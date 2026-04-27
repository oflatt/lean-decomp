import Lean
import LeanDecomp.CasesOn

namespace LeanDecomp
open Lean Meta

/-- Build `Eq.mpr h True.intro` for `h : src = True`. -/
private def mkMprTrue (src h : Expr) : Expr :=
  mkApp4 (mkConst ``Eq.mpr [Level.zero]) src (mkConst ``True) h (mkConst ``True.intro)

/-- Build `propext (Iff.intro fwd bwd) : lhs = rhs`. -/
private def mkPropextIff (lhs rhs fwd bwd : Expr) : Expr :=
  mkApp3 (mkConst ``propext) lhs rhs
    (mkApp4 (mkConst ``Iff.intro) lhs rhs fwd bwd)

/-- Unfold grind marker wrappers that are just identity functions or proposition casts. -/
def simplifyGrindWrappers (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname == ``Lean.Grind.alreadyNorm then
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
    if args.length >= 1 then
      return some (mkApp (mkConst ``Classical.em []) args[0]!)
    return none
  -- Note: `Lean.Grind.of_eq_eq_true h : a ∧ b ∨ ¬a ∧ ¬b` was previously
  -- rewritten to `Eq.mpr lhs True h True.intro : a = b`. That rewrite is
  -- type-incorrect (different result types) and produces ill-typed proof
  -- terms when this expression sits under `Or.casesOn`. Leave it alone here
  -- so the structural decompiler can recurse via the theorem-app fallback.
  if cname == ``Lean.Grind.of_eq_eq_false then
    if let some h := args.getLast? then
      match (← Meta.inferType h) with
      | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
          if rhs.isConstOf ``False then
            return some (mkApp3 (mkConst ``Eq.mp [Level.zero]) lhs (mkConst ``False) h)
          else
            return none
      | _ => return none
    return none
  return none

/-- Simplify `Lean.Grind.*` theorem-based combinator applications to standard-library
    equivalents (`eq_true`, `eq_false'`, `propext`).  These standard forms are then
    handled by the generic propositional cast simplifier on re-traversal. -/
def simplifyGrindCombinators (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  match cname with
  | ``Lean.Grind.eq_true_of_and_eq_true_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let pair := mkMprTrue (mkApp2 (mkConst ``And) a b) h
    return some (mkApp2 (mkConst ``eq_true) a (mkApp3 (mkConst ``And.left) a b pair))
  | ``Lean.Grind.eq_true_of_and_eq_true_right =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let pair := mkMprTrue (mkApp2 (mkConst ``And) a b) h
    return some (mkApp2 (mkConst ``eq_true) b (mkApp3 (mkConst ``And.right) a b pair))
  | ``Lean.Grind.and_eq_of_eq_true_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let fwd := Expr.lam `h andAB (mkApp3 (mkConst ``And.right) a b (.bvar 0)) .default
    let bwd := Expr.lam `h b (mkApp4 (mkConst ``And.intro) a b (mkMprTrue a h) (.bvar 0)) .default
    return some (mkPropextIff andAB b fwd bwd)
  | ``Lean.Grind.and_eq_of_eq_true_right =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let fwd := Expr.lam `h andAB (mkApp3 (mkConst ``And.left) a b (.bvar 0)) .default
    let bwd := Expr.lam `h a (mkApp4 (mkConst ``And.intro) a b (.bvar 0) (mkMprTrue b h)) .default
    return some (mkPropextIff andAB a fwd bwd)
  | ``Lean.Grind.and_eq_of_eq_false_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h)
      (mkApp3 (mkConst ``And.left) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') andAB (Expr.lam `h andAB body .default))
  | ``Lean.Grind.and_eq_of_eq_false_right =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let andAB := mkApp2 (mkConst ``And) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) b (mkConst ``False) h)
      (mkApp3 (mkConst ``And.right) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') andAB (Expr.lam `h andAB body .default))
  | ``Lean.Grind.eq_false_of_or_eq_false_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) orAB (mkConst ``False) h)
      (mkApp3 (mkConst ``Or.inl) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') a (Expr.lam `h a body .default))
  | ``Lean.Grind.eq_false_of_or_eq_false_right =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    let body := mkApp
      (mkApp3 (mkConst ``Eq.mp [Level.zero]) orAB (mkConst ``False) h)
      (mkApp3 (mkConst ``Or.inr) a b (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') b (Expr.lam `h b body .default))
  | ``Lean.Grind.or_eq_of_eq_true_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    return some (mkApp2 (mkConst ``eq_true) orAB (mkApp3 (mkConst ``Or.inl) a b (mkMprTrue a h)))
  | ``Lean.Grind.or_eq_of_eq_true_right =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    return some (mkApp2 (mkConst ``eq_true) orAB (mkApp3 (mkConst ``Or.inr) a b (mkMprTrue b h)))
  | ``Lean.Grind.or_eq_of_eq_false_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let orAB := mkApp2 (mkConst ``Or) a b
    let leftBr := Expr.lam `h a
      (mkApp2 (mkConst ``False.elim [Level.zero]) b
        (mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h) (.bvar 0))) .default
    let rightBr := Expr.lam `h b (.bvar 0) .default
    let fwd := Expr.lam `h orAB
      (mkAppN (mkConst ``Or.elim) #[a, b, b, .bvar 0, leftBr, rightBr]) .default
    let bwd := Expr.lam `h b (mkApp3 (mkConst ``Or.inr) a b (.bvar 0)) .default
    return some (mkPropextIff orAB b fwd bwd)
  | ``Lean.Grind.or_eq_of_eq_false_right =>
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
  | ``Lean.Grind.eq_false_of_not_eq_true =>
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    return some (mkApp2 (mkConst ``eq_false') a (mkMprTrue (mkApp (mkConst ``Not) a) h))
  | ``Lean.Grind.eq_true_of_not_eq_false =>
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    let notA := mkApp (mkConst ``Not) a
    let mp := mkApp3 (mkConst ``Eq.mp [Level.zero]) notA (mkConst ``False) h
    return some (mkApp2 (mkConst ``eq_true) a (mkApp2 (mkConst ``Classical.byContradiction) a mp))
  | ``Lean.Grind.not_eq_of_eq_true =>
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    let notA := mkApp (mkConst ``Not) a
    let body := mkApp (.bvar 0) (mkMprTrue a h)
    return some (mkApp2 (mkConst ``eq_false') notA (Expr.lam `h notA body .default))
  | ``Lean.Grind.not_eq_of_eq_false =>
    if args.length < 2 then return none
    let a := args[0]!; let h := args[1]!
    let notA := mkApp (mkConst ``Not) a
    return some (mkApp2 (mkConst ``eq_true) notA (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h))
  | ``Lean.Grind.imp_eq_of_eq_false_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    let body := mkApp2 (mkConst ``False.elim [Level.zero]) b
      (mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) a (mkConst ``False) h) (.bvar 0))
    return some (mkApp2 (mkConst ``eq_true) impAB (Expr.lam `h a body .default))
  | ``Lean.Grind.imp_eq_of_eq_true_right =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    return some (mkApp2 (mkConst ``eq_true) impAB (Expr.lam `_ a (mkMprTrue b h) .default))
  | ``Lean.Grind.imp_eq_of_eq_true_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    let fwd := Expr.lam `f impAB (mkApp (.bvar 0) (mkMprTrue a h)) .default
    let bwd := Expr.lam `h b (Expr.lam `_ a (.bvar 1) .default) .default
    return some (mkPropextIff impAB b fwd bwd)
  | ``Lean.Grind.eq_true_of_imp_eq_false =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    let innerBody := mkApp2 (mkConst ``False.elim [Level.zero]) b (mkApp (.bvar 1) (.bvar 0))
    let vacuousF := Expr.lam `h a innerBody .default
    let byContraBody := mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) impAB (mkConst ``False) h) vacuousF
    let notA := mkApp (mkConst ``Not) a
    let lam := Expr.lam `h notA byContraBody .default
    return some (mkApp2 (mkConst ``eq_true) a (mkApp2 (mkConst ``Classical.byContradiction) a lam))
  | ``Lean.Grind.eq_false_of_imp_eq_false =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let impAB := Expr.forallE `_ a b .default
    let constF := Expr.lam `_ a (.bvar 1) .default
    let body := mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) impAB (mkConst ``False) h) constF
    return some (mkApp2 (mkConst ``eq_false') b (Expr.lam `h b body .default))
  | ``Lean.Grind.eq_false_of_imp_eq_true =>
    if args.length < 4 then return none
    let a := args[0]!; let b := args[1]!; let h₁ := args[2]!; let h₂ := args[3]!
    let impAB := Expr.forallE `_ a b .default
    let f := mkMprTrue impAB h₁
    let body := mkApp (mkApp3 (mkConst ``Eq.mp [Level.zero]) b (mkConst ``False) h₂) (mkApp f (.bvar 0))
    return some (mkApp2 (mkConst ``eq_false') a (Expr.lam `h a body .default))
  | ``Lean.Grind.eq_eq_of_eq_true_left =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let prop := mkSort Level.zero
    let eqAB := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) prop a b
    let aVal := mkMprTrue a h
    let fwd := Expr.lam `h eqAB (mkApp4 (mkConst ``Eq.mp [Level.zero]) a b (.bvar 0) aVal) .default
    let iffFwd := Expr.lam `_ a (.bvar 1) .default
    let iffBwd := Expr.lam `_ b aVal .default
    let bwd := Expr.lam `h b
      (mkApp3 (mkConst ``propext) a b (mkApp4 (mkConst ``Iff.intro) a b iffFwd iffBwd)) .default
    return some (mkPropextIff eqAB b fwd bwd)
  | ``Lean.Grind.eq_eq_of_eq_true_right =>
    if args.length < 3 then return none
    let a := args[0]!; let b := args[1]!; let h := args[2]!
    let prop := mkSort Level.zero
    let eqAB := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) prop a b
    let bVal := mkMprTrue b h
    let fwd := Expr.lam `h eqAB (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a b (.bvar 0) bVal) .default
    let iffFwd := Expr.lam `_ a bVal .default
    let iffBwd := Expr.lam `_ b (.bvar 1) .default
    let bwd := Expr.lam `h a
      (mkApp3 (mkConst ``propext) a b (mkApp4 (mkConst ``Iff.intro) a b iffFwd iffBwd)) .default
    return some (mkPropextIff eqAB a fwd bwd)
  | _ => return none

/-- Reduce `Eq.mp (Eq.mp (Lean.Grind.not_eq_prop p q) h) hp` to a direct proof of `¬ q`.
    This preserves the information grind encoded while avoiding nested proposition
    equality transports that are hard for the decompiler to reconstruct. -/
def simplifyGrindNotEqPropNestedCast (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp || args.length != 4 then return none
  let eqProof := args[2]!
  let hp := args[3]!
  let (innerFn, innerArgs) := peelArgs eqProof
  if innerFn.constName? != some ``Eq.mp || innerArgs.length != 4 then return none
  let innerEqProof := innerArgs[2]!
  let hneq := innerArgs[3]!
  let (headFn, headArgs) := peelArgs innerEqProof
  if headFn.constName? != some ``Lean.Grind.not_eq_prop || headArgs.length < 2 then return none
  let p := headArgs[0]!
  let q := headArgs[1]!
  let hpTy ← instantiateMVars (← Meta.inferType hp)
  unless (← Meta.isDefEq hpTy p) do return none
  let resultTy ← instantiateMVars (← Meta.inferType e)
  match resultTy with
  | .app (.const ``Not _) q' =>
      unless (← Meta.isDefEq q' q) do
        return none
  | _ => return none
  let fwd := Expr.lam `_ p (.bvar 1) .default
  let bwd := Expr.lam `_ q hp .default
  let eqpq := mkApp3 (mkConst ``propext) p q (mkApp4 (mkConst ``Iff.intro) p q fwd bwd)
  let body := mkApp hneq eqpq
  return some (Expr.lam `hq q body .default)

/-- Grind-specific propositional casts handled before the generic cast simplifier. -/
def simplifyGrindPropCast (e : Expr) : MetaM (Option Expr) := do
  if let some r ← simplifyGrindNotEqPropNestedCast e then
    return some r
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp && cname != ``Eq.mpr then return none
  if args.length != 4 then return none
  unless fn.isConst do return none
  let isForward := (cname == ``Eq.mp)
  let eqProof := args[2]!
  let evidence := args[3]!
  let (eqFn, eqArgs) := peelArgs eqProof
  let some eqName := eqFn.constName? | return none
  if eqName == ``Lean.Grind.iff_eq then
    if eqArgs.length < 2 then return none
    if isForward then
      return some (mkApp3 (mkConst ``propext) eqArgs[0]! eqArgs[1]! evidence)
    else
      return none
  return none

/-- Reduce `intro_with_eq p p' q he k hp` → `k (Eq.mp he hp)` (or `k hp` when p ≡ p'). -/
def simplifyGrindIntroWithEq (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Lean.Grind.intro_with_eq && cname != ``Lean.Grind.intro_with_eq' then
    return none
  if args.length == 6 then
    let p := args[0]!; let p' := args[1]!; let k := args[4]!; let hp := args[5]!
    let arg ← if (← Meta.withDefault <| Meta.isDefEq p p') then
      pure hp
    else
      let he := args[3]!
      pure (mkApp4 (mkConst ``Eq.mp [Level.zero]) p p' he hp)
    return some (Expr.app k arg).headBeta
  else if args.length == 5 then
    let p := args[0]!; let p' := args[1]!; let k := args[4]!
    let body ← if (← Meta.withDefault <| Meta.isDefEq p p') then
      pure (Expr.lam `hp p (Expr.app (k.liftLooseBVars 0 1) (.bvar 0)) .default)
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

end LeanDecomp
