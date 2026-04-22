import LeanDecomp.ProofTermMacro
import Lean.Elab.GuardMsgs

namespace LeanDecomp.Test

-- Test 1: Simple arithmetic proof
theorem simple_arith : 2 + 2 = 4 :=
  by decide

/--
info: Try this:
  [apply] decide
-/
#guard_msgs in
example : 2 + 2 = 4 := by
  decompile decide

-- Test 2: Simple implication with intro
/--
info: Try this:
  [apply]
    intro h
    exact h
-/
#guard_msgs (whitespace := lax) in
example (P : Prop) : P → P := by
  decompile intro h; exact h

-- Test 3: And introduction
/--
info: Try this:
  [apply] exact ⟨ha, hb⟩
-/
#guard_msgs in
example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  decompile exact ⟨ha, hb⟩

-- Test 4: Modus ponens
/--
info: Try this:
  [apply] exact h a
-/
#guard_msgs in
example (P Q : Prop) (h : P → Q) (a : P) : Q := by
  decompile exact h a

-- Test 5: Universal statement
/--
info: Try this:
  [apply]
    intro n
    exact Nat.zero_add n
-/
#guard_msgs (whitespace := lax) in
example : ∀ n : Nat, 0 + n = n := by
  decompile intro n; exact Nat.zero_add n

-- Test 6: grind arithmetic contradiction.
-- The decompiler emits the full structural proof term, replacing grind's
-- `eagerReduce (Eq.refl true)` certificate gadgets with holes closed by `rfl`.
/--
info: Try this:
  [apply] refine @Eq.mp (5 ≤ n) False ?_ ?_
    · refine @Lean.Grind.Order.eq_trans_false ((5 : Nat) ≤ n) ((5 : Int) ≤ ↑n) ?_ ?_
      · refine Nat.ToInt.le_eq ?_ ?_
        · exact Nat.ToInt.natCast_ofNat 5
        · rfl
      · refine @Lean.Grind.Order.eq_trans_false ((5 : Int) ≤ ↑n) ((0 : Int) ≤ ↑n + IntCast.intCast (-5 : Int)) ?_ ?_
        · refine
            @Lean.Grind.CommRing.le_norm_expr Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
              (Lean.RArray.leaf ↑n) (Lean.Grind.CommRing.Expr.num 5) (Lean.Grind.CommRing.Expr.var 0)
              (Lean.Grind.CommRing.Expr.num 0)
              ((Lean.Grind.CommRing.Expr.var 0).add (Lean.Grind.CommRing.Expr.intCast (-5))) ?_
          · refine @Std.IsLinearPreorder.toIsPreorder Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
        · refine
            @Lean.Grind.Order.le_eq_false_of_le_k Int Int.instLEInt Int.instLTInt ?_ ?_ Lean.Grind.instCommRingInt.toRing
              ?_ (↑n) 0 3 (-5) ?_ ?_
          · exact Lean.Grind.instLawfulOrderLTInt
          · refine @Std.IsLinearPreorder.toIsPreorder Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
          · refine @Lean.Grind.Order.eq_mp (↑n ≤ (3 : Int)) (↑n ≤ (0 : Int) + IntCast.intCast (3 : Int)) ?_ ?_
            · refine
                @Lean.Grind.CommRing.le_norm_expr Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
                  (Lean.RArray.leaf ↑n) (Lean.Grind.CommRing.Expr.var 0) (Lean.Grind.CommRing.Expr.num 3)
                  (Lean.Grind.CommRing.Expr.var 0)
                  ((Lean.Grind.CommRing.Expr.num 0).add (Lean.Grind.CommRing.Expr.intCast 3)) ?_
              · refine @Std.IsLinearPreorder.toIsPreorder Int Int.instLEInt ?_
                · refine @Std.IsLinearOrder.toIsLinearPreorder Int Int.instLEInt ?_
                  · exact Lean.Grind.instIsLinearOrderInt
              · exact Lean.Grind.instOrderedRingInt
              · decide
            · refine of_eq_true ?_
              · refine @Lean.Grind.Order.eq_trans_true' (n ≤ (3 : Nat)) (↑n ≤ (3 : Int)) ?_ ?_
                · refine Nat.ToInt.le_eq ?_ ?_
                  · rfl
                  · exact Nat.ToInt.natCast_ofNat 3
                · refine eq_true ?_
                  · exact h1
    · exact h2
-/
#guard_msgs (whitespace := lax) in
example (n : Nat) (h1 : n ≤ 3) (h2 : 5 ≤ n) : False := by
  decompile grind

-- Test 7: grind byContradiction + derived have.
/--
info: Try this:
  [apply] apply Classical.byContradiction
    intro hp
    refine @Eq.mp (10 ≤ n) False ?_ ?_
    · refine @Lean.Grind.Order.eq_trans_false ((10 : Nat) ≤ n) ((10 : Int) ≤ ↑n) ?_ ?_
      · refine Nat.ToInt.le_eq ?_ ?_
        · exact Nat.ToInt.natCast_ofNat 10
        · rfl
      · refine @Lean.Grind.Order.eq_trans_false ((10 : Int) ≤ ↑n) ((0 : Int) ≤ ↑n + IntCast.intCast (-10 : Int)) ?_ ?_
        · refine
            @Lean.Grind.CommRing.le_norm_expr Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
              (Lean.RArray.leaf ↑n) (Lean.Grind.CommRing.Expr.num 10) (Lean.Grind.CommRing.Expr.var 0)
              (Lean.Grind.CommRing.Expr.num 0)
              ((Lean.Grind.CommRing.Expr.var 0).add (Lean.Grind.CommRing.Expr.intCast (-10))) ?_
          · refine @Std.IsLinearPreorder.toIsPreorder Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
        · refine
            @Lean.Grind.Order.le_eq_false_of_le_k Int Int.instLEInt Int.instLTInt ?_ ?_ Lean.Grind.instCommRingInt.toRing
              ?_ (↑n) 0 4 (-10) ?_ ?_
          · exact Lean.Grind.instLawfulOrderLTInt
          · refine @Std.IsLinearPreorder.toIsPreorder Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
          · refine @Lean.Grind.Order.eq_mp (↑n ≤ (4 : Int)) (↑n ≤ (0 : Int) + IntCast.intCast (4 : Int)) ?_ ?_
            · refine
                @Lean.Grind.CommRing.le_norm_expr Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
                  (Lean.RArray.leaf ↑n) (Lean.Grind.CommRing.Expr.var 0) (Lean.Grind.CommRing.Expr.num 4)
                  (Lean.Grind.CommRing.Expr.var 0)
                  ((Lean.Grind.CommRing.Expr.num 0).add (Lean.Grind.CommRing.Expr.intCast 4)) ?_
              · refine @Std.IsLinearPreorder.toIsPreorder Int Int.instLEInt ?_
                · refine @Std.IsLinearOrder.toIsLinearPreorder Int Int.instLEInt ?_
                  · exact Lean.Grind.instIsLinearOrderInt
              · exact Lean.Grind.instOrderedRingInt
              · decide
            · refine of_eq_true ?_
              · refine @Lean.Grind.Order.eq_trans_true' (n ≤ (4 : Nat)) (↑n ≤ (4 : Int)) ?_ ?_
                · refine Nat.ToInt.le_eq ?_ ?_
                  · rfl
                  · exact Nat.ToInt.natCast_ofNat 4
                · refine eq_true ?_
                  · refine @Eq.mp (n + 1 ≤ 5) (n ≤ 5 - 1) ?_ ?_
                    · refine Nat.Simproc.add_le_le n ?_
                      · decide
                    · exact h
    · refine @Eq.mp (¬n ≤ 9) (9 + 1 ≤ n) ?_ ?_
      · exact Nat.not_le_eq n 9
      · refine @mt (n ≤ (9 : Nat)) (n < (10 : Nat)) ?_ ?_
        ·
          exact fun b =>
            Eq.symm (Eq.trans (Lean.Grind.Nat.lt_eq n 10) (Nat.Simproc.add_le_le n (of_decide_eq_true (Eq.refl true)))) ▸
              b
        · exact hp
-/
#guard_msgs (whitespace := lax) in
example (n : Nat) (h : n < 5) : n < 10 := by
  decompile grind

-- Test 8: P and ¬P contradiction
/--
info: Try this:
  [apply] contradiction
-/
#guard_msgs in
example (P : Prop) (h : P) (h' : ¬P) : False := by
  decompile exact absurd h h'

-- Test 9: False.elim → cases
/--
info: Try this:
  [apply] cases h
-/
#guard_msgs in
example (h : False) : 1 = 2 := by
  decompile exact h.elim

end LeanDecomp.Test
