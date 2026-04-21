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
    · refine
        @Lean.Grind.Order.eq_trans_false
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n)
          (@LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5)))
            (@NatCast.natCast.{0} Int instNatCastInt n))
          ?_ ?_
      · refine Nat.ToInt.le_eq ?_ ?_
        · exact Nat.ToInt.natCast_ofNat 5
        · exact @Eq.refl.{1} Int (@NatCast.natCast.{0} Int instNatCastInt n)
      · refine
          @Lean.Grind.Order.eq_trans_false
            (@LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5)))
              (@NatCast.natCast.{0} Int instNatCastInt n))
            (@LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@NatCast.natCast.{0} Int instNatCastInt n)
                (@IntCast.intCast.{0} Int instIntCastInt
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5)))))))
            ?_ ?_
        · refine
            @Lean.Grind.CommRing.le_norm_expr.{0} Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
              (@Lean.RArray.leaf.{0} Int (@NatCast.natCast.{0} Int instNatCastInt n))
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))))
              (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (Lean.Grind.CommRing.Expr.add
                (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (Lean.Grind.CommRing.Expr.intCast
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))))))
              ?_
          · refine @Std.IsLinearPreorder.toIsPreorder.{0} Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder.{0} Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
        · refine
            @Lean.Grind.Order.le_eq_false_of_le_k.{0} Int Int.instLEInt Int.instLTInt ?_ ?_
              (@Lean.Grind.CommRing.toRing.{0} Int Lean.Grind.instCommRingInt) ?_
              (@NatCast.natCast.{0} Int instNatCastInt n) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5)))) ?_ ?_
          · exact Lean.Grind.instLawfulOrderLTInt
          · refine @Std.IsLinearPreorder.toIsPreorder.{0} Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder.{0} Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
          · refine
              @Lean.Grind.Order.eq_mp
                (@LE.le.{0} Int Int.instLEInt (@NatCast.natCast.{0} Int instNatCastInt n)
                  (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
                (@LE.le.{0} Int Int.instLEInt (@NatCast.natCast.{0} Int instNatCastInt n)
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@IntCast.intCast.{0} Int instIntCastInt
                      (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))))
                ?_ ?_
            · refine
                @Lean.Grind.CommRing.le_norm_expr.{0} Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
                  (@Lean.RArray.leaf.{0} Int (@NatCast.natCast.{0} Int instNatCastInt n))
                  (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
                  (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Lean.Grind.CommRing.Expr.add
                    (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                    (Lean.Grind.CommRing.Expr.intCast (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
                  ?_
              · refine @Std.IsLinearPreorder.toIsPreorder.{0} Int Int.instLEInt ?_
                · refine @Std.IsLinearOrder.toIsLinearPreorder.{0} Int Int.instLEInt ?_
                  · exact Lean.Grind.instIsLinearOrderInt
              · exact Lean.Grind.instOrderedRingInt
              · decide
            · refine of_eq_true ?_
              · refine
                  @Lean.Grind.Order.eq_trans_true'
                    (@LE.le.{0} Nat instLENat n (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@LE.le.{0} Int Int.instLEInt (@NatCast.natCast.{0} Int instNatCastInt n)
                      (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
                    ?_ ?_
                · refine Nat.ToInt.le_eq ?_ ?_
                  · exact @Eq.refl.{1} Int (@NatCast.natCast.{0} Int instNatCastInt n)
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
    · refine
        @Lean.Grind.Order.eq_trans_false
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) n)
          (@LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10)))
            (@NatCast.natCast.{0} Int instNatCastInt n))
          ?_ ?_
      · refine Nat.ToInt.le_eq ?_ ?_
        · exact Nat.ToInt.natCast_ofNat 10
        · exact @Eq.refl.{1} Int (@NatCast.natCast.{0} Int instNatCastInt n)
      · refine
          @Lean.Grind.Order.eq_trans_false
            (@LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10)))
              (@NatCast.natCast.{0} Int instNatCastInt n))
            (@LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@NatCast.natCast.{0} Int instNatCastInt n)
                (@IntCast.intCast.{0} Int instIntCastInt
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10)))))))
            ?_ ?_
        · refine
            @Lean.Grind.CommRing.le_norm_expr.{0} Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
              (@Lean.RArray.leaf.{0} Int (@NatCast.natCast.{0} Int instNatCastInt n))
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10))))
              (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (Lean.Grind.CommRing.Expr.add
                (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (Lean.Grind.CommRing.Expr.intCast
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10))))))
              ?_
          · refine @Std.IsLinearPreorder.toIsPreorder.{0} Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder.{0} Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
        · refine
            @Lean.Grind.Order.le_eq_false_of_le_k.{0} Int Int.instLEInt Int.instLTInt ?_ ?_
              (@Lean.Grind.CommRing.toRing.{0} Int Lean.Grind.instCommRingInt) ?_
              (@NatCast.natCast.{0} Int instNatCastInt n) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10)))) ?_ ?_
          · exact Lean.Grind.instLawfulOrderLTInt
          · refine @Std.IsLinearPreorder.toIsPreorder.{0} Int Int.instLEInt ?_
            · refine @Std.IsLinearOrder.toIsLinearPreorder.{0} Int Int.instLEInt ?_
              · exact Lean.Grind.instIsLinearOrderInt
          · exact Lean.Grind.instOrderedRingInt
          · decide
          · refine
              @Lean.Grind.Order.eq_mp
                (@LE.le.{0} Int Int.instLEInt (@NatCast.natCast.{0} Int instNatCastInt n)
                  (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
                (@LE.le.{0} Int Int.instLEInt (@NatCast.natCast.{0} Int instNatCastInt n)
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@IntCast.intCast.{0} Int instIntCastInt
                      (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))))
                ?_ ?_
            · refine
                @Lean.Grind.CommRing.le_norm_expr.{0} Int Lean.Grind.instCommRingInt Int.instLEInt Int.instLTInt ?_ ?_
                  (@Lean.RArray.leaf.{0} Int (@NatCast.natCast.{0} Int instNatCastInt n))
                  (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
                  (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Lean.Grind.CommRing.Expr.add
                    (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                    (Lean.Grind.CommRing.Expr.intCast (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))))
                  ?_
              · refine @Std.IsLinearPreorder.toIsPreorder.{0} Int Int.instLEInt ?_
                · refine @Std.IsLinearOrder.toIsLinearPreorder.{0} Int Int.instLEInt ?_
                  · exact Lean.Grind.instIsLinearOrderInt
              · exact Lean.Grind.instOrderedRingInt
              · decide
            · refine of_eq_true ?_
              · refine
                  @Lean.Grind.Order.eq_trans_true'
                    (@LE.le.{0} Nat instLENat n (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@LE.le.{0} Int Int.instLEInt (@NatCast.natCast.{0} Int instNatCastInt n)
                      (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
                    ?_ ?_
                · refine Nat.ToInt.le_eq ?_ ?_
                  · exact @Eq.refl.{1} Int (@NatCast.natCast.{0} Int instNatCastInt n)
                  · exact Nat.ToInt.natCast_ofNat 4
                · refine eq_true ?_
                  · refine @Eq.mp (n + 1 ≤ 5) (n ≤ 5 - 1) ?_ ?_
                    · refine Nat.Simproc.add_le_le n ?_
                      · decide
                    · exact h
    · refine @Eq.mp (¬n ≤ 9) (9 + 1 ≤ n) ?_ ?_
      · exact Nat.not_le_eq n 9
      · refine
          @mt (@LE.le.{0} Nat instLENat n (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
            (@LT.lt.{0} Nat instLTNat n (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) ?_ ?_
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
