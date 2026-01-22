import LeanDecomp.ProofTermMacro
import Lean.Elab.GuardMsgs

namespace LeanDecomp.Test

-- Test 1: Simple arithmetic proof
theorem simple_arith : 2 + 2 = 4 :=
  by decide

/--
info: Try this:
  [apply] by
    exact  of_decide_eq_true  id  Eq.refl  true
-/
#guard_msgs in
example : 2 + 2 = 4 := by
  decompile decide

-- Test 2: Simple implication with intro
/--
info: Try this:
  [apply] by
    intros h
    exact  h
-/
#guard_msgs in
example (P : Prop) : P → P := by
  decompile intro h; exact h

-- Test 3: And introduction
/--
info: Try this:
  [apply] by
    exact  ⟨  ha  ,  hb  ⟩
-/
#guard_msgs in
example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  decompile exact ⟨ha, hb⟩

-- Test 4: Modus ponens
/--
info: Try this:
  [apply] by
    exact  h  a
-/
#guard_msgs in
example (P Q : Prop) (h : P → Q) (a : P) : Q := by
  decompile exact h a

-- Test 5: Universal statement
/--
info: Try this:
  [apply] by
    intros n
    exact  Nat.zero_add  n
-/
#guard_msgs in
example : ∀ n : Nat, 0 + n = n := by
  decompile intro n; exact Nat.zero_add n

end LeanDecomp.Test
