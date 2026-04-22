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
  [apply] intro n
    lia
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
    · lia
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
    · lia
    · refine @Eq.mp (¬n ≤ 9) (9 + 1 ≤ n) ?_ ?_
      · lia
      · lia
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

-- Test 10: arithmetic hypotheses prefer exact over arithmetic terminal passes.
/--
info: Try this:
  [apply] exact h
-/
#guard_msgs in
example (n : Nat) (h : 5 ≤ n) : 5 ≤ n := by
  decompile exact h

-- Test 11: bare False hypotheses prefer exact before contradiction/cases.
/--
info: Try this:
  [apply] exact h
-/
#guard_msgs in
example (h : False) : False := by
  decompile exact h

end LeanDecomp.Test
