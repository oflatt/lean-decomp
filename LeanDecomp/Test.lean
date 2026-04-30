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

-- Test 6: grind arithmetic contradiction. Closes via single `lia` once the
-- byContradiction body's grind certificate is collapsed by `tryDecompFalseFromLia`.
/--
info: Try this:
  [apply] lia
-/
#guard_msgs (whitespace := lax) in
example (n : Nat) (h1 : n ≤ 3) (h2 : 5 ≤ n) : False := by
  decompile grind

-- Test 7: grind byContradiction + derived have. Closes via `lia` after intro.
/--
info: Try this:
  [apply] apply Classical.byContradiction
    intro hp
    lia
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

-- Test 12: nested `not_eq_prop` casts simplify to a direct proof of `¬ Q`.
/--
info: Try this:
  [apply] intro hq
    apply h
    · apply propext
      · constructor
        · intro x1
          exact hq
        · intro x1_1
          exact hp
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (h : ¬ (P = Q)) (hp : P) : ¬ Q := by
  decompile exact (Eq.mp (Eq.mp (Lean.Grind.not_eq_prop P Q) h) hp)

-- Test 13: recurse into `mt` implication proofs instead of embedding them raw.
/--
info: Try this:
  [apply] apply mt
    · exact hPQ
    · exact hnQ
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (hPQ : P → Q) (hnQ : ¬ Q) : ¬ P := by
  decompile exact mt hPQ hnQ

-- Test 14: `Eq.mp (propext (Iff.intro f g)) ev` collapses to `f ev` (forward
-- direction).  This is the core simplifier-side reduction
-- (`simplifyPropCast` → `simplifyProjOfIntro`) that grind's polynomial
-- normalization chains rely on — keep it locked down so a regression in
-- those simplifier rules surfaces here, not as a Sum/Int nightly timeout.
set_option linter.unusedVariables false in
/--
info: Try this:
  [apply] exact f hp
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (f : P → Q) (g : Q → P) (hp : P) : Q := by
  decompile exact (Eq.mp (propext (Iff.intro f g)) hp)

-- Test 15: `Eq.mp (Eq.symm (propext (Iff.intro f g))) ev` collapses to `g ev`
-- (backward direction via Eq.symm wrap).  Same simplifier path as Test 14
-- but exercising the `Eq.symm` peel in `simplifyPropCast`.
set_option linter.unusedVariables false in
/--
info: Try this:
  [apply] exact g hq
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (f : P → Q) (g : Q → P) (hq : Q) : P := by
  decompile exact (Eq.mp (Eq.symm (propext (Iff.intro f g))) hq)

-- Test 16: `Eq.mp (forall_congr h_eq) h_uni a` — `tryDecompEqMpForallCongr`
-- instantiated case (one trailing application).  Locks in the L70 fix:
-- regressing this handler is what caused Sum L70 to time out at 200k
-- heartbeats before the peeler landed.  The `have` step puts the user-form
-- hypothesis in the lctx so downstream `lia` (in real grind output) can
-- close — here there's no arithmetic so we fall through to the structural
-- `refine @Eq.mp` recursion.
set_option linter.unusedVariables false in
/--
info: Try this:
  [apply] have h := h_uni a
    refine @Eq.mp (P a) (Q a) ?_ ?_
    · exact h_eq a
    · exact h
-/
#guard_msgs (whitespace := lax) in
example (P Q : Nat → Prop) (h_eq : ∀ x, P x = Q x) (h_uni : ∀ x, P x) (a : Nat) : Q a := by
  decompile exact Eq.mp (forall_congr h_eq) h_uni a

-- Test 18: `Eq.mp (forall_congr (fun x => h_eq x)) h_uni` —
-- `tryDecompEqMpForallCongr` universal case (no trailing args).  The handler
-- uses `lambdaTelescope` to peel the binder, which only fires when the body
-- is a literal lambda — real grind output always has a non-trivial lambda
-- body so this is the realistic shape.
set_option linter.unusedVariables false in
/--
info: Try this:
  [apply] intro x
    have h := h_uni x
    refine @Eq.mp (P x) (Q x) ?_ ?_
    · exact h_eq x
    · exact h
-/
#guard_msgs (whitespace := lax) in
example (P Q : Nat → Prop) (h_eq : ∀ x, P x = Q x) (h_uni : ∀ x, P x) : ∀ x, Q x := by
  decompile exact Eq.mp (forall_congr (fun x => h_eq x)) h_uni

-- Test 17: `Eq.mp (implies_congr Eq.refl q_eq) h_imp hp` —
-- `tryDecompEqMpImpliesCongr` premise-applied case.  The `Eq.refl` premise
-- is a hard requirement of the handler (the `p_eq ≠ Eq.refl` case is
-- deferred — see EqDecomp.lean docstring).  Closes via the handler's `lia`
-- fast path: `grind`'s congruence closure derives `Q` from `h : R` and the
-- ambient `h_eq : R = Q` without needing the structural `refine` wiring.
set_option linter.unusedVariables false in
/--
info: Try this:
  [apply] have h := h_imp hp
    lia
-/
#guard_msgs (whitespace := lax) in
example (P R Q : Prop) (h_eq : R = Q) (h_imp : P → R) (hp : P) : Q := by
  decompile exact Eq.mp (implies_congr (Eq.refl P) h_eq) h_imp hp

end LeanDecomp.Test
