import LeanDecomp.ProofTermMacro
import Lean.Elab.GuardMsgs

/-!
# Decompiler regression tests

Snapshot tests organized by handler.  Each section locks down the output for
one structural/specialized handler so a regression surfaces here rather than
as a nightly timeout on Sum.lean / Int.lean.  When a test fails, prefer
re-reading the relevant handler docstring before "fixing" the snapshot —
the snapshot exists because the previous output was load-bearing.

Sections:
- §1 Smoke tests: `decide`, `intro`, `And.intro`, modus ponens, basic universal.
- §2 byContradiction + arithmetic terminal (`tryDecompFalseFromLia`).
- §3 Hypothesis preferences (`tryDecompExactLocalHyp`).
- §4 Specialized grind handlers (`mt`, `not_eq_prop`).
- §5 propext / Iff.intro simplifier reductions (`simplifyProjOfIntro` /
    `simplifyPropCast`).  Regression-locks for the L70/L36 simplifier fixes.
- §6 forall_congr / implies_congr peelers (`tryDecompEqMpForallCongr`,
    `tryDecompEqMpImpliesCongr`).  Regression-locks for the L70/L36 peeler
    fixes.
- §7 Inaccessible-name sanitizer (`sanitizeInaccessibleIdents`).
- §8 Structural-handler smoke tests (`tryDecompAndProj`, `tryDecompEqSymm`,
    `tryDecompIffMpMpr`, `tryDecompEqRefl`, `tryDecompEagerReduce`,
    `tryDecompTheoremAppFallback`).  These handlers run rarely in real
    grind output but fire deep in dispatch — without coverage, a
    refactor can silently break them and only surface as a regression
    in a downstream simplifier chain.
-/

namespace LeanDecomp.Test

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §1  Smoke tests                                                      ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Test 1: Simple arithmetic proof (`tryDecompDecide`).
theorem simple_arith : 2 + 2 = 4 :=
  by decide

/--
info: Try this:
  [apply] decide
-/
#guard_msgs in
example : 2 + 2 = 4 := by
  decompile decide

-- Test 2: Simple implication with intro (`tryDecompIntro`).
/--
info: Try this:
  [apply]
    intro h
    exact h
-/
#guard_msgs (whitespace := lax) in
example (P : Prop) : P → P := by
  decompile intro h; exact h

-- Test 3: And introduction (theorem-app fallback emits anonymous constructor).
/--
info: Try this:
  [apply] exact ⟨ha, hb⟩
-/
#guard_msgs in
example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  decompile exact ⟨ha, hb⟩

-- Test 4: Modus ponens (theorem-app fallback).  fvar head, 1 proof arg.
-- TheoremAppFallback's `if !problematic && proofArgs.size < 2 then return none`
-- gate refuses to fire for trivial single-arg apps, so this falls through to
-- `decompExact` and emits `exact h a` rather than `apply h; · exact a`.
/--
info: Try this:
  [apply] exact h a
-/
#guard_msgs in
example (P Q : Prop) (h : P → Q) (a : P) : Q := by
  decompile exact h a

-- Test 4b: fvar head, 2 proof args.  Goes through `tryDecompTheoremAppFallback`
-- (TheoremAppFallback's `proofArgs.size >= 2` branch fires).  All args are
-- proof-like, so the all-args-proof-like branch emits `apply h` rather than
-- `refine h ?_ ?_` — same subgoals, cleaner output.  Regression-locks the
-- fvar-app path that `tryDecompProblematicProofApp` was originally Phase 1
-- of dispatch for; after the Problematic/TheoremApp collapse, this is the
-- canonical path.
/--
info: Try this:
  [apply] apply h
    · exact a
    · exact b
-/
#guard_msgs (whitespace := lax) in
example (P Q R : Prop) (h : P → Q → R) (a : P) (b : Q) : R := by
  decompile exact h a b

-- Test 5: Universal statement (`tryDecompIntro` + arithmetic terminal).
/--
info: Try this:
  [apply] intro n
    lia
-/
#guard_msgs (whitespace := lax) in
example : ∀ n : Nat, 0 + n = n := by
  decompile intro n; exact Nat.zero_add n

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §2  byContradiction + arithmetic terminal                            ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Test 6: grind arithmetic contradiction.  Closes via single `lia` once the
-- byContradiction body's grind certificate is collapsed by
-- `tryDecompFalseFromLia`.
/--
info: Try this:
  [apply] lia
-/
#guard_msgs (whitespace := lax) in
example (n : Nat) (h1 : n ≤ 3) (h2 : 5 ≤ n) : False := by
  decompile grind

-- Test 7: grind byContradiction + derived `have`.  Closes via `lia` after
-- intro of the negation hypothesis.
/--
info: Try this:
  [apply] apply Classical.byContradiction
    intro hp
    lia
-/
#guard_msgs (whitespace := lax) in
example (n : Nat) (h : n < 5) : n < 10 := by
  decompile grind

-- Test 8: P and ¬P contradiction (`tryDecompFalseFromLia` falls through to
-- `contradiction` via the `tryDecompArithmeticTerminalPasses` chain).
/--
info: Try this:
  [apply] contradiction
-/
#guard_msgs in
example (P : Prop) (h : P) (h' : ¬P) : False := by
  decompile exact absurd h h'

-- Test 9: False.elim → cases (`tryDecompCasesOn` on the `False` discriminant).
/--
info: Try this:
  [apply] cases h
-/
#guard_msgs in
example (h : False) : 1 = 2 := by
  decompile exact h.elim

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §3  Hypothesis preferences                                           ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Test 10: arithmetic hypotheses prefer `exact` over arithmetic terminal
-- passes.  `tryDecompExactLocalHyp` runs in Phase 1 of dispatch, before
-- the specialized handlers that would emit `lia`.
/--
info: Try this:
  [apply] exact h
-/
#guard_msgs in
example (n : Nat) (h : 5 ≤ n) : 5 ≤ n := by
  decompile exact h

-- Test 11: bare False hypotheses prefer `exact` before contradiction/cases —
-- same Phase 1 priority as Test 10.
/--
info: Try this:
  [apply] exact h
-/
#guard_msgs in
example (h : False) : False := by
  decompile exact h

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §4  Specialized grind handlers                                       ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Test 12: nested `not_eq_prop` casts simplify to a direct proof of `¬ Q`.
-- Exercises `tryDecompEqMpNotEqProp` in `Specialized/Grind.lean`.
--
-- DISPATCH-ORDER LOCK: this snapshot also pins the invariant that
-- `trySpecializedDecompHandlers` (Phase 3) runs BEFORE the general
-- structural `tryDecompEqMp` (Phase 4).  If you swap their order, this
-- snapshot diverges to a generic `refine @Eq.mp ...` over the
-- un-collapsed `not_eq_prop`-wrapped expression — losing both the
-- `intro hq` introduction and the recursive `propext`/`Iff.intro`
-- restructure.  See `Decompiler.lean:351`.
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

-- Test 13: recurse into `mt` implication proofs instead of embedding them
-- raw.  Exercises `tryDecompMt` in `Specialized/Grind.lean`.
/--
info: Try this:
  [apply] apply mt
    · exact hPQ
    · exact hnQ
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (hPQ : P → Q) (hnQ : ¬ Q) : ¬ P := by
  decompile exact mt hPQ hnQ

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §5  propext / Iff.intro simplifier reductions  (regression locks)    ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Test 14: `Eq.mp (propext (Iff.intro f g)) ev` collapses to `f ev` (forward
-- direction).  Core simplifier-side reduction (`simplifyPropCast` →
-- `simplifyProjOfIntro`) that grind's polynomial normalization chains rely
-- on.  Regressing it surfaces here, not as a Sum/Int nightly timeout.
set_option linter.unusedVariables false in
/--
info: Try this:
  [apply] exact f hp
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (f : P → Q) (g : Q → P) (hp : P) : Q := by
  decompile exact (Eq.mp (propext (Iff.intro f g)) hp)

-- Test 15: `Eq.mp (Eq.symm (propext (Iff.intro f g))) ev` collapses to
-- `g ev` (backward direction via `Eq.symm` wrap).  Same simplifier path as
-- Test 14 but exercising the `Eq.symm` peel in `simplifyPropCast`.
set_option linter.unusedVariables false in
/--
info: Try this:
  [apply] exact g hq
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (f : P → Q) (g : Q → P) (hq : Q) : P := by
  decompile exact (Eq.mp (Eq.symm (propext (Iff.intro f g))) hq)

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §6  forall_congr / implies_congr peelers  (regression locks)         ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Test 16: `Eq.mp (forall_congr h_eq) h_uni a` —
-- `tryDecompEqMpForallCongr` instantiated case (one trailing application).
-- Locks in the L70 fix: regressing this handler is what caused Sum L70 to
-- time out at 200k heartbeats before the peeler landed.  The `have` step
-- puts the user-form hypothesis in the lctx so downstream `lia` (in real
-- grind output) can close — here there's no arithmetic so we fall through
-- to the structural `refine @Eq.mp` recursion.
--
-- DISPATCH-ORDER LOCK: this snapshot also pins the invariant that
-- `tryDecompEqMpForallCongr` (Phase 4) runs BEFORE `tryDecompEqMp`
-- (also Phase 4 but later in the list).  If you swap their dispatch
-- order, this snapshot diverges to a generic `refine @Eq.mp ...` over
-- the un-peeled `forall_congr` premise.  See `Decompiler.lean:360`.
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

-- Test 18: `Eq.mp (forall_congr (fun x => h_eq x)) h_uni` —
-- `tryDecompEqMpForallCongr` universal case (no trailing args).  The
-- handler uses `lambdaTelescope` to peel the binder, which only fires when
-- the body is a literal lambda — real grind output always has a non-trivial
-- lambda body so this is the realistic shape.
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

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §7  sanitizeInaccessibleIdents (regression locks)                    ║
-- ╚══════════════════════════════════════════════════════════════════════╝
--
-- The 2026-05-04 cross-file fix: anonymous typeclass binders (`[Foo α]`
-- with no explicit name) get hygienic / inaccessible userNames in the
-- lctx, and `tryDecompTheoremAppFallback`'s `refine @theorem α inst✝ …`
-- form would then emit those `inst✝` refs literally.  The `✝` marker
-- makes them unparseable as source, so the dumped suggestion fails
-- cross-file re-elaboration.  `sanitizeInaccessibleIdents` (Helpers.lean)
-- runs at `buildDecompiledTactics` and replaces those refs with
-- `inferInstance` — typeclass synthesis re-fills the position at re-elab.
--
-- Narrow gate: macro-scoped or `✝`-bearing name + lctx hit + class type.
-- A previous broader version that fired on any `hasMacroScopes` ident
-- broke validation by replacing accessible hygienic binders.

namespace Sanitize

class FooBar (α : Type) where
  rel : α → α → Prop

axiom foo_trans {α : Type} [FooBar α] {a b c : α}
  (h1 : FooBar.rel a b) (h2 : FooBar.rel b c) : FooBar.rel a c

end Sanitize

open Sanitize

-- Test 19: bare `inst✝` ref → `inferInstance`.
-- Trigger: a theorem app with multiple proof args forces
-- `tryDecompTheoremAppFallback` to emit `refine @foo_trans α inst✝ a b c ?_ ?_`.
-- The anonymous `[FooBar α]` binder gives the instance fvar a hygienic
-- userName; the sanitizer rewrites the `inst✝` slot to `inferInstance`.
/--
info: Try this:
  [apply] refine @LeanDecomp.Test.Sanitize.foo_trans α inferInstance a b c ?_ ?_
    · exact h1
    · exact h2
-/
#guard_msgs (whitespace := lax) in
example {α : Type} [FooBar α] (a b c : α)
    (h1 : FooBar.rel a b) (h2 : FooBar.rel b c) : FooBar.rel a c := by
  decompile exact foo_trans h1 h2

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║ §8  Structural-handler smoke tests                                   ║
-- ╚══════════════════════════════════════════════════════════════════════╝
--
-- These handlers fire deep in Phase 4 / Phase 6 of dispatch and rarely
-- appear in nightly snapshots, so changes can silently regress them.
-- Each test is a tiny synthetic input where the named handler is the
-- only candidate — if it stops firing, the snapshot drops to a raw
-- `exact <term>` from `decompExact`, which is easy to spot.

-- Test 20: `tryDecompAndProj` on `And.left h`.  The handler refuses on
-- the applied-to-extra-args case (`h.left x`), so this is the canonical
-- 3-arg shape.  Theorem-app fallback would otherwise emit `exact h.left`.
/--
info: Try this:
  [apply] apply And.left
    · exact h
-/
#guard_msgs (whitespace := lax) in
example (a b : Prop) (h : a ∧ b) : a := by
  decompile exact And.left h

-- Test 21: `tryDecompEqSymm` on `Eq.symm h`.  `tryDecompEqMp` doesn't
-- match (no `Eq.mp` head); `tryDecompEqSymm` is the only candidate
-- before the theorem-app fallback.
/--
info: Try this:
  [apply] refine Eq.symm ?_
    · exact h
-/
#guard_msgs (whitespace := lax) in
example (a b : Nat) (h : a = b) : b = a := by
  decompile exact Eq.symm h

-- Test 22: `tryDecompIffMpMpr` on `Iff.mp h hp`.  Phase 4 propositional
-- handler.  Locks the `@`-prefixed emit shape (concern #11 fix,
-- 2026-05-09): the handler emits `refine @Iff.mp P Q ?_ ?_` with the
-- type args explicit so re-elaboration doesn't depend on later mvar
-- unification.  Without `@` + explicit types, the bare
-- `refine Iff.mp ?_ ?_` shape fails synthetic re-elab because `?P, ?Q`
-- can't be inferred before the holes are filled.
/--
info: Try this:
  [apply] refine @Iff.mp P Q ?_ ?_
    · exact h
    · exact hp
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  decompile exact Iff.mp h hp

-- Test 23: `tryDecompEqRefl` on `@Eq.refl Nat 1`.  Trivial but locks the
-- `Eq.refl → rfl` rewrite — without it, the term would render as
-- `exact @Eq.refl Nat 1` (verbose) or hit the theorem-app fallback
-- which can't recurse meaningfully on a fully-applied refl.
/--
info: Try this:
  [apply] rfl
-/
#guard_msgs in
example : (1 : Nat) = 1 := by
  decompile exact @Eq.refl Nat 1

-- Test 24: `tryDecompEagerReduce` on `eagerReduce (Eq.refl true)`.  Phase 6
-- handler — fires when `eagerReduce` is the literal proof-term head.
-- Without this handler, the wrapper would prevent `tryDecompEqRefl` from
-- collapsing to `rfl` (head is `eagerReduce`, not `Eq.refl`), and the
-- term would fall through to the theorem-app fallback or `exact`.
-- Real grind certificates use `eagerReduce (Eq.refl true) : <decide-expr> = true`
-- as a reducibility marker.
/--
info: Try this:
  [apply] decide
-/
#guard_msgs in
example : (true : Bool) = true := by
  decompile exact eagerReduce (Eq.refl true)

-- Test 25: `tryDecompTheoremAppFallback` const head, mixed proof / non-proof
-- args, no typeclass binders.  Test 19 covers this path with an inferInstance
-- sanitizer rewrite; this test locks the no-sanitizer baseline (custom axiom
-- with two `Prop` parameters and two proof-args).
namespace MultiArg
axiom my_thm (P Q : Prop) (h1 : P) (h2 : Q) : P ∧ Q
end MultiArg

/--
info: Try this:
  [apply] refine MultiArg.my_thm P Q ?_ ?_
    · exact h1
    · exact h2
-/
#guard_msgs (whitespace := lax) in
example (P Q : Prop) (h1 : P) (h2 : Q) : P ∧ Q := by
  decompile exact MultiArg.my_thm P Q h1 h2

end LeanDecomp.Test
