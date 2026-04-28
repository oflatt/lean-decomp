# lean-decomp

A Lean 4 proof decompiler that converts low-level proof terms into readable tactic scripts. It avoids powerful automation in the output (no `grind`, `simp`, `simp_all`, or `omega`), sticking to basic tactics like `cases`, `intro`, `apply`, `exact`, `refine`, `rfl`, `contradiction`, and `decide`. The goal is a faithful, low-level structural translation of the proof term.

## How it works

lean-decomp provides a `decompile` tactic that wraps any other tactic block:

```lean
import LeanDecomp

example : P := by
  decompile
    grind
```

When elaborated, `decompile` runs the wrapped tactic, captures the resulting proof term, then runs it through a three-stage pipeline:

1. **Term simplification** (`Simplify.lean`) — Rewrites the proof term before decompilation: unfolds auxiliary definitions, eliminates identity wrappers (e.g. `Lean.Grind.alreadyNorm`, `Lean.Grind.nestedProof`), simplifies `Eq.rec`/`noConfusion` patterns, and beta-reduces.
2. **Term-to-tactic decompilation** (`Decompiler.lean`) — Pattern-matches on proof term structure and maps it to tactics (`intro` for lambdas, `cases` for `casesOn`, `apply`/`exact`/`refine` for applications, `let` for let-bindings, `rfl` for `Eq.refl`, `decide` for `eagerReduce`, `contradiction` for `False` eliminations, etc.). This stage is a faithful structural translation — it does not change the proof strategy, only the representation.
3. **Tactic simplification** (planned) — Will clean up the generated script (e.g., collapsing redundant steps).

After decompilation, the pipeline validates the generated tactics by re-elaborating them against the original goal, then suggests the result via Lean's "Try This" mechanism.

### Correctness Invariant

The primary invariant is: **the decompiler should always produce a proof that re-elaborates successfully**.

Readability is secondary to correctness. When the structural decompiler cannot safely reconstruct a recursive subproof, it should fall back to an `exact` proof term for that subproof rather than emit a prettier script that does not validate.

## Top TODO

1. **Try `decide` in `mkExactFallbackTactics` before `with_unfolding_all exact`** when the proof term contains `eagerReduce`.
   - Background: `eagerReduce.{u} : {α} → α → α := fun a => a` is grind's identity-function kernel marker that forces eager unfolding under `with_unfolding_all`. It typically wraps a `(Eq.refl true : c.toBool = true)` certificate inside `Int.Linear.norm_le` (and similar) reflective normalizers.
   - The current fallback emits `with_unfolding_all exact <giant>`. That re-runs the kernel reduction at re-elaboration time and is the dominant cost in Sum L70's `forall_congr` block.
   - When the goal is decidable (which it is whenever an `eagerReduce`-wrapped certificate is the witness — those certificates are exactly `Decidable.decide ... = true`), `decide` runs the same reduction once and produces a much smaller residual term. Try `decide` first; fall back to `with_unfolding_all exact` only when `decide` does not validate.
   - Implementation: `LeanDecomp/Helpers.lean`, in `mkExactFallbackTactics`, in the `containsEagerReduce` branch. Use `validateOrExact`-style validation rather than committing the tactic eagerly.
2. **Snapshot tests for the decompiler output.** Today regressions on Sum L70 / Int L91 surface only as nightly elaboration timeouts. Locking down the generated tactic shape (line counts, presence/absence of `with_unfolding_all` blocks) in `LeanDecomp/Test.lean`-style `#guard_msgs` blocks would catch silent regressions before they hit nightly.
3. **Document the supported envelope.** The decompiler ships with a stable list of structural handlers (see *What Is Working* below) and a list of grind-specific specializations (see `Specialized/Grind.lean`). A short "what shapes do we handle" table near the top of the README would make it easier to predict whether a new failure is in scope.

## Recommended Next Steps (after the top TODO)

- **Extend the `MVarId.cases`-based per-branch decomp to generalized motives.** The current implementation falls back to a synthesized lctx when the casesOn motive carries a trailing `heq : disc = ctor xs` (i.e., proofs from `cases h : disc with`). The naive approach — `MVarId.generalize` with `hName?` to introduce both the abstracted fvar and the eq hyp, then `MVarId.cases`, then substitute `heq → real_eq_fvar` in the body — was tried and breaks `LeanDecomp.simple`: the old body's `Eq.rec` cleanup (substituting `heq → Eq.refl s` and stripping the resulting transport) turns out to be load-bearing for downstream handlers like `contradiction` and `noConfusion`, which consume the type-incorrect intermediate the cleanup produces. The right fix probably needs to either (a) keep the old cleanup but run the recursion in the new substituted lctx, or (b) drive the per-branch recursion through `evalTactic` of `cases h : disc with` syntax (using a synthetic outer mvar) so Lean's elaborator handles the transport natively. Multi-eq generalized motives (indexed inductive types) are a further extension.
- **Add a function-leaf handler for `Eq.mp <forall_congr ...> <evidence>` patterns.** The single remaining `with_unfolding_all exact` block in Sum L70 has shape `Eq.mp.{0} (∀ x : T, P x → Q_user x) (∀ x : T, P x → Q_poly x) (forall_congr (fun x => implies_congr ...)) <evidence>` — a Pi-typed value transported through grind's polynomial-normalization `forall_congr` cast. A handler that detects this shape and emits `intro x hx; have h_user := <evidence> x hx; lia` would replace the whole leaf with ~3 lines of clean tactic. Estimated <60 LOC in `Specialized/Grind.lean`.
- **Apply the "single lia call" pattern wherever multiple sub-goals close arithmetically.** `tryDecompFinsetIntervalMembership` and `tryDecompFalseFromLia` are the current users. Any handler that currently emits per-branch `lia` is a candidate.
- **Generalize `simplifyEqRecOfIdMotive` past the `a = True ∧ base = True.intro` restriction.** Rule was renamed in preparation but body is still narrow. Lifting the restriction caused `maximum recursion depth has been reached` errors before; retry with a more conservative generalization.
- **Audit other `Lean.Grind.*` simplifier rewrites for type-correctness bugs** (the `of_eq_eq_true` precedent — the rewrite returned a proof of `a = b` for a lemma whose actual conclusion was `a ∧ b ∨ ¬a ∧ ¬b`).
- **Set `pp.numericTypes` and `pp.coercions.types` on every delab call that produces user-elaborable syntax.** L91 demonstrated that default delab options drop type information needed to disambiguate mixed-numeric expressions.

## Design Notes

### Decompiler invariant: real proof state at every recursive call

The decompiler is structured so that **every recursive call into `decompileExpr` runs in a `(lctx, localInsts)` that matches the proof state the real run of the surrounding tactics would produce**. This is the single invariant that keeps validation accurate: `subproofTacticsCloseGoal` allocates a fresh synthetic-opaque mvar in the caller's `(lctx, localInsts)`, so as long as that context matches the real run, the candidate tactics elaborate the same way they would in the real proof.

The hard case is `tryDecompCasesOn`. Real `cases h : disc with | ctor a b ... => body` doesn't just bind `a, b` — it also *substitutes* the discriminant: any fvar whose type mentions `disc` is rewritten in terms of the constructor outputs, and `disc` itself is consumed. A naively synthesized branch lctx (just adding the constructor args via `Meta.lambdaTelescope`) misses this substitution, and validation false-negatives appear: tactics like `contradiction` that rely on injection/noConfusion across the case binding succeed in real elaboration but fail in fresh-mvar validation.

The fix: `tryDecompCasesOn` allocates a synthetic outer mvar of the casesOn application's type, calls `MVarId.generalize` (if the discriminant isn't already a fvar), then `MVarId.cases` to obtain the real substituted per-branch lctxs. Each branch's recursive `decompileOrExact` call uses the substituted lctx — validation reflects what the real run would do.

The relevant code lives in `LeanDecomp/Helpers.lean` (`runInGoal`, `runInSubgoal` building blocks; the invariant is documented there) and `LeanDecomp/CasesOn.lean` (the `MVarId.cases`-based per-branch loop).

**Currently uncovered**: generalized cases motives (`cases h : disc with`). `MVarId.cases` doesn't reproduce the trailing `heq : disc = ctor xs` hypothesis those motives produce, so that path falls back to the older synthesized lctx and `decompileOrExact` silently degrades to `exact` when validation false-negatives bite. See "Recommended Next Steps" for what was tried and what's left.

**Other recursion sites** maintain the invariant naturally: `tryDecompIntro` (renamed lctx matches real `intro`), `tryDecompLet` (let-decl matches real `let`), `tryDecompByContradiction` (binder matches real `intro` after `apply Classical.byContradiction`), and `emitTacticWithSubgoals` (outer lctx is correct for `refine ?_` style subgoals that don't introduce bindings).

For handler decisions that need a quick test of the goal but where validation would be too heavyweight (or would loop on the very tactic being decided), goal-shape checks ("is the goal exactly `False`?") are preferred over `subproofTacticsCloseGoal`.

### What `eagerReduce` is and how we use it

`eagerReduce.{u} : {α : Sort u} → α → α := fun {α} a => a` is an identity function declared with `isReducible: false`. The kernel uses it as a marker for eager unfolding under `with_unfolding_all`. Grind's polynomial normalizers (`Int.Linear.norm_le`, `Nat.Linear.*`, etc.) emit certificates of the form `eagerReduce (Eq.refl true) : <decide-expr> = true` so the kernel can verify the certificate by definitional reduction.

The decompiler currently has two responses:
- `tryDecompEagerReduce` (`Decompiler.lean`): when `eagerReduce` is the literal proof-term head, emit `decide`.
- `mkExactFallbackTactics` (`Helpers.lean`): when an `eagerReduce` appears anywhere inside a fallback exact, wrap the whole fallback in `with_unfolding_all exact <term>` so re-elaboration triggers the same unfolding.

The "top TODO" above is to try `decide` before `with_unfolding_all exact` in the second case — same kernel work, much smaller residual term.

## Current Status

**Goal**: a low-level decompiler from grind proof terms to basic tactics. Short term we want to decompile every `grind` call in mathlib; long term we will simplify the resulting proof via a tactic-level pass.

### What Is Working

- The project is fully on the structural decompiler path; the old `Omega.lean` route is gone.
- `LeanDecomp/Test.lean` builds successfully, including the arithmetic regressions that previously failed on certificate-heavy `Eq.mp` terms.
- The decompiler has stable structural handlers for:
  - lambdas / `intro`
  - `let` bindings
  - `casesOn` (with up-front `have hOr : ... := by ...` decompile of non-fvar discriminants)
  - `False.rec` / contradiction-style eliminators
  - `Eq.refl -> rfl`
  - `eagerReduce -> decide`
  - structural `Eq.mp`
  - `propext` and `Iff.intro`
  - `Iff.mp` / `Iff.mpr` (via `refine` with two subgoals)
  - `And.left` / `And.right` (via `apply` on the conjunction witness)
  - proposition-valued `Eq.rec` / `Eq.ndrec` transports (`EqDecomp.lean`)
  - `byContradiction` (tries structural decomp of the body first, falls back to arithmetic terminals only if that fails)
  - late theorem-application fallback with recursive proof subgoals
- Specialized grind handling includes:
  - `mt` decomposed into two structural subgoals
  - small `Eq.mp` peelers for `Lean.Grind.iff_eq` and `Lean.Grind.not_eq_prop`
  - `tryDecompEqMpIntLinearNormLe` collapses `Int.Linear.norm_le ...` casts into a single `lia`
  - `tryDecompFinsetIntervalMembership` for `_ ∈ Finset.<X> a b` (single trailing `lia` after `rw [mem_X]`)
  - `tryDecompFalseFromLia` for `False` goals carrying grind automation
  - `tryDecompAbsLeaf` for `abs.eq_1` leaves with a matching sign hypothesis
  - `tryDecompAbsCaseSplitContradiction` for `False` goals where the lctx has any `abs x` hypothesis
- Simplifier rewrites in `Simplify.lean` / `Simplify/Grind.lean`:
  - `simplifyProjOfIntro` reduces `And.left/And.right` of explicit `And.intro`, and `Iff.mp/mpr` of explicit `Iff.intro`. This unblocks the `Eq.mp (Eq.symm (propext (Iff.intro f g))) ev → g ev` chains grind emits.
  - `simplifyEqRecOfIdMotive` (formerly `simplifyEqRecOfTrueIntro`) reduces `Eq.rec.{0, _} Prop True (motive := fun x _ => x) True.intro target h` to `Eq.mp h True.intro`.
  - `simplifyEqMpTrueIntroEqTrue` matches both `Eq.mp` and `Eq.mpr` (since `simplifyPropCast` rewrites between them) and handles applied transports with beta-reduction.
- Output policy is enforced: the decompiler does **not** emit `simp`, `simp_all`, `grind`, or `omega` as generated proof steps.

### Nightly Snapshot

Recent focused nightly runs:

```bash
python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean \
  --treatment decompile --no-benchmark \
  --dump dump-nightly-int --output results-nightly-int.json

python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean \
  --treatment decompile --no-benchmark \
  --dump dump-nightly-sum --output results-nightly-sum.json
```

Results:
- `Mathlib/Algebra/Order/Group/Unbundled/Int.lean`: 5/5 (lines 47, 69, 76, 79, 91).
- `Mathlib/Algebra/Order/Group/Int/Sum.lean`: 2/4 (55, 81 succeed; 36, 70 timeout).

Int L69 simplifies to `apply Classical.byContradiction; intro hp; lia`. L47/L76/L79/L91 decompile via byContradiction → outer `cases` over an `of_eq_eq_true`-shaped disjunction → inner `cases` of the resulting `And` → `tryDecompAbsCaseSplitContradiction` at each leaf.

### Main Open Blockers

- **Sum L36 / L70 elaboration timeouts.** Decomposition produces structurally valid tactics (~140 lines for L70), but elaboration of the generated tactic exceeds the default 200k heartbeat budget. After the `MVarId.cases` refactor, wall time at 8M heartbeats dropped from ~25s to ~12s (substituted lctxs are smaller and faster to elaborate), but the heartbeat budget is still bounded by kernel `isDefEq`/`whnf` work in the **single remaining** `with_unfolding_all exact` block — an `Eq.mp.{0} (∀ x ∈ s, c ≤ x) (∀ x ∈ s, c + -1·x ≤ 0) (forall_congr ...) <evidence>` transport. The "top TODO" `decide` swap targets this block; the longer-term fix is the `forall_congr` handler listed under Recommended Next Steps.
- **No stage-3 tactic simplifier.** Successful decompiles still contain `have hOr : ... := by lia; cases hOr with | inl ⟨..⟩ => ...` boilerplate.

## Lessons Learned (selected)

These are the lessons most likely to bite future work; the full chronological log lived in earlier README revisions and is now in `git log`.

- **Targeted decompiler-side handlers beat broad simplifier rewrites.** A more aggressive `Eq.rec` simplification caused recursion-depth problems and was removed. Naive expansion of single-cast `Lean.Grind.not_eq_prop` was benchmark-negative.
- **Type-correctness of `Lean.Grind.*` simplifier rewrites must be checked.** `Lean.Grind.of_eq_eq_true` rewrote `h : a ∧ b ∨ ¬a ∧ ¬b` to `Eq.mpr ... True.intro : a = b` — different result types. The bug was hidden for months by a `casesOn` bail-out on `Lean.Grind.*` discriminants. Removing both the rewrite and the bail-out unblocked many `Int.lean` failures. Any rewrite in `Simplify/Grind.lean` should be type-preserving.
- **One `lia` call on a compound goal is much cheaper than many.** `lia` (= `cutsat`, routed through `grind`) pays a per-call setup cost — engine setup, polynomial term construction, search — that does not amortize. Switching `tryDecompFinsetIntervalMembership` from `rw [mem_X]; refine ⟨?_, ?_⟩ <;> lia` to `rw [mem_X]; lia` cut Sum L70 from ~86s to ~25s.
- **The `cases ... with` contradiction-branch skip must respect single-constructor inductives.** Skipping the only alt for an `And.intro`-shaped match leaves `cases hOr with` with no alternatives, which Lean rejects.
- **Default `delabToRefinableSyntax` options drop type information the parser needs.** L91 was blocked by `(-1) * ↑a + ↑b ≤ 0 ∨ ¬...` re-elaborating against `ℕ`; setting `pp.numericTypes := true` and `pp.coercions.types := true` on `have <type>` and `by_cases <pred>` delabs fixed it.
- **Validation does not see cases-bound constructor unification.** Per-branch validation in fresh synthetic-opaque mvar contexts gave false negatives whenever the real proof relied on injection/noConfusion across the cases binding. Now `tryDecompCasesOn` calls `MVarId.cases` directly to obtain the real substituted per-branch lctx, and recursive decomp runs in that lctx so validation reflects the real run. See "Decompiler invariant" above. Generalized motives (`cases h : disc with`) are still on the older path.
- **Generalized motives extension via `MVarId.generalize` + eq-fvar substitution breaks `LeanDecomp.simple`.** Tried the obvious extension (use `MVarId.generalize` with `hName?` to introduce both abstracted fvar and eq hyp, then `MVarId.cases`, then substitute `heq → real_eq_fvar` in the body). Two issues surfaced: (1) `MVarId.cases` reverts and re-introduces dependent hypotheses, so the eq-fvar's id changes per branch — must be looked up by user name. (2) More importantly, the old path's `Eq.rec` cleanup (substituting `heq → Eq.refl s` and stripping the resulting transport) is **load-bearing** for downstream handlers like `contradiction` and `noConfusion`, which consume the type-incorrect intermediate the cleanup produces. Reverted; documented in Recommended Next Steps.
- **The `MVarId.cases` refactor reduced wall-time elaboration cost as a side effect.** Sum L70 wall time at 8M heartbeats dropped from ~24s to ~12s. Likely because the cases-substituted lctx is smaller (the discriminant fvar is gone, references go directly to the constructor pattern rather than through a transport). The 200k-heartbeat budget is unchanged — the timeout for L70/L36 is bounded by kernel `isDefEq`/`whnf` work, which the substitution doesn't reduce.
- **Decompilation does not share subterms.** Walking the proof as a tree (no hash-consing or `let`-binding) means an inner subproof appearing `n` times generates `n` copies in the output. CSE on the proof term would amortize the elaborator's work, but is deferred until simpler structural fixes are exhausted.

## Things that already failed and should not be retried naively

- broad `Eq.rec` simplification in `Simplify.lean`
- naive expansion of single-cast `Lean.Grind.not_eq_prop`
- adding `simp` to generated proof output to close arithmetic subgoals
- the previous `Lean.Grind.of_eq_eq_true` simplifier rewrite (returned a proof of the wrong type)
- using `subproofTacticsCloseGoal` to validate `contradiction`-style tactics inside a handler — validation does not reproduce `cases`-introduced unification

## Architecture Notes

- `LeanDecomp/Simplify.lean` — Expr-level proof-term cleanup before decompilation. `LeanDecomp/Simplify/Grind.lean` is its grind-specific subset; rewrites must be type-preserving.
- `LeanDecomp/Decompiler.lean` — main structural term-to-tactic pass and late theorem-app fallback. Keep grind-specific knowledge out: reason about goal shapes, not proof-term contents.
- `LeanDecomp/EqDecomp.lean` — equality, congruence, and proposition-transport handlers.
- `LeanDecomp/CasesOn.lean` — `tryDecompCasesOn`. Uses `MVarId.cases` to obtain the real substituted per-branch lctx for non-generalized motives (see "Decompiler invariant" above). Generalized motives still take the older `Meta.lambdaTelescope` path.
- `LeanDecomp/Specialized/Grind.lean` — grind-specific structural handlers (`mt`, `Eq.mp` peelers, `abs`-shaped contradictions). Tried via `trySpecializedDecompHandlers` between `tryDecompCasesOn` and the general structural handlers.
- `LeanDecomp/Helpers.lean` — `subproofTacticsCloseGoal`, `validateOrExact`, `mkExactFallbackTactics` (the `decide`/`with_unfolding_all` fallback site).
- `LeanDecomp/ProofTermMacro.lean` — `decompile`/`showterm`/`showsimpl` elabs.

## Benchmarking

- **`scripts/nightly.py`** — Nightly evaluation: clones mathlib4, finds files containing `grind`, benchmarks the decompiler on each grind site.
- **`scripts/mine_grind_history.py`** — Mines mathlib history for removed `grind` calls. `--benchmark-limit N` compares whole-file timing before vs after the first N removal hunks.
- **[eval-live](https://github.com/oflatt/eval-live)** — Live HTML dashboard library for viewing benchmark results.

Use `--dump <dir>` to preserve generated inputs. The nightly script copies validated variants to `<dir>/Mathlib/.../<FileStem>/L<line>.<treatment>.lean` and failures to `*.query.lean` / `*.failed.lean`.

### Using `nightly.py`

Run from the repository root. It will reuse or clone `mathlib4/`, reset that checkout to the pinned commit in `scripts/nightly.py`, add the local `lean-decomp` dependency, build `lean-decomp`, build the targeted mathlib modules, and run the selected treatments on each `grind` site.

```bash
# Show CLI help
python scripts/nightly.py --help

# Run decompile extraction only on one file, and keep generated queries
python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean \
  --treatment decompile --no-benchmark \
  --dump dump-nightly-int --output results-nightly-int.json

# Benchmark all treatments on a folder and serve the HTML dashboard
python scripts/nightly.py mathlib4/Mathlib/Algebra/Order/Group \
  --runs 3 --warmup 1 --serve
```

Notes:
- `path` is workspace-relative, not mathlib-relative.
- `--no-benchmark` is the fastest way to check whether extraction/re-elaboration succeeds.
- `--treatment decompile` is useful while focusing on the decompiler specifically.
- `--dump` is essential when debugging failures.

## Debugging Playbook

Start with the saved nightly artifacts rather than re-running all of mathlib:

```bash
# Re-check a saved failing query directly
cd mathlib4
lake env lean ../dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/L55.decompile.query.lean
```

When changing decompilation behavior:

```bash
lake build LeanDecomp.Test    # focused regression file
python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean \
  --treatment decompile --no-benchmark \
  --dump dump-nightly-sum --output results-nightly-sum.json
```

For Sum/Int failures, the most efficient workflow is:
- inspect the preserved `*.query.lean` file
- isolate the failing obligation into a smaller probe if needed
- inspect the simplified proof shape (head: `Eq.rec`, `Eq.ndrec`, `Eq.mp`, `propext`, `congrArg`, `mt`, `Iff.mp`, `And.left`, `Or.casesOn`, `byContradiction`?)
- add the narrowest possible structural handler
- rebuild `LeanDecomp.Test`
- rerun only the affected nightly slice

Where to make changes:
- proof-term normalization → `LeanDecomp/Simplify.lean`
- equality transport / congruence → `LeanDecomp/EqDecomp.lean`
- theorem-app structure / fallback behavior → `LeanDecomp/Decompiler.lean`
- grind-specific shapes → `LeanDecomp/Specialized/Grind.lean`
