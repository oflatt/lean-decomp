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

1. **Order-grind handlers** for `Lean.Grind.Order.*` — analog to the existing `Int.Linear.*` arithmetic specialization in `Specialized/Grind.lean`.  Investigation 2026-05-01: `min_assoc` (one of the historical "replaced with manual proof" cases — the human replacement is 6 lines) decompiles to 112 lines that re-elaborate correctly, but 3 inner `exact <Eq.trans …>` chains reference `Lean.Grind.Order.le_eq_false_of_lt` etc.  Specialized handlers for these would close the order-grind cluster of failures (≈10 of the 36 broader-corpus failures, including the `Field/Basic.lean` and `Ring/Unbundled/*` clusters).
2. **Cross-version stability experiment.** Pick a grind-heavy mathlib file, decompile every grind site, then bump grind/Lean toolchain and count how many decompiled proofs still elaborate vs how many grind sites still close. Mining surfaced the headline anchor: `Mathlib/Algebra/ContinuedFractions/.../CorrectnessTerminating.lean:150` was reverted with `#adaptation_note` citing [lean4#9825](https://github.com/leanprover/lean4/issues/9825) — author waiting for upstream grind fix.  Decompile-once should survive that regression.
3. **Stage-3 tactic simplifier (residual speed gap).** After the byContradiction Phase-A short-circuit landed (2026-05-01) and the `Or.casesOn → bare lia` collapse landed (2026-05-04 — see Done section below), decompile is 0.72×–1.13× of grind on grind-success cases.  The remaining gap is in the `by_cases h_abs : … ; · rw [abs_of_nonpos h_abs] at hp; lia ; · rw [abs_of_pos (not_le.mp h_abs)] at hp; lia` shape emitted by `tryDecompAbsCaseSplitContradiction` (Int L47/L91): two `lia` calls, neither obviously merge-able since each branch needs a different rewrite first.  Closing this needs either lia/cutsat to natively handle `abs x` case splits or a hypothesis-rewrite-aware "single lia over the conjoined goal" rule — much less mechanical than the trivial `Or` collapse was.  Polish item, not paper-blocker.
4. **Decompile-cost characterization on the broader corpus.** Coverage on `Mathlib/Algebra/Order/` is 33% (18/54).  Failure clusters: 15 cross-file re-elaboration (anonymous `inst✝` refs), 10 wall-clock timeouts (>120s — simplifier hangs on giant grind output), 5 heartbeat timeouts, 5 validation→exact-fallback, 1 too-large output. Each cluster suggests a concrete fix: emit hygienic typeclass refs / add heartbeat checks in the simplifier / etc.
5. **Snapshot tests for the decompiler output.** Tests 14/15 lock down the `Eq.mp (Eq.symm? (propext (Iff.intro f g))) ev → f/g ev` simplifier collapse; **Tests 16/17/18** lock down the `tryDecompEqMpForallCongr` / `tryDecompEqMpImpliesCongr` peelers. Still missing: snapshots for the actual Sum/Int *output shape* — those depend on grind's emitted certificates and are version-sensitive.
6. **Document the supported envelope.** The decompiler ships with a stable list of structural handlers (see *What Is Working* below) and grind-specific specializations (see `Specialized/Grind.lean`). A short "what shapes do we handle" table near the top of the README would make it easier to predict whether a new failure is in scope.

## Long-term plan / Paper framing

Goal: a paper on decompiling Lean proofs as a way to get **simpler, more stable, and (ideally) faster** proofs out of opaque automation tactics. Phased to land each artifact a paper would need.

- **Phase 1 — close the speed gap (next ~2 weeks).** Ship the stage-3 tactic simplifier. Target: Int L91 from 0.640s to under 0.1s. Goal threshold: decompile within 2× of grind on grind-success cases on both nightly slices. Without this we cannot say "comparable on success, much better elsewhere" — the comparison story has to start with parity.
- **Phase 2 — find the wins (~4 weeks).** Expand `mine_grind_history.py` to surface grind sites that historically took >1s or timed out. Decompile each. Bin results into qualitative wins (grind fails, decompile closes) and quantitative wins (≥10× speedup). These are the paper's empirical anchors.
- **Phase 3 — robustness experiment (~6 weeks).** Cross-version stability comparison: pin a mathlib file, decompile every grind, bump grind / Lean toolchain, count survivors on each side. If decompiled proofs are more stable than grind invocations across versions, that's the paper's headline. Lock the methodology before running the experiment so we don't p-hack.
- **Phase 4 — generality (~8 weeks, parallel with refactors).** Extend coverage beyond grind: `omega`, `polyrith`, `linarith`, `norm_num`. Each tactic has its own certificate shape; one paper subsection each. The structural handlers (`Eq.mp`, `casesOn`, `propext`, etc.) are general — most of the work is per-tactic specializer modules under `Specialized/`.
- **Phase 5 — paper writing.** Outline: motivation (opaque automation, broken-after-grind-bumps proofs); approach (3-stage pipeline: term simplify → term-to-tactic → tactic simplify); specialization (per-tactic certificate handlers); evaluation (mathlib coverage %, head-to-head speed, cross-version stability); limitations (heartbeat-bounded recursion, generalized cases motives, etc.).

## Performance Snapshot (2026-05-01, updated after byContradiction specialized-first)

Benchmarks via `scripts/nightly.py --runs 3 --warmup 1 --treatment {original,decompile}`. Times are cumulative `tactic execution` seconds at default heartbeat budget; "speedup" is (original / decompile).

| File / line | grind (orig) | decompile | speedup |
|-|-|-|-|
| Sum L36 | 0.217 | 0.277 | 0.78× |
| Sum L55 | 0.208 | 0.222 | 0.93× |
| Sum L70 | 0.227 | 0.317 | 0.72× |
| Sum L81 | 0.214 | 0.218 | 0.98× |
| Int L47 | 0.045 | 0.054 | 0.83× |
| Int L69 | 0.044 | 0.058 | 0.77× |
| Int L76 | 0.049 | 0.068 | 0.72× |
| Int L79 | 0.049 | 0.062 | 0.79× |
| Int L91 | 0.050 | 0.063 | 0.79× |

**Decompile is now 0.72×–0.98× of grind on grind-success cases — within 30% on average, equal in the best case.**  Down from the previous 0.07×–0.98× range (Int L91 alone was 14× slower).

The big change: `tryDecompByContradiction` now tries specialized handlers (`tryDecompAbsCaseSplitContradiction`, `tryDecompFalseFromLia`, etc.) **before** structural recursion (in a new "Phase A" — see `Decompiler.lean:436`).  Previously, when grind's contradiction body was a deeply-nested `Or.casesOn` tree that ultimately resolves to a single `by_cases h_abs : a ≤ 0; …`, the structural recursion would emit ~50 lines of nested `cases hOr_N` with 6+ inner `lia` calls before the abs handler fired at the leaves.  Phase-A short-circuit lets the abs handler fire at the OUTER level and emit a flat 5-line equivalent, skipping the nested tree entirely.

Concrete L91 example: was 14× slower (0.640s, ~50 lines), now 1.3× slower (0.063s, ~5 lines).  L47 same shape: 3× → 1.2× slower.

Speed pitch for the paper now defensible: **comparable to grind on grind-success cases (within 30% on average), much faster on grind-timeout cases** (yet to be measured systematically).  The remaining 20–30% gap is from running `lia`/`grind`'s engine multiple times per branch in the cases that *do* genuinely need a case-split — addressable via the Top TODO #1 stage-3 simplifier.

## Broader corpus coverage (2026-05-01)

Ran nightly across all of `Mathlib/Algebra/Order/` (25 files containing 54 grind sites), with a per-query 120s wall-clock timeout to prevent hangs from blocking the rest.  Results in `results-broader-order.json`, dumps in `dump-broader-order/`.

**Coverage: 18/54 = 33%.**

Failure breakdown (36 total):

| Failure mode | Count | What it means |
|-|-|-|
| "suggestion produced but cross-file re-elaboration failed" | 15 | Macro's local validation passed, but the suggestion file written by `--dump` doesn't re-elaborate.  Usually because the emitted tactics reference `inst✝` (anonymous typeclass instances) or other names that don't survive cross-file emission. |
| Wall-clock timeout (>120s) | 10 | Macro hangs.  Most are `Antidiag/*` and similar — grind produces a giant proof and our simplifier or recursion gets stuck without yielding to heartbeat checks. |
| Heartbeat timeout | 5 | Macro's per-call budget exceeded inside one of the speculative-validation calls. |
| Validation failure → exact fallback | 5 | Decompile produced tactics that didn't close the goal; fell back to `exact <giant>` which also failed. |
| Decompile output too large (>20KB) | 1 | Output exceeded the macro's `maxSize`; refused to emit. |

**Successful shapes** are dominated by the `apply Classical.byContradiction; intro h; have hOr_N : φ ∨ ¬φ := by lia; cases hOr_N with | inl … | inr …` pattern (the same pattern that's slow in the perf snapshot above).  Some successes use `with_unfolding_all exact <giant>` — coverage but bad readability.

**Open coverage clusters** suggested by the failures:
- `Mathlib/Algebra/Order/Antidiag/*`: simplifier hangs on complex grind outputs.
- `Mathlib/Algebra/Order/Field/Basic`: 6 failures, mostly "suggestion produced but re-elaboration failed" — anonymous typeclass refs.
- `Mathlib/Algebra/Order/Ring/Unbundled/Rat`: 5 failures, similar pattern.

Running `min_assoc` from `Mathlib/Order/Defs/LinearOrder.lean:158` (one of the historical "replaced with manual proof" cases — the human replacement is 6 lines): our decompile produces a 112-line tactic block that re-elaborates correctly.  3 inner `exact <Eq.trans …>` blocks reference `Lean.Grind.Order.le_eq_false_of_lt` etc. — public Mathlib lemmas, but the structural decomp can't break those down further.  Suggests we need order-grind handlers (analogous to the existing `Int.Linear.*` arithmetic handlers) to get coverage on the `min`/`max`/`ite` shapes.

## Historical grind removals (2026-05-01)

`scripts/mine_grind_history.py` mined ~2 years of mathlib history for commits that removed a `grind` tactic call.  Results in `results-mine-grind-history.json` (165 KB).

**195 removal hunks**:

| Classification | Count |
|-|-|
| Replaced with other automation (simp / omega / aesop / cutsat) | 92 |
| Replaced with manual proof | 52 |
| Unknown refactor (file moves, splits) | 51 |

The **52 manual-proof replacements** are the paper's "where decompile wins" empirical anchors: cases where the author gave up on grind and wrote an explicit proof.  If decompile produces a stable tactic block from the original grind-using version, that's a direct stability win.

Top representative cases (by replacement size):
1. `Mathlib/Algebra/Polynomial/Splits.lean:313` — `grind [splits_iff_card_roots]` → 19-line deprecated alias chain.
2. `Mathlib/Data/List/Chain.lean:276` — `induction l using twoStepInduction <;> grind` → 8-line manual structural proof.
3. `Mathlib/Order/Preorder/Chain.lean:143` — `grind [RelEmbedding.map_rel_iff]` → 7-line manual proof using `RelHomClass`.
4. `Mathlib/Order/Defs/LinearOrder.lean:158` — `min_assoc` (above).
5. `Mathlib/Algebra/ContinuedFractions/Computation/CorrectnessTerminating.lean:150` — explicitly reverted with `#adaptation_note` citing [lean4#9825](https://github.com/leanprover/lean4/issues/9825) — author waiting for upstream grind fix.  **This is the headline stability story:** decompile-once and you don't need to revert when grind's flaky.

These cases are not yet directly testable from our pinned mathlib commit (the mining went back further than the pin), but the paper plan can cite them and rerun against an updated pin once we're ready to run the cross-version stability experiment (Phase 3 of the long-term plan).

### Done: collapse trivial `Or.casesOn → lia | lia` to bare `lia` (2026-05-04)

Sum L55/L81 dumps still contained the textbook hot pattern flagged in the previous Top TODO #1:

```
have hOr : c + (-1 : ℤ) * x ≤ 0 ∨ ¬c + (-1 : ℤ) * x ≤ 0 := by lia
cases hOr with
| inl h_1 => lia
| inr h_1 => lia
```

The byContradiction Phase-A short-circuit (2026-05-01) didn't catch this because the goal at the `Or.casesOn` site isn't `False` (it's the post-`apply Classical.byContradiction; intro hp` goal) and the residue then takes the structural `tryDecompCasesOn` path.

Added a post-loop check at the end of `tryDecompCasesOn` (`CasesOn.lean`):
- Trigger gate: `info.indName == ``Or` AND `useHaveWrapper` AND every branch's tactic seq is exactly `[lia]` (kind comparison against a freshly-built reference, not stringification — robust to whitespace and macro-scope idiosyncrasies).
- Gated try: validate bare `lia` against the original goal type via `candidateTacticsCloseGoal` (heartbeat-bounded, so a pathological miss doesn't burn the ambient budget).  If `lia` (= cutsat) closes the goal — which it usually does, since cutsat does internal disjunction case splits over `Decidable` shapes — return `[lia]` instead of the cases form.
- Fall-through: if validation fails, the original cases form is emitted.  Worst case is one extra speculative `lia` validation.

The fix is intentionally narrow: only `Or` (the propositional disjunction the `have hOr := by lia` wrapper produces), only when both branches reduced to a bare `lia`, only when the `have hOr` wrapper was about to be emitted.  Won't fire spuriously on, say, `Bool.casesOn` or `Nat.casesOn` — those have different shapes and benefit from the structural form.

**Why this is in `tryDecompCasesOn` rather than the `TacticSimplify.lean` post-pass**: the validation check needs the original goal's `(lctx, localInsts, exprTy)` to call `candidateTacticsCloseGoal`.  `simplifyTactics` runs in `CoreM` after the `(lctx, …)` context has been discarded, so doing it as a stage-3 syntactic rewrite would require re-plumbing the elaboration context through the simplifier — bigger surgery for the same effect.  Treat this as a stage-2 optimization that does what stage-3 conceptually wants.

**Impact**:
- Sum L55: was `apply Classical.byContradiction; intro hp; have hOr := …; cases hOr | inl h_1 => lia | inr h_1 => lia` (8 lines), now `apply Classical.byContradiction; intro hp; lia` (3 lines).  Speedup 0.93× → 0.96× of grind.
- Sum L81: same collapse.  0.98× → 1.13× of grind (now **faster** than grind on this case).
- Int L47/L91: indirect — the `by_cases h_abs` shape these emit isn't an `Or.casesOn`, so the Or-collapse doesn't fire.  Their dumps unchanged from the 2026-05-01 baseline.
- Sum L36/L70 / Int L69/L76/L79: unchanged (their cases-on shapes don't match the trigger gate).

Sum.lean still 4/4, Int.lean still 5/5, all 19 snapshot tests pass.  No new snapshot regression-lock added — the collapse only fires under the narrow gate, and all existing snapshot inputs either have non-`lia` branch bodies or no `useHaveWrapper`, so existing tests are an indirect lock against the gate going too wide.

### Done: byContradiction specialized-first dispatch (2026-05-01)

`tryDecompByContradiction` (in `Decompiler.lean`) used to recurse structurally into the contradiction body first, falling back to specialized handlers (and then arithmetic terminals) only if the structural attempt failed.  For grind-emitted contradiction bodies whose outer shape is a deeply-nested `Or.casesOn` tree but whose inner leaves all close via the same specialized handler (`tryDecompAbsCaseSplitContradiction`, `tryDecompFalseFromLia`), the structural recursion would emit ~50 lines of nested `cases hOr_N` with 6+ inner `lia` calls before the specialized handler fired at the leaves.

Reordered the dispatch in `tryDecompByContradiction` to four phases:
- **Phase A — specialized short-circuit** (NEW): try `trySpecializedDecompHandlers` directly on the body before any structural recursion.  If the candidate validates with the `apply Classical.byContradiction; intro h; <body>` wrapping, use it.  Lets `tryDecompAbsCaseSplitContradiction` and friends fire at the OUTER level instead of waiting until the inner branches.
- **Phase B — structural recursion** (was Phase A): unchanged, runs when no specialized handler matched.
- **Phase C — arithmetic terminal** (was Phase B): `lia` / `grind_order` / `grind_linarith` against the body.
- **Phase D — final fallback** (was Phase C): `validateOrExact` with structural recursion → exact term.

The state save/restore at error boundaries (the state-monad refactor's `let savedUsed ← getUsed; … set savedUsed`) was also threaded through Phase A so a failed specialized attempt doesn't leak names into Phase B.

**Impact on benchmarks**:
- Int L91: 0.640s → 0.063s — **10×** speedup, was 14× slower than grind, now 1.3× slower.
- Int L47: 0.109s → 0.054s — 2× speedup, was 3× slower than grind, now 1.2× slower.
- Other Int / Sum sites: 1.2×–1.5× speedup each.
- Range collapses from 0.07×–0.98× to **0.72×–0.98×** of grind.

Sum.lean still 4/4, Int.lean still 5/5, all 19 snapshot tests pass.  See "Performance Snapshot" above for the full table.

### Done: dev-cycle tooling (2026-05-01)

A pass on developer-experience pain points that surfaced during the previous batches' work.  No behavior change; new tooling all opt-in via options or scripts.

- **`scripts/probe.sh <file> <line> [maxHeartbeats]`**: wraps the workflow that previously took 5 manual steps when investigating a failing query — locate the dumped query file, copy to `/tmp`, inject `set_option maxHeartbeats N`, run `lake env lean` from `mathlib4/`, capture output.  Default heartbeat cap 8M (40× the default 200k file budget).
- **Mathlib module build cache in `nightly.py`**: when every target module's `.olean` is newer than its source `.lean`, skip the redundant `lake build Mathlib.X` invocation (which costs ~5–8s of lake startup overhead per nightly call even when nothing has changed).  Saves several seconds per iteration when the only edits are to lean-decomp itself.  Cache key is the per-module mtime comparison; lean-decomp source mtimes are NOT included because mathlib doesn't import lean-decomp.
- **`set_option trace.leanDecomp true`**: registers the `leanDecomp` trace class and adds a `tracedFirstSomeM` dispatcher in `Decompiler.lean` that logs `<HandlerName>: ✓` (matched and emitted) or `<HandlerName>: ·` (skipped) for every handler tried at every recursion point.  InfoView shows the full dispatch trail.  Replaces hand-instrumented `IO.println` / `dbg_trace` calls.
- **`set_option leanDecomp.dumpOnFail true`**: on validation failure, the macro writes the candidate tactics + simplified proof term + lctx to `/tmp/lean-decomp-debug-<timestamp>.{tac,proof,lctx}` and includes the path stem in the error message.  Replaces the "instrument the macro, build, run, revert" loop that previously took 10+ minutes per debugging session.
- **`showdecomp <term>` (tactic form)**: runs `<term>` through the simplifier + decompiler in the current goal context and prints the resulting tactic block as a message.  Doesn't validate or emit a `Try this` suggestion — strictly an inspection helper for "what does the decompiler produce on this shape?" without writing an `example := by decompile …` plus going through the full validation round-trip.  (Term-form `#showdecomp` deferred — `decompileExpr` runs in `DecompM = StateRefT _ TacticM` which the term elaborator doesn't naturally provide.)
- **`set_option leanDecomp.profile true`**: at the end of each `decompile` call, log per-stage wall-clock timing — `inner` (the wrapped tactic), `simplify`, `decomp`, `validate`, `emit`, `total`.  Pairs with the trace mode (which tells you *which* handlers fired) to get a "where did the time go" picture.  Per-handler breakdown intentionally not measured — would require state-monad plumbing of a `ProfileMap` for limited dev-cycle gain.
- **`leanDecomp.candidateMaxHeartbeats` option**: previously hardcoded at 100000; now exposed as a `set_option` so individual `decompile` calls can tune the speculative-validation cap without recompiling.
- **README "Debugging Playbook" rewrite**: now references all the new tooling with copy-pasteable examples for trace / profile / dump / probe / `--grind-line` workflows.

### Done: fvar-app handler collapse (2026-04-30, batch 4)

- **Deleted `tryDecompProblematicProofApp`** (`Decompiler.lean`, ~40 lines).  Phase 1 dispatch slot is now empty; fvar-headed apps with proof args fall through to `tryDecompTheoremAppFallback` at Phase 8.  Investigation showed `tryDecompTheoremAppFallback` was already handling fvar heads correctly when reached — the duplicate handler was preserved purely to make fvar-app dispatch happen at Phase 1 rather than Phase 8, which had no semantic effect (no Phase 2-7 handler matches fvar heads).
- **Generalized `tryDecompTheoremAppFallback`'s emission**.  Previously it always used `refine $delabTerm`.  Added the all-args-proof-like branch that emits `apply $head` instead — recovers the `apply h; · exact a; · exact b` shape that the old `tryDecompProblematicProofApp` produced (test 12, the `not_eq_prop` regression).
- **Test 4b** (new): fvar head + 2 proof args, regression-locks the fvar-app path through the unified `tryDecompTheoremAppFallback`.  Combined with Test 4 (fvar head + 1 proof arg, falls to `decompExact`) the two snapshots cover both branches of the gating logic.
- **Updated dispatch-list documentation** (`Decompiler.lean:317-`) to reflect that Phase 1 is now just `tryDecompExactLocalHyp` and Phase 8's `tryDecompTheoremAppFallback` handles both fvar and const heads.

Sum.lean still 4/4, Int.lean still 5/5, all 19 snapshot tests pass.

### Done: `used : List String` → state-monad refactor (2026-05-01)

Threading the used-name accumulator as an explicit parameter through every handler signature was a long-standing wart: ~30-40 functions across 6 files all carried `(used : List String)` as a parameter and returned `(_, List String)` tuples, and threading bugs (`used.length` vs `used1.length`) had been a recurring source of regressions.

Lifted into `DecompM := StateRefT (List String) TacticM` in `Helpers.lean`. Handler signatures are now `… → DecompM (Option (Array (TSyntax \`tactic)))` instead of `… → List String → TacticM (Option (Array (TSyntax \`tactic) × List String))`. Recursive calls drop the parameter and tuple — `let tactics ← decompileExpr expr lctx localInsts` instead of `let (tactics, used') ← decompileExpr expr lctx localInsts used`.

Key design points:
- **`getUsed` / `addUsed`** for read/write access to the accumulator. `addUsed` is no-op on duplicates (matches old `used.contains` guard).
- **`chooseIntroName (idx : Nat) (userName : Name) : DecompM String`** keeps the explicit `idx` parameter (rather than reading `(← getUsed).length` internally) because the historical naming behavior depends on per-batch position counters: two consecutive `_` binders in one `assignIntroNames` call get base names `x1`, `x2` (not `x1`, `x_{used.length}`) — preserving snapshot-test naming output. Singleton sites (`tryDecompByContradiction`, `tryDecompLet`) pass `(← getUsed).length`; `assignIntroNames` threads its own local `idx := 0, 1, 2, …` counter.
- **State save/restore at error boundaries**: `validateOrExact` saves the used-name list before calling `build`, restores it on either `subproofTacticsCloseGoal` failure or thrown exception. Same in `tryDecompByContradiction`'s catch arm. Without this, names introduced only in a failed branch would leak into subsequent handlers' name choices.
- **Entry point**: `ProofTermMacro.lean`'s `buildDecompiledTactics` now does `(decompileExpr proof lctx localInstances).run' []` to discard the final used-name state.

Affected files: `Helpers.lean`, `CasesOn.lean`, `EqDecomp.lean`, `Specialized.lean`, `Specialized/Grind.lean`, `Decompiler.lean`, `ProofTermMacro.lean`. Sum 4/4, Int 5/5, all 19 snapshot tests pass.

### Done: combinator + strategy + handler-split cleanup (2026-04-30, batch 3)

Continuation of the cleanup pass.  No behavior change (Sum 4/4, Int 5/5, all 18 tests pass).
- **Heartbeat option exposure**.  `candidateMaxHeartbeats` (`Helpers.lean`) is now `register_option leanDecomp.candidateMaxHeartbeats : Nat := { defValue := 100000, … }`.  Nightly / tests can tune the speculative-validation cap via `set_option leanDecomp.candidateMaxHeartbeats N` without recompiling.
- **`chooseExactStrategy` unified policy** (`Helpers.lean`).  The three fallback sites — `mkExactFallbackTactics` (validation-failure), `validateOrExact`'s catch arm, and `Decompiler.lean`'s `decompExact` (no-handler-matched) — interleave delab-vs-pp.all, decide-vs-with_unfolding_all-exact decisions differently.  Lifted into a single `chooseExactStrategy` parameterized by an `ExactStrategyConfig` record (`enforceMaxSize`, `tryDecideFirst`, `forcePrettyPrint : Expr → Bool`).  Each call site now passes its config.  Future tuning (e.g. always trying `decide`, or always pp.all-rendering propext) edits one function.
- **`matchConstApp?` combinator** (`Helpers.lean`).  Most `tryDecompXxx` handlers shared the boilerplate `let (fn, args) := peelArgs e; let some name := fn.constName? | return none; if name != ``Foo then return none; if args.length < N then return none`.  Added `matchConstApp? : Expr → Name → Nat → Option (List Expr)` so handlers become `let some args := matchConstApp? e ``Foo N | return none`.  Applied to 12 handlers across `Decompiler.lean` (Iff.intro/mp/mpr, And.intro/proj, propext), `EqDecomp.lean` (congr, congrArg, Eq.symm, Eq.trans, the two `*Congr` peelers), and `Specialized/Grind.lean` (Eq.mpAutomationCast, Eq.mpKnownGrindCast, Eq.mpIntLinearNormLe, mt).  Net: ~3 lines saved per handler and the *intent* — "match this shape" — is now visible at the top of each handler.
- **`tryDecompCasesOn` split** (`CasesOn.lean`).  340-line function broken up by extracting three named helpers, each with its own docstring:
  - `runMVarIdCases` (~20 lines): allocate a fresh synthetic-opaque mvar of `expr`'s type, generalize the discriminant if needed, run `MVarId.cases`, return subgoals.  Returns `none` for generalized motives so the caller falls back to the older `lambdaTelescope` path.
  - `cleanupEqMotiveTransport` (~40 lines): the load-bearing eq-motive substitution + `Eq.rec`/`Eq.ndrec` strip.  Documented why we strip only when the base is a lambda (would otherwise erase `noConfusion`'s const-headed `Eq.rec`).
  - `mkCasesWithAltsTactic` (~10 lines): final `cases <disc> with …` syntax build, with optional `cases h : <disc>` form for generalized-equation motives.
  Main `tryDecompCasesOn` body shrunk by ~70 lines and gained a docstring describing the three-phase per-branch flow (telescope → cleanup → recurse).

### Done: dispatch + simplifier + test cleanup (2026-04-30, batch 2)

Continuation of the cleanup pass.  No behavior change (Sum 4/4, Int 5/5, all 18 tests pass).
- **Documented `firstSomeM` dispatch** in `Decompiler.lean:363-450`. Annotated 8 phases (Pre / Binder-introducing / Specialized / Structural-propositional / Structural-equality / False / Term-shape / Terminal-arithmetic / Theorem-app fallback) with rationale for each ordering invariant. Swapping phases now obviously breaks correctness — e.g. the comment for Phase 4 spells out that `tryDecompEqMpForallCongr` MUST precede `tryDecompEqMp` so the L70/L36 fast path fires.
- **Added simplifier type-preservation invariant** in `Simplify.lean`. New `register_option leanDecomp.simplify.checkTypes` (default `false`) wraps every rule's output through `Meta.isDefEq oldTy newTy` and throws if the rule changed the proof term's type. This is the precise class of bug the old `Lean.Grind.of_eq_eq_true` rewrite had — it claimed to produce `a = b` but actually produced `Eq.mpr ... True.intro` of a different proposition. Smoke-tested at `set_option leanDecomp.simplify.checkTypes true` against all 18 snapshot tests; no current rules violate the invariant.
- **Refactored `collectFinsetMemRewrites`** (`Specialized/Grind.lean`). Three passes (proof-walk for direct `Iff.mp` hits, cross-product of found lemmas × target fvars, lctx scan) are now visually separated with section comments and share a single `pushRw` helper that handles `(lemma, hyp)` deduplication. The shared `emitted : HashSet (Name × Name)` accumulator makes the dedup invariant explicit (preventing the "rw lemma at hyp twice fails" bug that broke L70 in the first iteration).
- **Removed dead `extractGrindLemmaNames`** (30 lines, zero callers).
- **Modernized `isStructuralConst` / `isGrindConst`** in `Helpers.lean` to use `Name.isPrefixOf` against namespace literals (`Eq`, `Classical`, `Int.Linear`, `Lean.Grind`, `Lean.RArray`) where possible. Added comment explaining why `congr*` / `*_congr*` / `eq_true*` / `eq_false*` checks remain string-prefixed (root-namespace names with no shared parent).
- **Extracted `setInductionAltBinders`** in `CasesOn.lean`. The 40-line `Syntax.node` surgery that mutates an `inductionAltLHS`'s binder slot is now a named, documented helper instead of inline raw-syntax matching at the call site. The call site went from ~40 lines to one if-expression.
- **Reorganized `Test.lean`** into 6 sections grouped by handler (Smoke / byContradiction / Hypothesis-preferences / Specialized-grind / propext-Iff regression locks / forall_congr+implies_congr regression locks) with an introductory comment block. Tests 14–18 are now annotated as "regression locks" so future contributors know not to "fix the snapshot" without reading the relevant handler docstring.

### Done: utility consolidation pass (2026-04-30)

Code-review punch list found three utility duplicates and several dead files. Cleaned up in one pass with no behavior change (`Sum.lean` still 4/4, `Int.lean` still 5/5, all 18 snapshot tests still pass). Net: −410 lines.
- **Deleted dead files**: `BenchGrind.lean`, `casesonterm.lean`, `casesOnType.lean`, `IndentTest.lean`, `simpleterm` — orphan dump-output and unreferenced experiments.
- **Consolidated `peelArgs`** (was duplicated in `EqDecomp.lean` as `peelApps`, `CasesOn.lean`, and `Specialized/Grind.lean`) into the single `LeanDecomp.peelArgs` in `Helpers.lean`.
- **Consolidated `containsConstName` / `containsEagerReduce`** (3 copies each across `Decompiler.lean`, `EqDecomp.lean`, `Helpers.lean`) into the public `Helpers.lean` versions.
- **Consolidated `anonymizeSyntheticMVars` / `ppExprToTermSyntax` / `ppExprToTermSyntaxWith`** (duplicated between `Decompiler.lean` and `Helpers.lean`) into single public `Helpers.lean` versions.
- **Modernized `isBoolEqTrue`** in `Helpers.lean` to use `Expr.eq?` instead of an inline app-peeler.
- **Extracted `silentTry` helper** in `Helpers.lean` for the save-messages / suppress / try `withoutModifyingState` / catch / restore pattern shared by `subproofTacticsCloseGoal`, `refineTacProducesGoals`, and `refineTacMatchesProofArgs`.
- **Factored `tryDecompEqMpForallCongr` / `tryDecompEqMpImpliesCongr` clones**: extracted `emitHavePeel` in `EqDecomp.lean` for the shared `<introTacs>; have h := <ev>; <fast-path lia | recurse on Eq.mp eqProof h>` tail. Universal sub-cases pass `tryFastPath := false` (post-intro goal is still a `∀`, fast-path lia is a guaranteed miss); instantiated sub-cases pass `tryFastPath := true`. Cut ~80 lines and put the four sub-cases on equal footing.

### Done: lctx-based mem-rewrite scan in `collectFinsetMemRewrites` (2026-04-30)

Sum L36 was the last remaining nightly failure on `Sum.lean`. Investigation (instrumented `decompile` to dump the simplified proof term and per-phase markers to `/tmp`) showed the macro was running out of heartbeats inside `buildDecompiledTactics` rather than at validation time, with a single Eq.mp `refine` taking ~6.6s on the default 200k budget. Even 8M heartbeats wasn't enough.

Root cause was a coverage gap, not a perf problem: `collectFinsetMemRewrites` only emitted rewrites when the proof contained `Iff.mp Finset.mem_<X> <fvar>` directly. L36's proof references `mem_sdiff.mp (Eq.mp <transport> hp)` — the third arg is an Eq.mp expr, not a direct fvar — so Pass 1 missed it, and Pass 2's lemma-only set had no `targetFvars` to pair with. The `tryHavesPlusLia` candidate ended up being just `have h_fact := hs x …; lia`, which can't close False without the membership rewrites of `hp`.

Fix:
- Added a Pass 3 to `collectFinsetMemRewrites` (in `Specialized/Grind.lean`) that scans the **lctx** for hypotheses whose type matches a known Finset interval / sdiff constructor and emits `rw [Finset.mem_<X>] at <hyp>` (and `rw [Finset.mem_sdiff]` first when the set is `s \ Finset.<X> a b`). Resolves `set r := …` opaque fvars by looking through the let-binding.
- Made Pass 2 also insert into `foundPairs` so Pass 3 can dedupe against it — the duplicate `rw` on an already-rewritten hypothesis fails (LHS no longer matches), tanking the whole candidate. This was the bug that broke L70 in the first iteration.
- Added a defensive heartbeat bound on `candidateTacticsCloseGoal` (Helpers.lean) — speculative validation attempts now run with `maxHeartbeats := 100000` so a single pathological refine candidate cannot consume the entire ambient budget. `validateOrExact` / `subproofTacticsCloseGoal` directly remain unbounded (they're the workhorse final check).

**Result**: Sum.lean is now 4/4 (L36 was 3/4 before); Int.lean stays at 5/5. Sum L36 collapses to 8 lines: `intro x hp; apply Classical.byContradiction; intro hp_1; have h_fact := hs x …; have h_fact_1 : … := Int.not_le_eq …; rw [Finset.mem_sdiff] at hp; rw [Finset.mem_Ioc] at hp; lia`. Same shape as L70's working output, with the outer `intro x hp` reflecting that the user didn't pre-bind the loop variable.

### Done: `forall_congr` / `implies_congr` peelers in `EqDecomp.lean`

Two general (non-grind-specific) handlers that compose with the existing grind-specific leaf handler:

- **`tryDecompEqMpForallCongr`** matches `Eq.mp (forall_congr <body>) <evidence>` (with optional trailing applications). Two cases:
  - **Instantiated** (trailing args present, e.g. `… <ev> x mx`): emit `have h := <ev> x` and recurse on `Eq.mp (<body> x) h <remaining args>`. Fast path: if `lia` (or `with_unfolding_all lia`) closes the outer goal with the new `have` in the lctx, emit `have h := <ev> x; lia` directly — skipping the inner refine chain.
  - **Universal** (no trailing args, goal is `∀ a, q a`): emit `intro x; have h := <ev> x; <recurse>`.
- **`tryDecompEqMpImpliesCongr`** matches `Eq.mp (implies_congr p_eq q_eq) <evidence>` when `p_eq = Eq.refl`. Symmetric structure: instantiated case (trailing premise) emits `have h := <ev> hp; <recurse-or-lia>`; universal case emits `intro hp; have h := <ev> hp; <recurse>`.

Both handlers also added a `have` step so downstream `lia` sees the user-form hypothesis in the lctx — without it, the application is just an expression invisible to lia.

`tryDecompEqMpIntLinearNormLe` (in `Specialized/Grind.lean`) was extended with a `with_unfolding_all lia` fallback for cases where the goal is in polynomial-denote form (`Int.Linear.Poly.denote' … ≤ 0`) — happens when the leaf fires inside another peel.

**Result on Sum L70**: now passes inside the default 200k-heartbeat budget. The decompile collapses to 7 lines: `apply Classical.byContradiction; intro hp; have h_fact := hs x (And.left (Finset.mem_sdiff.mp mx)); have h_fact_1 : (¬c + ↑(#s) ≤ x) = (x + (1 : ℤ) ≤ c + ↑(#s)) := Int.not_le_eq …; rw [Finset.mem_sdiff] at mx; rw [Finset.mem_Ico] at mx; lia`. The peeler's `lia` fast path closes the contradiction body directly with `h_fact` in the lctx — no outer `refine @Eq.mp <prop1> <prop2> ?_ ?_` chain on `propext (Iff.intro …)` shapes is generated, so the per-refine ~6.5s unification cost the previous bottleneck depended on never fires.

### Done: `decide` swap in `mkExactFallbackTactics`

Implemented in `LeanDecomp/Helpers.lean`. When the proof contains `eagerReduce` AND its inferred type is `(_ : Bool) = (true : Bool)` (the certificate shape), try `decide` before `with_unfolding_all exact`. Validates with `subproofTacticsCloseGoal`; falls back if `decide` doesn't close. Defensive: doesn't fire on the L70 forall_congr block (whose outer type is `∀ ...`, not `Bool = true`), so it didn't directly unblock L70/L36 — the L70 win came from the `forall_congr`/`implies_congr` peelers rerouting through `lia` instead of through the certificate fallback at all. Kept as a defensive change for future grind proofs that emit literal certificate-shaped fallbacks.

## Recommended Next Steps (after the top TODO)

- **Extend the `MVarId.cases`-based per-branch decomp to generalized motives.** The current implementation falls back to a synthesized lctx when the casesOn motive carries a trailing `heq : disc = ctor xs` (i.e., proofs from `cases h : disc with`). The naive approach — `MVarId.generalize` with `hName?` to introduce both the abstracted fvar and the eq hyp, then `MVarId.cases`, then substitute `heq → real_eq_fvar` in the body — was tried and breaks `LeanDecomp.simple`: the old body's `Eq.rec` cleanup (substituting `heq → Eq.refl s` and stripping the resulting transport) turns out to be load-bearing for downstream handlers like `contradiction` and `noConfusion`, which consume the type-incorrect intermediate the cleanup produces. The right fix probably needs to either (a) keep the old cleanup but run the recursion in the new substituted lctx, or (b) drive the per-branch recursion through `evalTactic` of `cases h : disc with` syntax (using a synthetic outer mvar) so Lean's elaborator handles the transport natively. Multi-eq generalized motives (indexed inductive types) are a further extension.
<!-- forall_congr handler promoted to Top TODO. -->

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
- `mkExactFallbackTactics` (`Helpers.lean`): when an `eagerReduce` appears anywhere inside a fallback exact, try `decide` first if the inferred type is `(_ : Bool) = (true : Bool)` (the certificate shape); otherwise wrap the fallback in `with_unfolding_all exact <term>` so re-elaboration triggers the same unfolding. See "Done: `decide` swap in `mkExactFallbackTactics`" above.

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

Results (2026-04-30):
- `Mathlib/Algebra/Order/Group/Unbundled/Int.lean`: 5/5 (lines 47, 69, 76, 79, 91).
- `Mathlib/Algebra/Order/Group/Int/Sum.lean`: 4/4 (lines 36, 55, 70, 81).

Int L69 simplifies to `apply Classical.byContradiction; intro hp; lia`. L47/L76/L79/L91 decompile via byContradiction → outer `cases` over an `of_eq_eq_true`-shaped disjunction → inner `cases` of the resulting `And` → `tryDecompAbsCaseSplitContradiction` at each leaf. Sum L70 and L36 both collapse to byContradiction + `have h_fact := hs x …` + `rw [Finset.mem_sdiff, Finset.mem_<Ico|Ioc>] at hp` + `lia` via the lctx-based mem-rewrite scan + `tryDecompEqMpForallCongr` peeler (see "Done" above).

### Main Open Blockers

- **No stage-3 tactic simplifier.** Successful decompiles still contain `have hOr : ... := by lia; cases hOr with | inl ⟨..⟩ => ...` boilerplate.
- **Coverage of grind sites is still narrow.** Both nightly slices are deliberately small. Broader sweeps will surface new shapes the structural handlers don't cover yet.

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
- **Decompiler-side beta-reduction of `Eq.mp (Eq.symm? (propext (Iff.intro fwd bwd))) base → fwd/bwd base`, intended to skip the slow `refine @Eq.mp <T1> <T2> ?_ ?_` block on Sum L70.** Implemented as `tryDecompPropExtIffTransport` between `tryDecompEqSymm` and `tryDecompEqRecPropTransport`. The handler fired correctly on the OUTER propext-Iff transport, but the substituted body still contained an inner non-propext transport (a `Eq.symm (congr (congrArg And eq1) eq2)` chain over polynomial-form ANDs). The recursion's eventual `lia` calls couldn't close their goals from the substituted-form hypotheses, validation failed, and the entire block fell back to `with_unfolding_all exact <giant>` — strictly worse than the unsimplified path's structural `refine @Eq.mp + Eq.symm + propext + constructor + intro + ⟨_,_⟩ + rw + lia` chain. Lesson: collapsing a transport at decompile time breaks `lia`'s view of the hypotheses unless the *entire* transport chain (including non-propext congr links) collapses too. Reverted; the slow refine on L70 stands.
- **Generalizing `simplifyEqRecOfIdMotive` past `True`/`True.intro`** still hits `maximum recursion depth` on `LeanDecomp.Test` (test 7, the `n < 5 → n < 10` byContradiction shape). Gating by eq-proof head (`propext`/`Eq.symm`/`Eq.trans`/etc.) didn't help — the recursion-depth comes from somewhere downstream in the simplifier, not from a missing termination check on the new rule itself. Still on the Recommended Next Steps list as a target for a more careful generalization.

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

When iterating on a specific failing site, use `--grind-line` and `scripts/probe.sh`:

```bash
# Focused nightly: only the failing site, mathlib build is cached automatically.
python3 scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean \
  --treatment decompile --no-benchmark --grind-line 36 \
  --dump dump-nightly-sum --output results-nightly-sum.json

# Inspect a single failure with elevated heartbeats (auto-finds the dump,
# injects set_option maxHeartbeats 8000000, runs lake env lean):
scripts/probe.sh mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean 36
```

When changing decompilation behavior, use the trace / profile / dump tools to investigate:

```lean
-- See which handler fired at each recursion point
set_option trace.leanDecomp true in
example : … := by decompile grind

-- Stage-level wall-clock timing per call
set_option leanDecomp.profile true in
example : … := by decompile grind
-- → "decompile profile: inner=… simplify=… decomp=… validate=… emit=… total=…ms"

-- On validation failure, dump candidate tactics + simplified proof + lctx to /tmp
set_option leanDecomp.dumpOnFail true in
example : … := by decompile grind

-- Inspect what the decompiler produces for a specific subterm without going
-- through the full validate/emit pipeline:
example : … := by
  showdecomp (Eq.mp (forall_congr h_eq) h_uni a)
  sorry
```

Heartbeat-cap tuning when you suspect the speculative-validation budget is the bottleneck:

```lean
set_option leanDecomp.candidateMaxHeartbeats 200000 in  -- default 100000
example : … := by decompile grind
```

For Sum/Int failures, the most efficient workflow is:
- inspect the preserved `*.query.lean` file
- isolate the failing obligation into a smaller probe if needed (or use `scripts/probe.sh`)
- turn on `set_option trace.leanDecomp true` to see the dispatch path
- inspect the simplified proof shape (head: `Eq.rec`, `Eq.ndrec`, `Eq.mp`, `propext`, `congrArg`, `mt`, `Iff.mp`, `And.left`, `Or.casesOn`, `byContradiction`?)
- add the narrowest possible structural handler
- rebuild `LeanDecomp.Test`
- rerun only the affected nightly slice (with `--grind-line N`)

Where to make changes:
- proof-term normalization → `LeanDecomp/Simplify.lean`
- equality transport / congruence → `LeanDecomp/EqDecomp.lean`
- theorem-app structure / fallback behavior → `LeanDecomp/Decompiler.lean`
- grind-specific shapes → `LeanDecomp/Specialized/Grind.lean`
