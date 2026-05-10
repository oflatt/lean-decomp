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

### Coverage / handler work

1. **Order-grind handlers** for `Lean.Grind.Order.*` — analog to the existing `Int.Linear.*` arithmetic specialization in `Specialized/Grind.lean`.  Concrete starting case: `Mathlib/Order/Defs/LinearOrder.lean:158` (`min_assoc`).  Targeting these would replace the `grind only [<extracted>]` leaves currently used in Rat L83/L89/L97 (visible in `analyze.py shape dump-broader-order`) with cleaner structural emission.  See "On the order-grind family" in the deep-dive doc below.
2. **Investigate Rat L44 (too-large) and L142 (validate-fallback)**.  The two remaining Rat failures need different attacks than the 2026-05-09 grind-only fallback (which closed L83/L89/L97).  L44's `0 ≤ if true = true then …` shape needs case-split-then-grind-only.  L142's structural decomp doesn't get traction at all.
3. **Cross-version stability experiment** (paper headline).  Pick a grind-heavy mathlib file, decompile every grind site, then bump grind/Lean toolchain and count survivors.  Mining surfaced the anchor: `Mathlib/Algebra/ContinuedFractions/.../CorrectnessTerminating.lean:150` was reverted with `#adaptation_note` citing [lean4#9825](https://github.com/leanprover/lean4/issues/9825) — decompile-once should survive that regression.

### Refactoring / dev-loop (from 2026-05-09 deep-dive review)

The deep-dive surfaced 10 concerns; the user accepted these for action (#8/#9 declined, #4 deferred).  Order is "smallest cost first":

4. **Add snapshot tests broadly** + lock dispatch order (concern #5).  *Done 2026-05-09 PM*: 20 → 25 snapshot tests via §8 (AndProj / EqSymm / IffMpMpr / EqRefl / EagerReduce / TheoremAppFallback const-head); Tests 12 and 16 docstrings strengthened with explicit dispatch-order claims.  Remaining shapes (`tryDecompFalseRec`, `tryDecompFalseType`) are hard to trigger in isolation because Phase 2 `tryDecompCasesOn` claims most synthetic False-elimination shapes first; deferred — the Sum/Int nightly slice exercises both paths.
5. **Cheap shape-checks in `tryDecompByContradiction` phases** (concern #2).  *Done 2026-05-09 PM* — the recomputation issue was specifically Phase B → Phase D rerunning the same `decompileExpr`.  Fixed by caching Phase B's body tactics for Phase D reuse.  See Done section.  Phase C's arithmetic shape-check was already in place at `Decompiler.lean:145`.
6. **Split the `Decompiler.lean` mutual block** (concern #10).  *Done 2026-05-09 EOD* — `tryDecompIntro` → `LeanDecomp/Intro.lean`, `tryDecompByContradiction` → `LeanDecomp/ByContradiction.lean`, and the arith-terminal helper cluster → `LeanDecomp/Helpers/ArithTerminal.lean`.  Decompiler.lean: 823 → 677 lines.  See Done section.
7. **Stage-3 dead-`have` elimination** (concern #7).  *Implemented 2026-05-09 EOD; gated off by default 2026-05-10* — pass is correct but per-have validation regresses broader-corpus by +11 wall-clock timeouts.  Lives behind `set_option leanDecomp.eliminateDeadHaves true`.  Future work: tighten the cost model so it can be on by default (skip validation when the closing tactic dominates the seq, etc.).  See Done section.

### Documentation

8. **Document the supported envelope.** The decompiler ships with a stable list of structural handlers (see *What Is Working* below) and grind-specific specializations (see `Specialized/Grind.lean`). A short "what shapes do we handle" table near the top of the README would make it easier to predict whether a new failure is in scope.

### Acknowledged but punted

- **Concern #3 (`validateOrExact` cumulative cost)** — `analyze.py shape` (added 2026-05-09 PM) already gives us per-file fallback-shape counts; iterate on actual data rather than instrumenting via Lean code.
- **Concern #4 (generalized cases motives)** — research item.  Current path silently degrades to `exact`; documented in "Recommended Next Steps".
- **Concern #6 (grind only output policy)** — clarified in code comments / Done section; doc-only.
- **Concern #8 (CSE / sub-proof sharing)** — declined as speculative without measurement.  `analyze.py shape` would surface the symptom first.
- **Concern #9 (two-tier heartbeats)** — declined.
- **Stage-3 simplifier residual** — only the "abs case-split-bound `lia`" remainder; not a paper-blocker.

## Long-term plan / Paper framing

Goal: a paper on decompiling Lean proofs as a way to get **simpler, more stable, and (ideally) faster** proofs out of opaque automation tactics. Phased to land each artifact a paper would need.

- **Phase 1 — close the speed gap (next ~2 weeks).** Ship the stage-3 tactic simplifier. Target: Int L91 from 0.640s to under 0.1s. Goal threshold: decompile within 2× of grind on grind-success cases on both nightly slices. Without this we cannot say "comparable on success, much better elsewhere" — the comparison story has to start with parity.
- **Phase 2 — find the wins (~4 weeks).** Expand `mine_grind_history.py` to surface grind sites that historically took >1s or timed out. Decompile each. Bin results into qualitative wins (grind fails, decompile closes) and quantitative wins (≥10× speedup). These are the paper's empirical anchors.
- **Phase 3 — robustness experiment (~6 weeks).** Cross-version stability comparison: pin a mathlib file, decompile every grind, bump grind / Lean toolchain, count survivors on each side. If decompiled proofs are more stable than grind invocations across versions, that's the paper's headline. Lock the methodology before running the experiment so we don't p-hack.
- **Phase 4 — generality (~8 weeks, parallel with refactors).** Extend coverage beyond grind: `omega`, `polyrith`, `linarith`, `norm_num`. Each tactic has its own certificate shape; one paper subsection each. The structural handlers (`Eq.mp`, `casesOn`, `propext`, etc.) are general — most of the work is per-tactic specializer modules under `Specialized/`.
- **Phase 5 — paper writing.** Outline: motivation (opaque automation, broken-after-grind-bumps proofs); approach (3-stage pipeline: term simplify → term-to-tactic → tactic simplify); specialization (per-tactic certificate handlers); evaluation (mathlib coverage %, head-to-head speed, cross-version stability); limitations (heartbeat-bounded recursion, generalized cases motives, etc.).

## Performance Snapshot (2026-05-01 baseline, validated within noise 2026-05-04)

Benchmarks via `scripts/nightly.py --runs 3 --warmup 1 --treatment {original,decompile}`. Times are cumulative `tactic execution` seconds at default heartbeat budget; "speedup" is (original / decompile).  Note: 2026-05-04 spot-checks reproduced these numbers within ±20% (noise is dominated by competing CPU load — a Friday `lean` orphan pile-up was caught and cleaned up; see Done section).  No re-baseline needed.

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

## Broader corpus coverage (2026-05-09 PM, post-cleanup re-sweep)

Re-ran `nightly.py --parallel 4 --runs 3 --warmup 1` across all of `Mathlib/Algebra/Order/`.  After today's cleanup pass (Helpers split + dead code removal): **26/42 = 62%** (up from 23/49 = 47% on 2026-05-05; AM run was 27/45 = 60%).  Site count drift (45→42) is the bench_grind regex catching slightly different `@[grind =]` attribute filtering across runs; coverage RATE moved up.  Sweep took ~17 min; zero stray processes.  Results in `results-broader-order.json`.

Decompile-treatment failure breakdown (n=16):

| Cluster | 2026-05-09 PM | 2026-05-05 | Δ | Notes |
|-|-|-|-|-|
| Wall-clock-timeout | 9 | 10 | -1 | Mostly file-load slowness; not a decompile bug. |
| Heartbeat | 4 | 5 | -1 | One site now passes (likely the cleanup made some validation faster). |
| Validate-fallback | 1 | 5 | **-4** | **Closed by 2026-05-09 grind-only fallback.** |
| Other | 0 | 5 | **-5** | **Closed by grind-only fallback (most were leaf-shape sites that now compile via `grind only [<extracted>]`).** |
| Parse-error | 1 | 1 | 0 | Edge case in attribute-skip detection. |
| Too-large | 1 | 1 | 0 | `Rat.lean:44` — case-split-bound shape; one-shot `grind only` can't compress. |
| Cross-file inst✝ | 0 | 0 | 0 | Closed in earlier sweeps. |

**Where the +4 sites came from**: every gain is in the `grind only [<extracted-user-lemmas>]` fallback path (added 2026-05-09).  Sites that previously fell through to a giant `with_unfolding_all exact <whole-proof>` now compile to a compact tactic block whose innermost leaves use `grind only [<lemma1>, <lemma2>]` extracted from the proof term itself.  Concrete examples: `Rat.lean:83/89/97`, `Group/Finset.lean:599` (locally), and a handful of others in the Order folder.

`scripts/analyze.py bucket` now defaults to `--treatment decompile` to avoid mixing in benchmark-treatment failures (`grindscript`/`grindonly`) that have their own non-decomp-related failure modes.  Pass `--treatment all` for the unfiltered view.
**Top remaining clusters by leverage**:
1. **Wall-clock-timeout (9)** — mostly file-load slowness for `Antidiag/*`, `Field/Basic`, etc.; not a decompile bug per se but blocks coverage.
2. **Heartbeat (5)** — per-call budget exhaustion in speculative validation.  Heterogeneous; investigate one at a time.
3. **Order-grind cluster (long tail)** — `Lean.Grind.Order.*` shape sites that decompiled successfully via the new grind-only fallback may still have non-ideal output (lots of `grind only [...]` at leaves vs cleaner structural).  The compactness story can be improved with `Specialized/Grind/Order.lean` handlers, but the COVERAGE story is now closed for these.

`min_assoc` from `Mathlib/Order/Defs/LinearOrder.lean:158` was the historical "replaced with manual proof" case — our decompile previously produced a 112-line tactic block.  After 2026-05-09's grind-only fallback, leaves like `exact <Eq.trans …>` over `Lean.Grind.Order.le_eq_false_of_lt` are likely now `grind only [<extracted>]`-shaped instead.


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

### Done: stage-3 dead-`have` elimination — opt-in only (2026-05-09 EOD → 2026-05-10, concern #7)

Implemented as a new pass in `LeanDecomp/TacticSimplify.lean` and gated behind `register_option leanDecomp.eliminateDeadHaves` (**default `false`**):

- **`extractHaveBinderName`** — detects `have h := X` / `have h : T := X` (term-RHS forms; `by`-RHS forms are already collapsed by the existing `simplifyTactic` to term-RHS).
- **`referencesName`** — recursive ident-match over a syntax tree.  Conservative: a destructuring pattern that rebinds the same name still counts as a reference, so we never drop a live have.
- **`eliminateDeadHavesAux`** — recursive walk; for each candidate, checks textual liveness, then validates the remaining tactic sequence via `LeanDecomp.candidateTacticsCloseGoal` (heartbeat-capped at 100k).  If validation passes, drops the have and re-checks from the same index.
- **`eliminateDeadHaves`** — entry point.  Called from `buildDecompiledTactics` between `simplifyTactics` and the inaccessible-name sanitizer.  No-op when the option is off.

**Why opt-in**: the pass is *correct* (validation guards correctness) and produces real improvements (Test 17's `have h := h_imp hp; lia` → just `lia` was the first catch).  But the per-have validation cost compounds on heartbeat-bound nightly sites — the 2026-05-09 broader-corpus measurement regressed from 26/42 → 20/45 (+11 wall-clock timeouts) when the pass ran on every `decompile` call.  Default-off lets users enable it in interactive sessions where output quality matters more than per-call cost; the code stays in tree for future investigation (e.g., a tighter cost model that skips validation when the seq is dominated by a single closing tactic).

**Scope**: top-level array only — focused subgoal blocks (`· …`) aren't walked because their lctx isn't available at simplification time.

### Done: split Decompiler.lean mutual block (2026-05-09 EOD, concern #10)

Closed Top TODO #6.  Extracted three modules from `LeanDecomp/Decompiler.lean`:
- **`LeanDecomp/Intro.lean`** (28 lines) — `tryDecompIntro` with `decompileExpr : DecompileCallback` parameter.
- **`LeanDecomp/ByContradiction.lean`** (100 lines) — `tryDecompByContradiction` with the same callback.  Imports `LeanDecomp.Helpers.ArithTerminal` and `LeanDecomp.Specialized` for the cross-handler dependencies.
- **`LeanDecomp/Helpers/ArithTerminal.lean`** (60 lines) — five helpers (`containsArithRelevantConst`, `containsArithmeticAutomationConst`, `isArithmeticLikeGoal`, `tryValidatedTerminalTactic`, `tryDecompArithmeticTerminalPasses`) that were `private` to `Decompiler.lean` but now need to be visible to `ByContradiction.lean`.  Promoted from `private def` to `def`.

`Decompiler.lean` shrank **823 → 677 lines** (-146).  Mutual block went from **11 → 9 partial defs**.  Each handler change in `Intro.lean` / `ByContradiction.lean` now recompiles only that file (~6.5s each) instead of the whole `Decompiler.lean` mutual block.  Build clean (`lake build LeanDecomp.Test` 17 jobs); smoke clean.

**Pattern**: same as `LeanDecomp/CasesOn.lean` — handlers that recurse pass `decompileExpr` as a parameter rather than referencing it through the mutual block.  The remaining mutual-block handlers (`tryDecompBetaRedex`, `tryDecompLet`, etc.) all genuinely need recursion-into-decompileExpr OR are tightly coupled to `decompExact`; they stay where they are.

### Done: byContradiction Phase B/D dedup (2026-05-09 PM, concern #2)

Closed Top TODO #5 with a small surgical change in `tryDecompByContradiction` (`Decompiler.lean:494`).  Phase B (`decompileExpr` + tight `candidateTacticsCloseGoal` validation, capped at `candidateMaxHeartbeats` = 100k) and Phase D (`validateOrExact` re-running the *same* `decompileExpr` under looser `subproofTacticsCloseGoal` validation, no heartbeat cap) used to recompute identical body tactics back-to-back.  Now Phase B caches its body tactics into `phaseBBodyTactics : Option (Array (TSyntax \`tactic))`; Phase D's `validateOrExact` build reuses the cache when present and only recomputes when Phase B threw.

**Why this is safe**: the cached `TSyntax` is pure data (no mutable state).  Phase B's `set savedUsed` restores name state to its pre-Phase-B snapshot, so a hypothetical Phase D recompute would start from the same state as Phase B and produce identical syntax — caching gives the same result with one fewer compute.  Phase D's looser validation still gets its second-chance shot at heartbeat-starved candidates.

**Why this matters**: contradiction bodies in Sum/Int/Rat regularly hit Phase D (the structural decomp produces a candidate that's tactically correct but exceeds 100k heartbeats during validation).  Each duplicated decompileExpr call was burning the full body-decompile cost.  Smoke clean post-change (Sum 4/4, Int 5/5, list 1/1).

### Done: §8 structural-handler snapshot tests + dispatch-order locks + IffMpMpr fix (2026-05-09 PM)

Filled coverage gap from the deep-dive #5: handlers that fire deep in dispatch and rarely show up in nightly snapshots had no regression locks.  Added a §8 section to `LeanDecomp/Test.lean` with five structural-handler smoke tests:
- **Test 20** — `tryDecompAndProj` on `And.left h` (locks the 3-arg shape; the applied-to-extra-args case correctly falls through).
- **Test 21** — `tryDecompEqSymm` on `Eq.symm h` (locks `refine Eq.symm ?_` shape).
- **Test 22** — `tryDecompIffMpMpr` on `Iff.mp h hp` (locks `refine @Iff.mp P Q ?_ ?_` shape, post concern #11 fix).
- **Test 23** — `tryDecompEqRefl` on `@Eq.refl Nat 1` (locks `Eq.refl → rfl` rewrite).
- **Test 24** — `tryDecompEagerReduce` on `eagerReduce (Eq.refl true)` (locks the Phase 6 `eagerReduce → decide` rewrite that real grind certificates rely on).
- **Test 25** — `tryDecompTheoremAppFallback` const head, mixed proof / non-proof args, no typeclass binders.  Test 19 covers the same path with a sanitizer rewrite; Test 25 locks the no-sanitizer baseline.

Also strengthened **Test 16's** and **Test 12's** docstrings with explicit dispatch-order claims:
- Test 16 — the `tryDecompEqMpForallCongr` MUST-precede `tryDecompEqMp` invariant (Phase 4 internal order).  Points at `Decompiler.lean:360`.
- Test 12 — the `trySpecializedDecompHandlers` (Phase 3) MUST-precede `tryDecompEqMp` (Phase 4) invariant.  Points at `Decompiler.lean:351`.

**Concern #11 fix in the same pass**: `tryDecompIffMpMpr` was emitting `refine Iff.mp ?_ ?_` without `@`-prefix or explicit type args, which fails synthetic re-elab because `?P, ?Q` can't be inferred before the holes are filled.  Changed emit shape to `refine @Iff.mp P Q ?_ ?_` (matches the `*Congr` peelers' style — see `EqDecomp.lean:306` for the established pattern).  Real grind output worked before via context, but the handler is now robust to isolated use as well.

**Test count: 20 → 25.**  Build clean (`lake build LeanDecomp.Test` 851ms).  Smoke clean (build / int / sum / list — all pass).

### Done: pre-flight `⋯` detection (2026-05-06)

Defensive forward-looking check in `checkDecompiled` (`ProofTermMacro.lean`): scan the formatted `tacticStr` for U+22EF (`⋯`, MIDLINE HORIZONTAL ELLIPSIS) BEFORE `evalTactic`.  If present, fail fast with a specific diagnostic ("decompile output contains the `⋯` truncation marker; route through `LeanDecomp.delabRefinable` / `LeanDecomp.ppTacticFull` …") instead of letting Lean bubble up an opaque "internal exception #5" with no actionable info.

**Why**: the L599 investigation (2026-05-04 / 2026-05-06) burned hours diagnosing what `internal exception #5` meant before identifying it was a parser-level rejection of `⋯`.  A future delab/format call site added without going through the wrappers would re-trigger the same multi-hour debugging.  The substring scan is O(n) on the rendered string (already produced for the error message), so cost is negligible.

`liftPPTruncationOptions` is now public so the diagnostic's suggested fix is actionable from anywhere.  In normal operation the diagnostic never fires — it's a guard against future regressions, not a behavior change.

### Done: route all delab through `delabRefinable` + lift `pp.maxSteps` (2026-05-06)

Followed up on yesterday's resume marker option (A) — thread the option lift through ALL `delabToRefinableSyntax` call sites.  Implementation: introduced **two single-source helpers** in `Helpers.lean`:

- `liftPPTruncationOptions : Lean.Options → Lean.Options` — lifts THREE truncation options (not two — yesterday's analysis missed `pp.maxSteps`).
- `delabRefinable : Expr → MetaM Term` — wraps `delabToRefinableSyntax` with the lift.
- `ppTacticFull : TSyntax → CoreM Format` — wraps `PrettyPrinter.ppTactic` with the lift, used at every `tacticSeq → string` site in `ProofTermMacro.lean`.

Then renamed every `delabToRefinableSyntax` call across `CasesOn.lean`, `EqDecomp.lean`, `Decompiler.lean`, `Specialized/Grind.lean` (plus the two fully-qualified `Lean.Meta.Tactic.TryThis.delabToRefinableSyntax` uses) to `delabRefinable`.  Removed the per-file `open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)` (replaced with `open LeanDecomp (delabRefinable)` where appropriate, or just a comment pointer).  The local `delabFull` previously inside `chooseExactStrategy` is now redundant — replaced with `delabRefinable`.

**The third option was the real culprit (`pp.maxSteps`)**.  Yesterday I lifted only `pp.deepTerms` and `pp.proofs` — neither helped L599.  Today's investigation: `pp.maxSteps` defaults to **5000** and tracks visited-expression count globally during a single format.  Large proof terms exhaust this budget mid-print, causing tail truncation as `⋯`.  L599's binder annotation `(h_2 : ⋯)` was elided BECAUSE the counter ran out before the binder, not because of depth or proof-elision.  Critically: `pp.all := true` does NOT lift `pp.maxSteps`, so even the `ppExprToTermSyntaxWith _ true` path was producing `⋯` for L599-sized proofs.  Lifted `pp.maxSteps := 1000000` in BOTH `ppExprToTermSyntaxWith` and `delabRefinable`/`ppTacticFull` via `liftPPTruncationOptions`.

**Validation on L599**: previously the failure was `unexpected '⋯'` style "internal exception #5".  Now the failure mode CHANGES — `decompile failed: generated proof too large (127738 chars, max 20000)`.  The fallback `exact <giant>` is now produced in full (127KB!), exceeding the macro's 20KB sanity guard.  This is a **correct** failure: the truncation was hiding a "proof is genuinely massive" issue.  L599's real fix would be either an order-grind handler that decomposes the giant fallback, or raising the 20KB threshold + adding a real exact-emission strategy that's more readable.  Either way, "the suggestion has `⋯` and crashes the parser" is no longer the failure mode.

**Other affected sites** (potential gains, not yet validated): every nightly query that previously failed validation due to `⋯` in any rendered output should now either succeed or fail with a more informative error.  Re-running the broader-corpus is Top TODO #1.

### Done: dev-loop tooling pass — probe.sh, analyze.py, smoke.sh, parallel sweep (2026-05-05/06)

Per the dev-loop priorities surfaced 2026-05-05:

1. **`scripts/probe.sh`** extended: accepts any `--dump <dir>` (default searches all `dump-*` dirs, was hardcoded to `dump-nightly-*`).  Also added `--profile` and `--dumpOnFail` flags for one-shot diagnostic injection.
2. **`scripts/analyze.py`** (new): `bucket RESULTS_JSON [DUMP_ROOT]` prints per-cluster failure breakdown; `diff OLD NEW` shows fixed/regressed/persistent (with shape-changed callouts) between sweeps.  Replaces the ad-hoc Python I was writing inline every analysis.
3. **`scripts/smoke.sh`** (new): runs `lake build` + Sum slice + Int slice + Group/List L234 cross-file.  Sequential mathlib setup once upfront, then Sum/List in parallel via `--skip-mathlib-setup`.  **80s sequential → 16s parallel**.  Catches >95% of regressions.  Includes orphan-process check at end.
4. **`nightly.py --parallel N`** (new): outer-loop parallelization via `concurrent.futures.ThreadPoolExecutor`.  Each worker uses its own `BenchDB` (SQLite in-memory dbs aren't thread-safe), merged at the end.  `LEAN_DECOMP_INNER_WORKERS` env var caps inner per-file parallelism to `cpu_count // N` so total concurrent `lean` processes stay around `cpu_count`.  Process-group cleanup from 2026-05-04 handles per-child orphans correctly under parallel load.  Verified launches 11 properly-parented `lean Mathlib/...` processes; no orphans after kill.
5. **`nightly.py --skip-mathlib-setup`** (new, supporting #3 + #4): skips the `git checkout` / `git clean` / `lake update` block in `ensure_mathlib`.  Required because parallel invocations otherwise race on `.git/index.lock`.  Caller is responsible for one-shot setup.
6. **`bench_grind.py` attribute false-positive fix (yesterday morning, 2026-05-05)**: `GRIND_RE` was matching `grind` inside `@[simp, grind =]` *attribute* declarations.  Added `ATTR_RE` and `GRIND_ATTR_EQ_RE` skip checks.  Re-baselined corpus from 54 → 49 actual grind tactic sites.

### Done: `scripts/analyze.py shape` subcommand (2026-05-09 PM)

Out-of-band detector for fallback-shape patterns in dumped suggestions.  Walks `*.decompile.lean` files in a dump dir, counts three patterns:
- `with_unfolding_all_exact` — fallback giant exact with eagerReduce wrapper.
- `grind_only_leaf` — `grind only [...]` at a leaf (the 2026-05-09 fallback).
- `big_exact` — `exact <multi-line term>` over 500 chars.

Per-file report sorted by total fallback count.  Run on `dump-broader-order` to identify candidate sites for handler work without instrumenting the Lean code.

Replaced an earlier sketch of an in-Lean `fallbackCounter` (concern #3 from the deep-dive) — out-of-band detection is lighter and works on existing dump artifacts.

```
$ python3 scripts/analyze.py shape dump-broader-order
Scanned 26 *.decompile.lean files under dump-broader-order.
Total fallback-shape occurrences:
     2  with_unfolding_all_exact
    10  grind_only_leaf
     2  big_exact
Per-file (top 6 by total fallback count):
    4  Mathlib/Algebra/Order/Ring/Int/L58.decompile.lean  (with_unfolding_all_exact=1, grind_only_leaf=2, big_exact=1)
    3  Mathlib/Algebra/Order/Ring/Unbundled/Rat/L83.decompile.lean  (grind_only_leaf=3)
    ...
```

### Done: cleanup pass — `Helpers.lean` split + dead code removal (2026-05-09 PM)

Code review surfaced three concerns; fixed all three.

1. **Removed dead helpers from failed investigations**:
   - `renameInaccessibleHyps` + `replaceInaccessibleRefs` (`Helpers.lean`, ~50 lines).  Wired into `chooseExactStrategy` then reverted because it hung L216.  Documented in earlier "Investigation: rename_i fallback" entry.
   - `tryDecompFalseFromOrderGrind` + `containsOrderUnsatLemma` + `orderGrindLeafMaxNodes` (`Specialized/Grind.lean`, ~50 lines).  Defined but commented out of dispatch list because it regressed L89/L97 to wall-clock-timeout.
   - The `renamePrefix` plumbing in `chooseExactStrategy` (initialized to `#[]`, never populated post-revert).
2. **Split `Helpers.lean` (855 → 637 lines) into three files**:
   - `Helpers/PP.lean` (92 lines): delab + ppTactic wrappers (`anonymizeSyntheticMVars`, `ppExprToTermSyntax`, `ppExprToTermSyntaxWith`, `liftPPTruncationOptions`, `delabRefinable`, `ppTacticFull`).
   - `Helpers/Sanitizer.lean` (81 lines): inaccessible-name handling (`isInaccessibleName`, `sanitizeInaccessibleIdents`).
   - `Helpers.lean` (slimmed): kept the genuinely-shared primitives — DecompM monad, validation infrastructure, naming helpers, exact-strategy chooser, common Expr utilities.
   - `Helpers.lean` re-exports the sub-files via `import` so external consumers (`CasesOn`, `Decompiler`, `EqDecomp`, `Specialized/Grind`) didn't need any changes.
3. **Trimmed verbose research-log comments** in `CasesOn.lean` (the "what we tried with `MVarId.generalize` and why it broke `LeanDecomp.simple`" block — the fact and the pointer to README are kept; the multi-paragraph rationale moved out of the hot path).

**Validation**: lake build 35/35 (was 31; +4 from new sub-files getting their own targets).  Smoke 4/4 (Sum, Int, List, build) clean.  Broader-corpus re-sweep: **26/42 = 62%** (vs 27/45 = 60% pre-cleanup; small site-count drift from bench_grind regex; coverage rate moved up).  Heartbeat cluster dropped 5 → 4 (one site now passes — possibly because something in the cleanup made an inner validation cheaper).

**Deferred** (per the original review, lower priority): splitting `Specialized/Grind.lean` into Structural vs Cert sub-files.  At 800 lines but still cohesive; revisit if it crosses 1000.

### Done: too-large escape hatch via `chooseExactStrategy` (2026-05-10, infra only)

Added a fallback in `ProofTermMacro.lean` after the 20KB max-size check: when the structural decomp produces output > 20KB, retry `chooseExactStrategy` on the whole simplified proof.  This triggers the `grind only [<extracted>]` attempt at the WHOLE-proof level — when the compressed form fits AND validates, emit it instead of erroring.

**Coverage win**: zero new sites today.  Tested on:
- `Mathlib/Algebra/Order/Ring/Unbundled/Rat.lean:44` (the targeted case): the compressed form is the SAME 34KB (the goal `0 ≤ if true = true then normalize … else …` requires `cases` on `s : Bool` to make progress; one-shot `grind only [<extracted>]` doesn't compress because the goal isn't directly grind-closable without the case split).  Stays "too-large".
- `Mathlib/Algebra/Order/Ring/Unbundled/Rat.lean:142` (validate-fallback): structural decomp doesn't get traction at all; the new escape doesn't help.  Stays failing.
- `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:599`: structural decomp now passes LOCAL validation (was failing before) — but cross-file re-elaboration fails with "typeclass instance problem is stuck: Singleton α ?m.143".  Some metavariable in the goal isn't fully determined.  Different failure mode; not addressed here.
- `Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean:216`: hits `(deterministic) timeout at delab` (the giant proof's delaboration overruns 200k heartbeats during the rendering pass).  Different shape; not addressed.

**Kept in tree** because the escape hatch is correct infrastructure: smoke 4/4 unaffected, no regressions, and any future case where structural-decomp-but-too-large overlaps with grind-only-can-compress will benefit automatically.

### Done: `grind only [<extracted>]` last-resort fallback (2026-05-09)

**Coverage win**: Rat 0/5 → **3/5** on `Mathlib/Algebra/Order/Ring/Unbundled/Rat.lean` (L83, L89, L97 now pass cross-file).  L142 (validate-fallback) and L44 (too-large) still fail.  Smoke green throughout (Sum 4/4, Int 5/5, List 1/1, build OK).  Zero stray processes.

**The fix**: in `chooseExactStrategy` (`Helpers.lean`), before emitting the giant `(with_unfolding_all)? exact <giant>` fallback, try `grind only [<extracted-user-lemmas>]` first.  The lemma list is collected from the proof term itself by `extractGrindOnlyLemmas` — these are the user-form lemmas grind picked up during proof search (e.g. `Rat.mkRat_pos_iff`, `Int.not_le_eq`).  When the extracted-lemma `grind only` validates locally, we emit it; otherwise fall through to the existing exact emission.

The output shape: structural decomp wins for everything that decomposes cleanly, with `grind only [<extracted>]` ONLY at leaf positions where the structural recursion can't make progress.  Concrete L89 emission:

```lean
apply Classical.byContradiction
intro hp
have hOr : … := by lia
cases hOr with
| inl h_1 =>
    cases h_1 with
    | intro left =>
      refine False.elim ?_
      · refine @Lean.Grind.Order.lt_unsat_k ℚ … ?_ ?_ ?_ ?_
        · exact Lean.Grind.instLawfulOrderLTRat
        · exact instIsPreorder_mathlib
        · exact Lean.Grind.instOrderedRingRat
        · decide
        · refine …
            · grind only [mkRat, Rat.mkRat_pos_iff, Int.not_le_eq]   -- ← here
        ...
```

Most of the proof is structural; `grind only` appears only at the (formerly opaque) order-grind leaves.

**`extractGrindOnlyLemmas` filter**: after a tightening pass, rejects (a) grind-internal namespaces (`Lean.Grind.*`, `Lean.Omega.*`, `Int.Linear.*`, `Lean.RArray.*`, `Lean.Parser.*`, `Lean.Elab.*`, `Lean.Meta.*`); (b) names with components starting `inst` (typeclass instances like `Rat.instLT`, `instOfNatNat`, `instIsPreorder_mathlib`) or starting `to` (typeclass projections like `PartialOrder.toPreorder`); (c) a small list of structural primitives + operator/literal classes.  Without the `inst*`/`to*` filter, lists ballooned to 37 lemmas of mostly typeclass instance noise; with it, lists are typically 1–3 user lemmas plus 1–2 type/constructor names.

**Policy note**: this is the deliberate relax of the "no `grind` in output" policy, scoped to `grind only [<extracted>]` AS A LAST RESORT.  Bare `grind` (with grind's automatic lemma discovery) is still forbidden.  `grind only [...]` is meaningfully different: the lemma list is fixed at decompile time, so the output is stable across grind-internal changes (grind's automatic lemma instantiation can shift between versions; an explicit `only [...]` list cannot).  Order: structural handlers → specialized handlers → terminal arithmetic (`lia`/`decide`) → **`grind only [<extracted>]`** → giant `(with_unfolding_all)? exact <whole>`.

**Limitation**: 100k-node walk cap in `extractGrindOnlyLemmas` (was 5k initially — too small; the L89 proof is ~13k nodes and `mkRat_pos_iff` appears past the 5k mark).  100k is enough for typical mathlib proofs while bounding worst-case time.

### Investigations that didn't ship (Rat / order-grind cluster)

Three attempts in 2026-05-07 / 2026-05-08 to crack the `Mathlib/Algebra/Order/Ring/Unbundled/Rat.lean` failures.  None shipped a coverage win.  The unifying lesson is in the resume-marker archive ("piecewise interventions on the order-grind family don't compose"); summaries below for posterity.

- **`Lean.Grind.Order.eq_mp` simplifier rewrite (2026-05-08)** — added rewrites in `Simplify/Grind.lean` for `Order.eq_mp p q h₁ h₂ → Eq.mp h₁ h₂` so the existing peeler chain could handle them.  Fired correctly (post-rewrite proof had 0 `Order.eq_mp` references) but Rat 0/5 unchanged because the surrounding `eq_trans_true` / `le_eq_true_of_lt_k` / `CommRing.le_norm_expr` wrappers are still opaque.  **Reverted.**
- **`tryDecompFalseFromOrderGrind` leaf handler (2026-05-07 PM)** — added in `Specialized/Grind.lean` to match `False` goals containing `Lean.Grind.Order.<name>_unsat_k` and emit `with_unfolding_all exact <leaf>` with a size guard.  Without the guard: regressed L83/L89/L97 to wall-clock-timeout.  With the guard: L83 returned to fast-fail but L89/L97 still timed out (deeper structural progress → bigger validation candidate).  **Definition kept but commented out of dispatch list.**
- **`rename_i` fallback for inaccessible hypotheses (2026-05-07)** — targeted `IsNonarchimedean.lean:216`'s fallback `exact <…> a✝` reference.  First wiring into `chooseExactStrategy` regressed L234; reworked as post-process `Syntax.replaceM` to fix L234 but then L216 hung 120s+ (Lean's elaborator on giant terms with missing names).  **Reverted; helpers `renameInaccessibleHyps` / `replaceInaccessibleRefs` removed from Helpers.lean during 2026-05-09 cleanup.**

Future direction for the order-grind cluster: a coordinated `Specialized/Grind/Order.lean` module (Top TODO #1) that handles the family as a system.

### Tomorrow's first thing (resume marker, 2026-05-10 — moving to bigger machine)

**For a new agent picking this up**: orient yourself with these five sections first — `## How it works` (5), `### Correctness Invariant` (25), `## Top TODO` (31), `### Pipeline overview` (in Design Notes), `### Concerns and risks`.  The 8-phase dispatch in `Decompiler.lean:382` is the load-bearing decomp logic; `tryDecompCasesOn` (`CasesOn.lean`) and `tryDecompByContradiction` (`ByContradiction.lean`) are the most subtle handlers.  For dev loop: `scripts/smoke.sh` is the fast regression check (16s); `lake build LeanDecomp.Test` is the snapshot regression check.  Standing user constraints in `~/.claude/.../memory/`: never commit; never stack lake/lean processes; broader-corpus sweeps only with explicit approval.

**Session state at handoff** — five concrete changes landed (all four code, plus tests):
1. **Concern #11 fix** (`Decompiler.lean tryDecompIffMpMpr`) — emit changed from `refine Iff.mp ?_ ?_` to `refine @Iff.mp P Q ?_ ?_` so synthetic re-elab works.  Locked by Test 22.
2. **Concern #2 / Top TODO #5** (`Decompiler.lean tryDecompByContradiction` → after split, `ByContradiction.lean`) — Phase B caches its body tactics; Phase D's `validateOrExact` reuses the cache instead of recomputing `decompileExpr`.  Heartbeat-starved candidates still get Phase D's looser validation second chance, no behavior change otherwise.
3. **Concern #10 / Top TODO #6** — split `Decompiler.lean`'s mutual block.  Three new files: `LeanDecomp/Intro.lean` (`tryDecompIntro`), `LeanDecomp/ByContradiction.lean` (`tryDecompByContradiction`), `LeanDecomp/Helpers/ArithTerminal.lean` (5 arith-terminal helpers promoted from `private`).  Decompiler.lean: 823 → 677 lines.  Mutual block: 11 → 9 partial defs.
4. **Concern #7 / Top TODO #7** (`TacticSimplify.lean eliminateDeadHaves`) — implemented + **gated off by default** via `register_option leanDecomp.eliminateDeadHaves`.  See Done section for the cost-regression rationale.
5. **Top TODO #4** (snapshot tests) — 20 → 25 in `Test.lean §8`: AndProj / EqSymm / IffMpMpr / EqRefl / EagerReduce / TheoremAppFallback const-head.  Tests 12 + 16 docstrings strengthened with explicit dispatch-order claims.

Smoke clean throughout (Sum 4/4, Int 5/5, list 1/1).  **All non-research deep-dive items closed.**

**Open from this session**: broader-corpus re-measurement.  The first attempt (with dead-have pass on) showed a regression (26/42 → 20/45, +11 wall-clock timeouts), which led to gating (Z) off.  **A clean post-fix sweep was not completed** — local machine constraints + an accidental cancellation left the run unfinished.  Resume on the bigger machine with:

```
cd /Users/oflatt/lean-decomp/mathlib4 && git clean -fdx -e .lake -e build Mathlib/Algebra/Order
cd /Users/oflatt/lean-decomp && python3 scripts/nightly.py --parallel 4 --runs 3 --warmup 1 --skip-mathlib-setup --output results-broader-order.json --dump dump-broader-order mathlib4/Mathlib/Algebra/Order > /tmp/sweep.log 2>&1
python3 scripts/analyze.py bucket results-broader-order.json dump-broader-order
```

Expected: similar to or slightly better than 26/42 = 62% (the IffMpMpr fix + byContradiction dedup are pure wins, no regressions expected).  `results-broader-order-with-deadhave.json` is preserved as the comparison-point for the dead-have-on regression (20/45) if anyone wants to investigate that path further.

**Pick from** (after the sweep validates):
- **(AA) Order-grind handlers** (Top TODO #1) — replace `grind only [<extracted>]` Rat leaves with structural emission.  Multi-session research.
- **(CC) Tighten dead-have cost model** so it can be on by default.  Idea: skip validation when the tactic following the `have` is one of `lia`/`grind`/`omega` *and* the tactic seq has only that one closing tactic (the regression came from validating big proofs with many haves; small proofs would be cheap).

**Don't break**: Sum 4/4, Int 5/5, all **25** snapshot tests, `bigstep`, `simple`, `bench_grind` unit tests, `scripts/smoke.sh`.  Broader-corpus baseline still **26/42 = 62%** from last measurement (will be re-measured on bigger machine).

### Earlier resume markers (archived)

Compressed log of prior session-end states.  Each "today's win + tomorrow's pick" was distilled to one line below; for the full text, `git log -- README.md` and walk back through.

- **2026-05-09 PM (post-broader-corpus rerun)** — 27/45 = 60% measurement landed (up from 23/49 = 47% on 2026-05-05).  Two `scripts/` bug fixes during the run: `nightly.py --parallel` SQLite cross-thread crash (serialize to plain lists in worker thread); `analyze.py bucket` mixing treatments (default to `--treatment decompile`).
- **2026-05-09 EOD** — `grind only [<extracted-user-lemmas>]` fallback shipped (Rat 0/5 → 3/5 covering L83/L89/L97).  See Done section.
- **2026-05-08 EOD** — three Rat-cluster attempts (rename_i fallback, `tryDecompFalseFromOrderGrind`, `Lean.Grind.Order.eq_mp` rewrite) all failed to ship a coverage win.  Lesson distilled: piecewise interventions on the order-grind family don't compose; the right level is a coordinated `Specialized/Grind/Order.lean` module.
- **2026-05-06 EOD** — `delabRefinable` + `pp.maxSteps` lift unblocked `⋯`-truncation globally.  L599 failure mode changed (truncation → 127KB exact, exposing the next blocker).
- **2026-05-05 PM** — investigated post-cross-file-fix clusters: identified the Rat `Lean.Grind.Order.*` family as the dominant remaining blocker; found an additional `⋯` source outside `chooseExactStrategy` that 2026-05-06's delab pass closed.

### Done log: pre-2026-05-09 (compressed)

Older Done entries condensed.  For the full pre-compression text of any entry, walk `git log -- README.md`.

**2026-05-05** — broader-corpus sweep: 18/54 → **23/49 = 47%** after closing the cross-file `inst✝` cluster (15 failures → 0); `bench_grind.GRIND_RE` false-positive fix (5 sites were `@[grind =]` attribute lines, not tactic calls — added `ATTR_RE` + `GRIND_ATTR_EQ_RE` skips).  Test 19 sanitizer snapshot lock added (synthetic `class FooBar` + axiom `foo_trans` exercises bare-ident gate).  A Test 20 for the projection-chain case couldn't be reproduced synthetically without mathlib's `Lean.Grind.Order.*` infra; `Group/List.lean L234` nightly slice is the existing lock for that path.

**2026-05-04** — five fixes:
- **Cross-file `inst✝` → `inferInstance` substitution**: new `LeanDecomp.sanitizeInaccessibleIdents` (now in `Helpers/Sanitizer.lean`).  Three-condition narrow gate (macro-scoped/✝ name + lctx fvar + `Meta.isClass?`).  Uses `inferInstance` (not `_` which fails in `exact`) via `mkIdent` (not `\`(inferInstance)` quotation which re-attaches macro scope).  Closed the dominant 15-failure cluster.
- **Cross-file projection-chain inaccessible refs**: extended sanitizer to handle `Term.proj` nodes whose root is an inaccessible-instance ident — replace the WHOLE `inst✝.toLE` chain with single `inferInstance` so typeclass synthesis targets the chain's result type.  Closed `Mathlib/Algebra/Order/BigOperators/Group/List.lean:234`.
- **Per-phase profile markers + `Core.checkSystem` in simplifier**: `IO.eprintln` + flush per phase so hangs surface immediately; `checkSystem` at `simplifyPre` entry so `Meta.transform`'s recursive walk respects heartbeats.  (Antidiag/Nat.lean L94 turned out to be a slow file-load issue, not a decompile bug.)
- **Process-group cleanup in `bench_grind.run_cmd`**: spawn with `start_new_session=True`, `os.killpg` on timeout/exit.  Closed the "18 orphaned `lean` workers from a Friday sweep" pattern.
- **Or → bare `lia` collapse**: post-loop check in `tryDecompCasesOn` for `Or` discriminant + both branches `[lia]` + `useHaveWrapper` → emit bare `lia` if validation passes.  Sum L55/L81: 8 lines → 3 lines, 0.96×–1.13× of grind.

**2026-05-01** — three fixes:
- **byContradiction specialized-first dispatch**: reordered to specialized → structural → terminal → fallback.  Int L91: 0.640s → 0.063s (10× speedup, 14× slower than grind → 1.3× slower).  Range collapsed from 0.07×–0.98× to 0.72×–0.98× of grind.  (The full 4-phase structure persists today, with the additional 2026-05-09 Phase B → Phase D dedup.)
- **`used : List String` → `DecompM := StateRefT (List String) TacticM`**: ~30–40 functions across 6 files lost the explicit accumulator parameter.  Save/restore at `validateOrExact` and `tryDecompByContradiction` error boundaries.
- **Dev-cycle tooling pass** — `scripts/probe.sh`, mathlib build cache in `nightly.py`, `set_option trace.leanDecomp / leanDecomp.profile / leanDecomp.dumpOnFail`, `showdecomp <term>` tactic, `leanDecomp.candidateMaxHeartbeats` exposed as register_option.  Debugging Playbook section in README rewritten.

**2026-04-30** — cleanup batches (no behavior change; net −410 lines):
- **Utility consolidation**: deleted 5 dead files (`BenchGrind.lean`, `casesonterm.lean`, `casesOnType.lean`, `IndentTest.lean`, `simpleterm`); consolidated `peelArgs` / `containsConstName` / `containsEagerReduce` / `anonymizeSyntheticMVars` duplicates into `Helpers.lean`; extracted `silentTry` helper; factored `emitHavePeel` shared between `tryDecompEqMpForallCongr` / `tryDecompEqMpImpliesCongr`.
- **Combinator + strategy + handler-split**: `chooseExactStrategy` unified policy with `ExactStrategyConfig`; `matchConstApp?` combinator applied to 12 handlers; `tryDecompCasesOn` 340-line function split into `runMVarIdCases` / `cleanupEqMotiveTransport` / `mkCasesWithAltsTactic`.
- **Dispatch + simplifier + test cleanup**: documented `firstSomeM` 8-phase dispatch with ordering invariants; added `leanDecomp.simplify.checkTypes` register_option (catches the `Lean.Grind.of_eq_eq_true` precedent class of bug); refactored `collectFinsetMemRewrites` 3-pass structure; reorganized `Test.lean` into 6 sections.
- **fvar-app handler collapse**: deleted `tryDecompProblematicProofApp` (~40 lines, dead duplicate of `tryDecompTheoremAppFallback`); generalized fallback to emit `apply $head` when all args are proof-like.  Test 4b regression-locks the path.
- **lctx-based mem-rewrite scan** (`Specialized/Grind.lean`): added Pass 3 to `collectFinsetMemRewrites` scanning lctx for `Finset.mem_<X>` shapes.  Sum L36: 3/4 → 4/4.  Defensive 100k heartbeat bound on `candidateTacticsCloseGoal` introduced same change.

**Earlier** — `forall_congr` / `implies_congr` peelers in `EqDecomp.lean`: two handlers (`tryDecompEqMpForallCongr` for `Eq.mp (forall_congr <body>) <evidence>`, `tryDecompEqMpImpliesCongr` for `Eq.mp (implies_congr Eq.refl q_eq) <evidence>`) that compose with the grind-specific leaf handler.  Each has instantiated and universal cases; `have h := <ev> x` / `<ev> hp` puts the user-form hypothesis in lctx for downstream `lia`.  Closed Sum L70 at default 200k heartbeats (collapses to 7 lines via `lia` fast path).

**Earlier** — `decide` swap in `mkExactFallbackTactics`: when proof contains `eagerReduce` AND inferred type is `(_ : Bool) = (true : Bool)` (the certificate shape), try `decide` before `with_unfolding_all exact`.  Defensive — kept for future grind proofs that emit literal certificate-shaped fallbacks.

## Recommended Next Steps (after the top TODO)

- **Extend the `MVarId.cases`-based per-branch decomp to generalized motives.** The current implementation falls back to a synthesized lctx when the casesOn motive carries a trailing `heq : disc = ctor xs` (i.e., proofs from `cases h : disc with`). The naive approach — `MVarId.generalize` with `hName?` to introduce both the abstracted fvar and the eq hyp, then `MVarId.cases`, then substitute `heq → real_eq_fvar` in the body — was tried and breaks `LeanDecomp.simple`: the old body's `Eq.rec` cleanup (substituting `heq → Eq.refl s` and stripping the resulting transport) turns out to be load-bearing for downstream handlers like `contradiction` and `noConfusion`, which consume the type-incorrect intermediate the cleanup produces. The right fix probably needs to either (a) keep the old cleanup but run the recursion in the new substituted lctx, or (b) drive the per-branch recursion through `evalTactic` of `cases h : disc with` syntax (using a synthetic outer mvar) so Lean's elaborator handles the transport natively. Multi-eq generalized motives (indexed inductive types) are a further extension.
<!-- forall_congr handler promoted to Top TODO. -->

- **Apply the "single lia call" pattern wherever multiple sub-goals close arithmetically.** `tryDecompFinsetIntervalMembership` and `tryDecompFalseFromLia` are the current users. Any handler that currently emits per-branch `lia` is a candidate.
- **Generalize `simplifyEqRecOfIdMotive` past the `a = True ∧ base = True.intro` restriction.** Rule was renamed in preparation but body is still narrow. Lifting the restriction caused `maximum recursion depth has been reached` errors before; retry with a more conservative generalization.
- **Audit other `Lean.Grind.*` simplifier rewrites for type-correctness bugs** (the `of_eq_eq_true` precedent — the rewrite returned a proof of `a = b` for a lemma whose actual conclusion was `a ∧ b ∨ ¬a ∧ ¬b`).
- **Set `pp.numericTypes` and `pp.coercions.types` on every delab call that produces user-elaborable syntax.** L91 demonstrated that default delab options drop type information needed to disambiguate mixed-numeric expressions.

## Design Notes

### Pipeline overview (deep-dive, 2026-05-09)

The macro is a 3-stage pipeline + sanitization + validation round-trip:

```
inner tactic           User's `decompile <tac>` runs the wrapped tactic, producing a proof term.
       ↓
Stage 1: simplifyProofTerm      Expr → Expr.   Strip wrappers, beta-reduce,
   (Simplify.lean)              normalize Eq.mp/Eq.mpr chains, convert grind
                                certs to standard library forms.
       ↓
Stage 2: decompileExpr          Expr → Array (TSyntax `tactic).  The bulk.
   (Decompiler.lean              8-phase dispatch over a mutual recursion of
    + sub-files)                 ~25 handlers.  Each handler validates before
                                 returning.
       ↓
Stage 3: simplifyTactics        TSyntax → TSyntax.  Currently only collapses
   (TacticSimplify.lean)        `have h := by exact t` → `have h := t`.
       ↓
sanitizeInaccessibleIdents      Cross-file safety: `inst✝` → `inferInstance`.
       ↓
checkDecompiled                  Round-trip validation.  If fails → error.
       ↓
addSuggestion                    `Try this` codeAction.
```

#### Stage 2's 8-phase dispatch

`Decompiler.lean:382` runs `tracedFirstSomeM` over a list of `(handlerName, action)` pairs in a fixed order.  First handler that returns `some` wins.  **Order is correctness-load-bearing in 2 places** (the `*Congr` peelers MUST precede `tryDecompEqMp`; specialized handlers MUST precede general structural Eq.mp).

1. **Pre / shape escapes**: `tryDecompExactLocalHyp`.
2. **Binder-introducing structural**: `tryDecompByContradiction`, `tryDecompCasesOn`.  Introduce new fvars for branch decomp.
3. **Specialized (grind-aware)**: `trySpecializedDecompHandlers` (`Specialized/Grind.lean`).
4. **Structural propositional + equality**: `tryDecompPropext`, `Iff.intro/mp/mpr`, `And.*`, `congr*`, `Eq.symm/trans`, `EqMp` peelers.
5. **False / contradiction**: `tryDecompFalseRec`, `tryDecompFalseType`.
6. **Term-shape**: `tryDecompLet`, `tryDecompBetaRedex`, `tryDecompEagerReduce`, `tryDecompEqRefl`, `tryDecompDecide`.
7. **Terminal arithmetic**: `tryDecompArithmeticTerminalPasses` (`lia` → `grind_order` → `grind_linarith`).
8. **Theorem-app fallback**: `tryDecompTheoremAppFallback`.

If all 8 return `none`, `decompExact body` emits `exact` / `with_unfolding_all exact` / `grind only [<extracted>]` via `chooseExactStrategy`.

#### Validation discipline

Every speculative emission goes through `silentTry` (state + message-log + error rollback) before being returned as a real result.  Heartbeat cap (`leanDecomp.candidateMaxHeartbeats = 100k`) bounds the cost of one bad candidate.  See "Validation discipline" line in the deep-dive section under `## Concerns and risks` for caveats.

#### `tryDecompByContradiction` — 4 internal phases

- **Phase A**: specialized short-circuit (`trySpecializedDecompHandlers` on the body).  Big wins when grind's contradiction body is decoration over a single decidable predicate.
- **Phase B**: structural recursion (`decompileExpr` on the body).
- **Phase C**: arithmetic terminal (`lia`/`grind_order`/`grind_linarith`).
- **Phase D**: `validateOrExact` final fallback.

State-restoration (`let savedUsed ← getUsed; ...; set savedUsed`) between phases prevents name-state leak from a failed phase.  **Concern #2** wants cheap shape-checks at each phase entry to skip work that obviously won't match.

#### `tryDecompCasesOn` — 3 sub-phases per branch

1. **runMVarIdCases**: synthetic outer mvar + `MVarId.generalize` (if needed) + `MVarId.cases` → real per-branch substituted subgoals.
2. **cleanupEqMotiveTransport**: substitute eq params; strip residual `Eq.rec`/`Eq.ndrec` (load-bearing for downstream `contradiction` / `noConfusion`).
3. **Recurse via `decompileOrExact`** in the substituted lctx.

Per-alt isolation via `let savedUsed ← getUsed; set savedUsed` so `cases h_inacc_1` in alt 1 doesn't bias alt 2.  Post-loop "trivial Or → bare lia" collapse closes the Sum L55/L81 hot pattern.

#### `chooseExactStrategy` — fallback orchestra

Order of attempts (`Helpers.lean:351`):
1. `extractGrindOnlyLemmas proof` → if non-empty, try `grind only [<lemmas>]`.  **The 2026-05-09 Rat coverage win lives here.**
2. If `containsEagerReduce proof` AND `cfg.tryDecideFirst` AND `proofTy = (_ : Bool) = true`: try `decide`.
3. If `containsEagerReduce proof`: emit `with_unfolding_all exact <termStx>`.
4. Else: emit `exact <termStx>`.

All delab paths route through `liftPPTruncationOptions` (lifts `pp.deepTerms` + `pp.proofs` + `pp.maxSteps`) so `⋯` never appears in rendered output.  Pre-flight check in `checkDecompiled` catches any regression.

### Concerns and risks (from 2026-05-09 deep-dive)

10 concerns surfaced in the review.  Status of each:
- **#1 Termination by heartbeat budget** — accepted; hard to prove formally.
- **#2 byContradiction phases re-run `decompileExpr`** — *fixed 2026-05-09 PM* (Top TODO #5).  Phase B → Phase D dedup via cached body tactics.
- **#3 `validateOrExact` cumulative cost** — `analyze.py shape` (added 2026-05-09 PM) gives per-file fallback-shape counts; iterate on data.
- **#4 Generalized cases motives gap** — research item, deferred.
- **#5 Dispatch-order load-bearing in 2 places** — fix planned (Top TODO #4 — snapshot tests that lock the order).
- **#6 grind only output-policy relax** — clarified in code comments + Done section.
- **#7 Stage-3 simplifier underused** — *2026-05-09 EOD: implemented; 2026-05-10: gated off by default* (Top TODO #7).  `eliminateDeadHaves` pass in `TacticSimplify.lean`, opt-in via `set_option leanDecomp.eliminateDeadHaves true`.
- **#8 No CSE / sub-proof sharing** — declined as speculative; revisit if `analyze.py shape` shows duplication.
- **#9 Two-tier heartbeat cap** — declined.
- **#10 Mutual block hurts dev loop** — *fixed 2026-05-09 EOD* (Top TODO #6).  Extracted to Intro.lean / ByContradiction.lean / Helpers/ArithTerminal.lean.
- **#11 `tryDecompIffMpMpr` brittle in synthetic contexts** (surfaced 2026-05-09 PM) — *fixed same day* (see Done section): emit changed from `refine Iff.mp ?_ ?_` to `refine @Iff.mp P Q ?_ ?_`.  Test 22 locks the new shape.

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
- Output sanitization (`sanitizeInaccessibleIdents` in `Helpers.lean`, run at `buildDecompiledTactics`) replaces inaccessible-named typeclass-instance refs (`inst✝`, `inst✝.toLE`, etc.) with `inferInstance` so emitted suggestions survive cross-file re-elaboration.  Three-condition narrow gate (macro-scoped/✝ name + lctx hit + `Meta.isClass?` true) ensures non-instance hygienic refs are left alone.
- Tactic-level collapse: `tryDecompCasesOn` recognises the trivial `Or.casesOn` with both branches reducing to bare `lia` (Sum L55/L81 hot pattern) and short-circuits to a single `lia`, validated against the original goal.

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

Results (2026-05-04, unchanged from 2026-04-30 except where today's `Or.casesOn → bare lia` collapse fired):
- `Mathlib/Algebra/Order/Group/Unbundled/Int.lean`: 5/5 (lines 47, 69, 76, 79, 91).
- `Mathlib/Algebra/Order/Group/Int/Sum.lean`: 4/4 (lines 36, 55, 70, 81).

Int L69 simplifies to `apply Classical.byContradiction; intro hp; lia`. L47/L76/L79/L91 decompile via byContradiction → outer `cases` over an `of_eq_eq_true`-shaped disjunction → inner `cases` of the resulting `And` → `tryDecompAbsCaseSplitContradiction` at each leaf. Sum L70 and L36 both collapse to byContradiction + `have h_fact := hs x …` + `rw [Finset.mem_sdiff, Finset.mem_<Ico|Ioc>] at hp` + `lia` via the lctx-based mem-rewrite scan + `tryDecompEqMpForallCongr` peeler.  **Sum L55/L81** further collapse all the way to bare `apply Classical.byContradiction; intro hp; lia` via the 2026-05-04 `Or → lia` rule.

### Main Open Blockers

- **Stage-3 tactic simplifier (residual).**  Trivial `cases hOr | lia | lia` collapse landed 2026-05-04.  Remaining residue: `tryDecompAbsCaseSplitContradiction`'s two-branch `by_cases h_abs ; · rw …; lia ; · rw …; lia` shape (Int L47/L91) — see Top TODO #4.
- **Cross-file coverage on the broader corpus** (Top TODO #1).  Today's `inferInstance` substitution and projection-chain handling addressed the dominant 15/36 failure mode, but a fresh sweep is needed to confirm the new coverage number and identify the next cluster.

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
- **Inaccessible-name sanitization needs three conditions** (2026-05-04).  The `inst✝ → inferInstance` rewrite must check (a) `Name.hasMacroScopes ∨ isInaccessibleUserName`, (b) FVar exists in lctx with that exact userName, AND (c) `Meta.isClass?` returns `some _`.  An earlier broader version that fired on any `hasMacroScopes` ident broke validation by replacing accessible hygienic binders.  Also: the substitute MUST be built via `mkIdent ``inferInstance` (not `\`(inferInstance)` quotation) — quotation attaches a fresh macro scope which PrettyPrinter then sanitizes back to `inferInstance✝`, ironically reproducing the exact problem we're fixing.
- **Projection-chain inaccessible refs need whole-projection replacement** (2026-05-04).  `inst✝.toLE` cannot be rewritten to `inferInstance.toLE` — Lean fails to synthesize `inferInstance : ?m` before descending into `.toLE` ("type class instance expected ?m").  The correct fix replaces the WHOLE `Term.proj` chain with a single `inferInstance`, since the projection's result type is also a class — typeclass synthesis can target the chain's final type directly.
- **Per-phase profile markers must `(← IO.getStderr).flush` explicitly** (2026-05-04).  Stderr is fully-buffered when redirected; without flush, `IO.eprintln` markers are lost on SIGKILL — defeating the diagnostic for "macro hung at phase X" cases that the markers exist to identify.
- **`subprocess.run(timeout=…)` only kills the immediate child** (2026-05-04, `bench_grind.run_cmd`).  `lake env lean` spawns `lean` workers that orphan to PID 1 when the lake parent dies.  Friday's broader-corpus run left 18 orphans burning CPU for 30+ hours.  Fix: `start_new_session=True` + `os.killpg(pgid, SIGTERM)` on timeout, plus an `atexit` / `SIGINT` / `SIGTERM` / `SIGHUP` walker over a `_LIVE_GROUPS` registry for script-level Ctrl-C / crash cases.  EPERM on `killpg(_, 0)` (probe) and EPERM on `killpg(_, SIGTERM/SIGKILL)` are both treated as "group is gone" — macOS returns EPERM after the leader is reaped even though the group is effectively dead.

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
