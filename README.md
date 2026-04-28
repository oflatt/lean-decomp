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

### Benchmarking

- **`scripts/nightly.py`** — Nightly evaluation: clones mathlib4, finds files containing `grind`, and benchmarks the decompiler on each grind call site.
- **`scripts/mine_grind_history.py`** — Mines recent mathlib history for removed `grind` calls. Pass `--benchmark-limit N` to compare whole-file timing before vs after the first `N` removal hunks.
- **[eval-live](https://github.com/oflatt/eval-live)** — Live HTML dashboard library for viewing benchmark results (installed via pip).

Use `--dump <dir>` to preserve generated inputs. The nightly script copies validated variants to `<dir>/Mathlib/.../<FileStem>/L<line>.<treatment>.lean` and failures to `*.query.lean` / `*.failed.lean`.

### Using `nightly.py`

Run `nightly.py` from the repository root. It will:
- reuse or clone `mathlib4/`
- reset that checkout to the pinned commit in `scripts/nightly.py`
- add the local `lean-decomp` dependency to the nested mathlib checkout
- build `lean-decomp`
- build the targeted mathlib modules
- run the selected treatments on each `grind` site

Useful commands:

```bash
# Show CLI help
python scripts/nightly.py --help

# Run decompile extraction only on one file, and keep generated queries
python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean \
  --treatment decompile \
  --no-benchmark \
  --dump dump-nightly-int \
  --output results-nightly-int.json

# Benchmark all treatments on a folder and serve the HTML dashboard
python scripts/nightly.py mathlib4/Mathlib/Algebra/Order/Group \
  --runs 3 \
  --warmup 1 \
  --serve
```

Notes:
- `path` is workspace-relative, not mathlib-relative.
- `--no-benchmark` is the fastest way to check whether extraction/re-elaboration succeeds.
- `--treatment decompile` is useful while focusing on the decompiler specifically.
- `--dump` is essential when debugging failures, because it preserves the generated `*.query.lean` files.



## Current Status

**Goal**: a low-level decompiler from grind proof terms to basic tactics. Short term we want to decompile every `grind` call in mathlib; long term we will simplify the resulting proof via a tactic-level pass.

This section is intended as a handoff snapshot of the current branch state.

### What Is Working

- The project is fully on the structural decompiler path; the old `Omega.lean` route is gone.
- `LeanDecomp/Test.lean` builds successfully, including the arithmetic regressions that previously failed on certificate-heavy `Eq.mp` terms.
- The decompiler now has stable structural handlers for:
  - lambdas / `intro`
  - `let` bindings
  - `casesOn`
  - `False.rec` / contradiction-style eliminators
  - `Eq.refl -> rfl`
  - `eagerReduce -> decide`
  - structural `Eq.mp`
  - `propext` and `Iff.intro`
  - `Iff.mp` / `Iff.mpr` (via `refine` with two subgoals)
  - `And.left` / `And.right` (via `apply` on the conjunction witness)
  - proposition-valued `Eq.rec` / `Eq.ndrec` transports (`EqDecomp.lean`)
  - `abs.eq_1` leaves with a matching sign hypothesis (emits `rw [abs_of_<sign> h]; lia`)
  - late theorem-application fallback with recursive proof subgoals
- `byContradiction` now tries structural decompilation of the contradiction body first, and only falls back to arithmetic terminals (`lia`, `grind_order`) when the structural script does not validate.
- `tryDecompCasesOn` no longer bails when the discriminant is a `Lean.Grind.*` term. The discriminant is decompiled up front into a `have hOr : ... := by ...` block (wrapped in try/catch so size-guard failures cleanly return `none` from the casesOn handler instead of propagating). The contradiction-branch skip only fires for multi-constructor inductives, so single-constructor types like `And` still produce a full `cases hOr with | intro ... => ...`.
- Specialized grind handling includes:
  - an `mt` handler (`mt hPQ hnQ` decomposes into two structural subgoals);
  - small `Eq.mp` peelers for `Lean.Grind.iff_eq` and `Lean.Grind.not_eq_prop` casts that recurse on the inner proof;
  - `tryDecompEqMpIntLinearNormLe` collapses `Eq.mp (Int.Linear.norm_le ...) <inner>` into a single `lia` step (with `Finset.mem_*` rewrites in the lctx if needed) — bypasses re-elaboration of grind's polynomial certificates;
  - `tryDecompFinsetIntervalMembership` for goals shaped `_ ∈ Finset.<X> a b`: emits `rw [Finset.mem_X]; lia`. The single trailing `lia` handles the resulting And-shaped arithmetic natively — much faster than `refine ⟨?_, ?_⟩ <;> lia` because `lia` setup amortizes across both conjuncts;
  - `tryDecompFalseFromLia` for `False` goals whose proof carries grind automation: tries `lia` (with `Finset.mem_*` rewrites if needed) — collapses many byContradiction-body decompositions into a single arithmetic terminal;
  - `tryDecompAbsLeaf` for grind's `abs.eq_1`-shaped abs unfoldings when a sign hypothesis is already available;
  - `tryDecompAbsCaseSplitContradiction` for `False` goals where the local context has any `abs x` hypothesis: it generates a `by_cases` sign split, rewrites each branch via `abs_of_<sign>`, and closes with `lia`.
- `tryDecompAndIntro` decomposes `And.intro a b <pfA> <pfB>` into `refine ⟨?_, ?_⟩` with two recursive subgoals, but skips when both components are local fvars (so trivial `⟨ha, hb⟩` cases still fall through to `exact ⟨ha, hb⟩`).
- `simplifyProjOfIntro` reduces `And.left/And.right` of an explicit `And.intro`, and `Iff.mp/Iff.mpr` of an explicit `Iff.intro`, in `Simplify.lean`. This exposes the projected component to downstream handlers and is the key reduction that lets grind's `Eq.mp (Eq.symm (propext (Iff.intro f g))) ev` chains collapse to `g ev` after `simplifyPropCast` strips the `Eq.mp/Eq.symm/propext` layers.
- `simplifyEqRecOfTrueIntro` reduces `Eq.rec.{0, _} Prop True (motive := fun x _ => x) True.intro target h` to `Eq.mp h True.intro`. This collapses the `e ▸ True.intro` shape grind emits when transporting `True.intro` through a `True = target` equality, exposing the cast to `simplifyEqMpTrueIntroEqTrue` for further peeling (`Eq.mp (Eq.symm (eq_true h)) True.intro → h` case added).
- The theorem-application fallback treats proof-valued functions as proof-like, which helps recurse into higher-order proof arguments instead of embedding large lambdas raw. Proof-like arguments are also elided from generated notation terms as `?_` holes.
- Arithmetic-like goal detection now recognizes grind automation constants (`Int.Linear.*`, `Nat.Linear.*`, `Lean.Grind.Order.*`, `Lean.Grind.CommRing.*`), which widens where `lia` is a safe terminal.
- The output is in line with the README policy: the decompiler does **not** emit `simp`, `simp_all`, `grind`, or `omega` as generated proof steps.

### What We Learned Recently

- Bigger proof terms are sometimes acceptable if they remove grind-specific scaffolding and expose recursive structure that the decompiler can handle.
- A naive simplifier for single-cast `Eq.mp (Lean.Grind.not_eq_prop ...) h` was benchmark-negative on real mathlib examples, so that experiment was reverted.
- Targeted decompiler-side transport handlers were safer than broad simplifier rewrites. A more aggressive `Eq.rec` simplification in `Simplify.lean` caused recursion-depth problems and was removed.
- The `Int/Sum` failures are not just outer `convert` noise. Even the bare `sum_nbij` obligations still contain substantial proposition transport, `propext`, `congrArg`, `byContradiction`, and arithmetic structure.
- Preferring structural decompilation inside `byContradiction` unblocked `Int.lean` line 69 but also made the remaining `Sum.lean` failure terms larger (36 went `12479 → 17321`, 70 went `8521 → 12039`). The extra structure is real information, not regression — the fallback-size guard just rejects it when no handler closes the leaves.
- For some grind-produced proofs (Sum L70, Int L47), the structural decomposition now succeeds and closes the goal, but the generated `refine` tactics elaborate more slowly than the original `grind` call (e.g., 20s of refines vs. 100ms grind). This is an inherent limitation: the sub-terms still contain the same amount of low-level unification work, just wrapped in `refine` layers. Without targeted handlers that collapse `Int.Linear` / `Lean.Grind.CommRing` normalization chains into smaller tactics, some proofs cannot be usefully decomposed.
- `cutsat` is deprecated in the pinned Lean toolchain (the tactic prints "use `lia` instead" and routes through `grind`); a standalone probe on `|a| < 1 ↔ a = 0` shows `cutsat` failing because it cannot unfold `abs` on its own. Adding `cutsat` to the arithmetic-terminal list therefore does not help the `Int.lean` abs-shaped goals.
- Added `tryDecompAbsLeaf` in `LeanDecomp/Specialized/Grind.lean`: when a proof-term leaf contains `abs.eq_1 x` (grind's internal abs-unfolding lemma) and the local context has a sign hypothesis for `x` — direct (`x ≤ 0`, `0 ≤ x`, `x < 0`, `0 < x`) or negated (`¬(x ≤ 0)` etc. via `not_le.mp` / `not_lt.mp`) — the handler emits `rw [abs_of_<sign> h] at <targets>; lia`.
- Added `try/catch` fallbacks around every `ppExprToTermSyntaxWith` → `delabToRefinableSyntax` call path (in `Decompiler.lean` and `Helpers.lean`) so pretty-print/reparse failures fall back to `delabToRefinableSyntax` instead of propagating up and collapsing the whole decomp into a giant `exact`. This was needed after traces showed `ppExprToTermSyntax` throwing on `@And.casesOn` applications at a specific character in the output.
- Completed `have hOr := ...; cases hOr with ...` rewrite in `tryDecompCasesOn`: when the `casesOn` discriminant is a non-fvar application, we now emit a `have`-bound name and case on that, instead of inlining the big term. This unblocked `Sum/Int/Sum.lean` lines 55 and 81 (discriminant `Lean.Grind.em _` → `have hOr : ... ∨ ¬... := by lia; cases hOr with ...`).
- **`Lean.Grind.of_eq_eq_true` simplifier rewrite was type-incorrect.** It rewrote `of_eq_eq_true h : a ∧ b ∨ ¬a ∧ ¬b` to `Eq.mpr lhs True h True.intro : a = b` — different result types. This produced ill-typed proof terms whenever the expression sat under `Or.casesOn`. The bug was hidden by a pre-existing bail-out that skipped any `casesOn` whose discriminant head was `Lean.Grind.*`. Removing both the rewrite and the bail-out unblocked the largest remaining set of `Int.lean` failures.
- **The `cases ... with` contradiction-branch skip was over-aggressive.** When `isBranchContradiction body` is true, `tryDecompCasesOn` skipped the alt — but for single-constructor inductives (e.g. `And.intro`), this leaves `cases hOr with` with no alternatives, which Lean rejects as `Alternative \`intro\` has not been provided`. Now we only skip when the inductive has multiple constructors.
- **`tryDecompAbsLeaf`'s rewrite-target list included compound hypotheses that get destructured by surrounding `cases`.** When the outer pass emits `cases h_1 with | intro left right => ...`, `h_1` is consumed before any inner `rw [...] at h_1` runs. `findHypsWithAbsOf` now skips hypotheses whose type head is `And` or `Or`.
- **Added `tryDecompAbsCaseSplitContradiction`.** When the goal is `False` and the local context contains a hypothesis mentioning `abs x` for some `x`, this handler emits `by_cases h : x ≤ 0` + `rw [abs_of_<sign>] at <targets>` + `lia` for both branches. It fires even when the proof term does not explicitly use `abs.eq_1`, which lets it discharge `Int.Linear.*` arithmetic certificates whose end result is `False` but which never explicitly unfold `abs`.
- **Added small `Eq.mp` peelers for known grind rewrite lemmas.** `tryDecompEqMpIffEq` and `tryDecompEqMpNotEqProp` recognize `Eq.mp (Lean.Grind.iff_eq _ _) h` and `Eq.mp (Lean.Grind.not_eq_prop _ _) h` respectively, emit `refine Eq.mp <cast> ?_`, and recurse on the inner proof. Each peeler is ~10 LOC and composes through `decompileOrExact` so deeper handlers (`tryDecompMt`, `tryDecompExactLocalHyp`) close the bottom of the chain.
- **`tryDecompFalseRec` only emits `contradiction` when the goal is exactly `False`.** When `False.elim` is being used polymorphically against a non-`False` goal (e.g. proving `a = 0 → False`), `contradiction` cannot close it; emitting it forces the caller to fall back to a giant `exact` that trips the size guard. The handler now returns `none` for non-`False` goals so dispatch can fall through to the structural theorem-app fallback. This is a goal-shape signal, not grind-specific.
- **Validation false negatives were a recurring trap.** `subproofTacticsCloseGoal` runs the candidate against a fresh synthetic-opaque mvar in the same lctx, but it does not reproduce the constructor-argument unification that real `cases h : disc with | ctor ... => ...` performs. Tactics like `contradiction` that rely on injection/noConfusion across the case binding succeed in real elaboration and fail in validation. This is why we use a goal-shape check rather than validating `contradiction` directly inside the FalseRec handler.
- **Default `delabToRefinableSyntax` options drop type information that the parser then needs.** L91 (`abs_sub_lt_of_lt_lt`) appeared to be a missing-handler problem, but the actual blocker was that `tryDecompCasesOn`'s `have hOr : <discType> := ...` was emitting `(-1) * ↑a + ↑b ≤ 0 ∨ ¬...` without numeric-type or coercion-type annotations. With `a b : ℕ` in scope, Lean's elaborator picked `ℕ` as the arithmetic type and choked on `Neg ℕ`. Setting `pp.numericTypes := true` and `pp.coercions.types := true` on the discType delab gives `(-1 : ℤ) * ↑a + ↑b ≤ (0 : ℤ) ∨ ...`, which re-elaborates unambiguously. The same fix was applied to the `by_cases` predicate in `tryDecompAbsCaseSplitContradiction`. Lesson: when generating `have` types or `by_cases` predicates that may involve mixed-numeric expressions, set both `pp` options on the relevant delab calls.
- **One `lia` call on a compound goal is much cheaper than many `lia` calls on its split components.** `lia` is `cutsat` (routed through `grind`); each invocation pays a setup cost — building polynomial terms, asserting hypotheses into the engine, running search — that does not amortize across calls. Switching `tryDecompFinsetIntervalMembership` from `rw [mem_X]; refine ⟨?_, ?_⟩ <;> lia` (two `lia` invocations during validation) to `rw [mem_X]; lia` (one invocation that handles the resulting And natively) cut L70's elaboration time from ~86s to ~12s — `lia` already splits arithmetic conjunctions internally with shared engine state. The same idea drives the new `tryDecompFalseFromLia`: when the goal is `False` and the proof carries grind automation, try the Finset.mem rewrites + a single `lia` rather than decomposing structurally. This unblocked Test 6 (`refine @Eq.mp (5 ≤ n) False ?_ ?_; · lia; · exact h2` → `lia`) and Test 7 (a 6-line `refine` chain → 3 lines).
- **The Sum L70/L36 budget gap is small but unbreached.** L70 currently elaborates the generated tactic in ~12s wall time at 8M heartbeats, but the default 200k heartbeat budget gives only ~10s. The ~20% over-budget gap is dominated by the kernel reduction inside the two remaining `with_unfolding_all exact <giant lambda>` blocks — those leaves carry `eagerReduce (Eq.refl true)` polynomial certificates that force `with_unfolding_all` transparency at re-elaboration. Eliminating one of those lambdas would likely close the gap. The simplifier rule `simplifyEqRecOfTrueIntro` reduces `Eq.rec.{0, _} Prop True (id-motive) True.intro target h → Eq.mp h True.intro` for one of the patterns, but the other `Eq.rec True` instance in the proof was not reduced (root cause unconfirmed — most likely a different motive shape or a deeper traversal gap in `Meta.transform`).
- **Decompilation does not share subterms.** Walking the proof as a tree (no hash-consing or `let`-binding) means an inner subproof that appears `n` times generates `n` independent occurrences in the output. For grind's polynomial-shape proofs, this multiplies the elaborator's work — each occurrence re-runs the same definitional reduction. CSE on the proof term before decompilation would amortize this, but is deferred until simpler structural fixes are exhausted.

### Nightly Snapshot

Recent focused nightly runs used:

```bash
python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean \
  --treatment decompile \
  --no-benchmark \
  --dump dump-nightly-int \
  --output results-nightly-int.json

python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean \
  --treatment decompile \
  --no-benchmark \
  --dump dump-nightly-sum \
  --output results-nightly-sum.json
```

Current results:
- `mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`: 5 `grind` sites, **5 successes** (lines 47, 69, 76, 79, 91).
- `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean`: 4 `grind` sites, 2 successes (lines 55, 81); 2 timeouts (lines 36, 70).

Int L69 still simplifies to `apply Classical.byContradiction; intro hp; lia`. L47/L76/L79/L91 decompile via the same pipeline: byContradiction → outer `cases` over an `of_eq_eq_true`-shaped disjunction → inner `cases` of the resulting `And` → `tryDecompAbsCaseSplitContradiction` (sign case-split + abs rewrite + `lia`) at each leaf.

Remaining failure mode:
- **Deterministic timeout during elaboration** (Sum L36, L70): structural decomposition completes and produces valid tactics, but the resulting `refine` chain over `Int.Linear.norm_le` / `Lean.Grind.CommRing.*` arguments exceeds the 200k heartbeat limit. The proof is `Eq.mp (Eq.symm (propext (Iff.intro f g))) <poly_proof>` converting between `x ∈ Finset.Ico c (c + #s)` and grind's polynomial form. The `tryDecompEqMpIntLinearNormLe` handler closes the simplest leaves with `lia`, but the inner subgoals `c + -1·x ≤ 0` (i.e. `c ≤ x`) cannot be discharged by `lia` alone when the only relevant hypothesis is a `Finset.mem_Ico` membership — `lia` does not unfold Finset membership lemmas. The remaining structural Eq.mp + propext chain is what re-elaboration times out on.

Useful debug artifacts:
- `dump-nightly-int/Mathlib/Algebra/Order/Group/Unbundled/Int/`
- `dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/`

### Main Open Blockers

- **Sum L36 / L70 elaboration timeouts.** The decompiler produces structurally valid tactics, but `refine` over `Int.Linear.norm_le`-shaped casts re-runs work `grind` had collapsed. This is an efficiency gap, not a correctness gap. Without targeted handlers that replace `Int.Linear.*` chains with a single `lia` step at a higher level, decomposition does not help.
- **No stage-3 tactic simplifier.** Successful decompiles still contain `have hOr : ... := by lia; cases hOr with | inl ⟨..⟩ => ...` boilerplate that a tactic-level simplifier could collapse.

### Recommended Next Steps

- **Eliminate one of L70's two remaining `with_unfolding_all exact` blocks.** The simpler block at line ~307 of the generated tactic is an `Eq.rec.{0, 1} Prop True (id-motive) True.intro target eq_proof` that `simplifyEqRecOfTrueIntro` should reduce — but it doesn't, for unclear reasons (probably a motive shape or traversal gap). Diagnosing this is likely a small fix that closes the ~20% budget gap.
- **Apply the "single lia call" pattern wherever multiple sub-goals close arithmetically.** `tryDecompFinsetIntervalMembership` and `tryDecompFalseFromLia` are the two current users. There may be other handlers — particularly `tryDecompCasesOn` branches on arithmetic discriminants — that currently emit per-branch `lia` and could be folded into a single trailing `lia`.
- **Forall-membership preprocessor for `lia`.** When `lia` fails on an arithmetic goal but the proof contains a `<forall_hyp> <args>` application (where `<forall_hyp>` is a lctx fvar of type `∀ y ∈ S, P y`), synthesize `have <fresh> := <forall_hyp> <args>` before retrying `lia`. Prototyped earlier (`tryHavesPlusLia`) but the validation cost was too high when fired on every arithmetic goal. A narrower trigger (only when the proof literally contains a forall-fvar application) would re-enable it safely.
- **Continue auditing `Lean.Grind.*` simplifier rewrites for type-correctness bugs** (the `of_eq_eq_true` precedent). Each rewrite should be type-preserving — easy to verify by comparing the inferred type of the input and output Exprs in a unit test.
- **Audit other `Lean.Grind.*` simplifier rewrites for the same type-correctness bug we found in `of_eq_eq_true`.** That rewrite returned a proof of `a = b` for a lemma whose actual conclusion was `a ∧ b ∨ ¬a ∧ ¬b`. The bug was hidden for a long time because the casesOn handler bailed on `Lean.Grind.*` discriminants. Since that bail-out is gone, any other type-incorrect rewrite in `Simplify/Grind.lean` will now surface as ill-typed proof terms or validation false-negatives. A focused review of `simplifyGrindWrappers` and `simplifyGrindCombinators` is the cheapest place to look.
- **Set `pp.numericTypes` and `pp.coercions.types` on every delab call that produces user-elaborable syntax.** L91 demonstrated that default delab options drop the type information needed to disambiguate mixed-numeric expressions. The same options should be applied wherever the decompiler emits a `have <ident> : <type> := ...` or `by_cases <ident> : <expr> ≤ ...`.
- **Keep transport cleanup narrow and decompiler-side when possible.** Broad global rewrites in `Simplify.lean` have been fragile; the `of_eq_eq_true` bug is a fresh data point in that direction. Specialized handlers in `Specialized/Grind.lean` are easier to validate and easier to revert.
- **Preserve the current output policy.** Do not introduce `simp`, `grind`, or `omega` as generated tactics even if it makes some obligations easier. `lia` is the workhorse arithmetic terminal; `grind_order` and `grind_linarith` are acceptable narrow variants.
- **Avoid grind-specific knowledge in core `Decompiler.lean`.** Keep grind-shaped heuristics in `Specialized/Grind.lean` or `Simplify/Grind.lean`. The core decompiler should reason about goal shapes (e.g. "is the goal `False`?") rather than proof-term internals (e.g. "does the proof term contain `Lean.Grind.*`?").
- **After more transport scaffolding is removed, re-run the two nightly slices above before broadening to larger mathlib folders.**

### Debugging Playbook

If you are resuming work on the current failures, this is the shortest path back into the problem.

Start with the saved nightly artifacts rather than re-running all of mathlib:

```bash
# Re-check a saved failing query directly
cd mathlib4
lake env lean ../dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/L55.decompile.query.lean

# Or inspect a different preserved query
lake env lean ../dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/L81.decompile.query.lean
```

Useful entry points:
- `dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/L55.decompile.query.lean`
- `dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/L81.decompile.query.lean`
- `dump-nightly-int/Mathlib/Algebra/Order/Group/Unbundled/Int/`
- `results-nightly-sum.json`
- `results-nightly-int.json`

When changing decompilation behavior, rebuild the focused regression file first:

```bash
lake build LeanDecomp.Test
```

Then rerun just the targeted nightly slice:

```bash
python scripts/nightly.py \
  mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean \
  --treatment decompile \
  --no-benchmark \
  --dump dump-nightly-sum \
  --output results-nightly-sum.json
```

For `Int/Sum`, the most promising workflow is:
- inspect the preserved `*.query.lean` file
- isolate the failing obligation into a smaller probe if needed
- inspect the simplified proof shape, especially whether the remaining head is `Eq.rec`, `Eq.ndrec`, `Eq.mp`, `propext`, `congrArg`, `mt`, `Iff.mp`, `And.left`, `Or.casesOn`, or `byContradiction`
- add the narrowest possible structural handler
- rebuild `LeanDecomp.Test`
- rerun only the affected nightly slice

Where to make changes:
- if the issue is a proof-term normalization problem before decompilation, start in `LeanDecomp/Simplify.lean`
- if the issue is equality transport or congruence structure, start in `LeanDecomp/EqDecomp.lean`
- if the issue is theorem-application structure or fallback behavior, start in `LeanDecomp/Decompiler.lean`
- if the issue is clearly grind-specific, start in `LeanDecomp/Specialized/Grind.lean`

Things that already failed and should not be retried naively:
- broad `Eq.rec` simplification in `LeanDecomp/Simplify.lean`
- naive expansion of single-cast `Lean.Grind.not_eq_prop`
- adding `simp` to generated proof output just to close arithmetic subgoals
- the previous `Lean.Grind.of_eq_eq_true` simplifier rewrite (returned a proof of the wrong type and silently produced ill-typed proof terms; removed)
- using `subproofTacticsCloseGoal` to validate `contradiction`-style tactics inside a handler; the validation does not reproduce `cases`-introduced unification and gives false negatives in real `cases h_eq : ...` contexts

### Architecture Notes For Handoff

- `LeanDecomp/Simplify.lean` performs Expr-level proof-term cleanup before decompilation. `LeanDecomp/Simplify/Grind.lean` is its grind-specific subset; any rewrite there must be type-preserving.
- `LeanDecomp/Decompiler.lean` is the main structural term-to-tactic pass and contains the late theorem-app fallback. Keep grind-specific knowledge out of this file: reason about goal shapes (e.g. "is the goal `False`?"), not proof-term contents.
- `LeanDecomp/EqDecomp.lean` is where equality, congruence, and proposition-transport handlers live.
- `LeanDecomp/Specialized/Grind.lean` is the right place for grind-specific structural handlers (`mt`, `Eq.mp` peelers for known grind casts, `abs`-shaped contradictions). Handlers here are tried via `trySpecializedDecompHandlers`, which sits between `tryDecompCasesOn` and the more general structural handlers in the dispatch list.
- `LeanDecomp/CasesOn.lean` contains the `tryDecompCasesOn` pass. The discriminant decompile happens up front, wrapped in try/catch so size-guard failures return `none` cleanly.
- When a recursive tactic block does not validate, the system should keep falling back to `exact` for that subproof rather than risk breaking the re-elaboration invariant.

