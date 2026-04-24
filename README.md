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
- Specialized grind handling includes an `mt` handler, so terms of the shape `mt hPQ hnQ` decompile structurally instead of collapsing into a large `exact` term.
- The theorem-application fallback treats proof-valued functions as proof-like, which helps recurse into higher-order proof arguments instead of embedding large lambdas raw. Proof-like arguments are also elided from generated notation terms as `?_` holes.
- Arithmetic-like goal detection now recognizes grind automation constants (`Int.Linear.*`, `Nat.Linear.*`, `Lean.Grind.Order.*`, `Lean.Grind.CommRing.*`), which widens where `lia` is a safe terminal.
- The output is in line with the README policy: the decompiler does **not** emit `simp`, `simp_all`, `grind`, or `omega` as generated proof steps.

### What We Learned Recently

- Bigger proof terms are sometimes acceptable if they remove grind-specific scaffolding and expose recursive structure that the decompiler can handle.
- A naive simplifier for single-cast `Eq.mp (Lean.Grind.not_eq_prop ...) h` was benchmark-negative on real mathlib examples, so that experiment was reverted.
- Targeted decompiler-side transport handlers were safer than broad simplifier rewrites. A more aggressive `Eq.rec` simplification in `Simplify.lean` caused recursion-depth problems and was removed.
- The `Int/Sum` failures are not just outer `convert` noise. Even the bare `sum_nbij` obligations still contain substantial proposition transport, `propext`, `congrArg`, `byContradiction`, and arithmetic structure.
- Preferring structural decompilation inside `byContradiction` unblocked `Int.lean` line 69 but also made the remaining `Sum.lean` failure terms larger (36 went `12479 → 17321`, 70 went `8521 → 12039`). The extra structure is real information, not regression — the fallback-size guard just rejects it when no handler closes the leaves.
- `tryDecompAndProj` used `args.getLast?` to pick the And proof, which is correct only when `.left`/`.right` is applied with exactly 3 arguments. For the applied case `(h.right) extraArg ...` (where `h.right` returns a function), `getLast?` would pick the extra argument instead of the And proof, producing a wrong `apply And.right` with the wrong subgoal. Fixed by bailing out when `args.length != 3`, letting the theorem-app fallback handle the applied case by refining with holes for both the And proof and the extra proof args.
- For some grind-produced proofs (Sum L70, Int L47), the structural decomposition now succeeds and closes the goal, but the generated `refine` tactics elaborate more slowly than the original `grind` call (e.g., 20s of refines vs. 100ms grind). This is an inherent limitation: the sub-terms still contain the same amount of low-level unification work, just wrapped in `refine` layers. Without targeted handlers that collapse `Int.Linear` / `Lean.Grind.CommRing` normalization chains into smaller tactics, some proofs cannot be usefully decomposed.
- `cutsat` is deprecated in the pinned Lean toolchain (the tactic prints "use `lia` instead" and routes through `grind`); a standalone probe on `|a| < 1 ↔ a = 0` shows `cutsat` failing because it cannot unfold `abs` on its own. Adding `cutsat` to the arithmetic-terminal list therefore does not help the `Int.lean` abs-shaped goals.
- Added `tryDecompAbsLeaf` in `LeanDecomp/Specialized/Grind.lean`: when a proof-term leaf contains `abs.eq_1 x` (grind's internal abs-unfolding lemma) and the local context has a sign hypothesis for `x` — direct (`x ≤ 0`, `0 ≤ x`, `x < 0`, `0 < x`) or negated (`¬(x ≤ 0)` etc. via `not_le.mp` / `not_lt.mp`) — the handler emits `rw [abs_of_<sign> h] at <targets>; lia`. Traces confirm it fires and closes the inner leaves for `Int.lean` L76/L79. It does NOT unblock those sites end-to-end, however, because the outer structural `cases <huge_discriminant> with ...` that wraps the leaves fails re-elaboration during candidate validation — the discriminant is an `Eq.mp (Lean.Grind.not_eq_prop ...) (mt ... hp)` chain that doesn't cleanly replay through Lean's parser. This is an orthogonal issue from abs.
- Added `try/catch` fallbacks around every `ppExprToTermSyntaxWith` → `delabToRefinableSyntax` call path (in `Decompiler.lean` and `Helpers.lean`) so pretty-print/reparse failures fall back to `delabToRefinableSyntax` instead of propagating up and collapsing the whole decomp into a giant `exact`. This was needed after traces showed `ppExprToTermSyntax` throwing on `@And.casesOn` applications at a specific character in the output.

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
- `mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`: 5 `grind` sites found, 1 decompile success (line 69).
- `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean`: 4 `grind` sites found, 2 decompile successes (lines 55 and 81).

Int L69 simplifies to `apply Classical.byContradiction; intro hp; lia`. Sum L55 and L81 now produce longer structural scripts (cases + let bindings + refines) after the `And.right` applied-projection fix exposed more of the proof structure.

Current failure mode splits into two categories after recent decompiler work:
- **Exact-fallback-too-large** (Int L76, L79, L91): the proof term still contains `Or.casesOn` / `Int.Linear` witness trees that no handler can decompose, so the size guard rejects the raw `exact` fallback.
- **Deterministic timeout during elaboration** (Int L47, Sum L36, Sum L70): the structural decomposition now completes and produces valid tactics, but the resulting `refine` chain exceeds the 200k heartbeat limit when the elaborator re-checks the transported arithmetic arguments. This is progress (we no longer fall through to raw `exact`), but the generated tactics are slower than the original `grind` call and therefore not useful to suggest.

Current fallback-size failures and timeouts from the saved result files:
- `results-nightly-int.json`: L76, L79, L91 fail with proof terms sized `16613`, `61538`, `23007` nodes; L47 times out during tactic execution.
- `results-nightly-sum.json`: L36 and L70 time out at `whnf` / `isDefEq` during elaboration of the generated `refine` chain.

Useful debug artifacts:
- `dump-nightly-int/Mathlib/Algebra/Order/Group/Unbundled/Int/`
- `dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/`

### Main Open Blockers

- `Unbundled/Int.lean` still contains grind-specific proposition transport, `Lean.Grind.not_eq_prop`, `mt`, `byContradiction`, `Or.casesOn`, and arithmetic certificates. The `mt` case and the `byContradiction`-first structural pass improved L69, but not enough to get L47/L76/L79/L91 under the exact fallback limit.
- `Int/Sum.lean` remains blocked on `sum_nbij` obligations. The hard obligations are full of transport around interval-membership statements such as `Finset.mem_Ico` / `Finset.mem_Ioc`, plus `propext`, `congrArg`, and contradiction-driven arithmetic reasoning.
- The arithmetic-terminal fallback inside `byContradiction` continues to handle the easy obligations (lines 55 and 81 in `Sum.lean`, line 69 in `Int.lean`) before the decompiler would unfold the giant `Or.casesOn` / `Int.Linear` witness trees.
- The current decompiler can often preserve more structure than before, but it still lacks enough targeted handlers to turn those transported obligations into small recursive subgoals.
- There is still no stage-3 tactic simplifier. That means even successful structural decompilation would remain noisier than desired.
- The structural-first failures that now timeout (Sum L36/L70, Int L47) reveal an efficiency gap: `refine` over raw `Int.Linear.norm_le` / `Lean.Grind.CommRing.*` arguments requires the elaborator to redo work that `grind` had already collapsed. Decomposition only helps when the sub-terms are themselves cheaper to elaborate than the full proof.

### Recommended Next Steps

- Investigate whether the `Int.Linear.norm_le` normalization chains that dominate Sum L36/L70 and Int L47 can be replaced by a single `lia` / `cutsat` step at a higher level in the proof tree. A handler that detects `Eq.mp (Int.Linear.norm_le ...) h` and emits `(h : <original_type>)` with a `show` cast, or simply replaces the chain with `lia` when the result type is an arithmetic inequality, would shrink both the generated text and the elaboration time.
- Add structural handlers for `Or.casesOn` / `And.casesOn` over arithmetic disjunctions (Int L76/L79/L91). These typically destructure a hypothesis of the form `a = 0 ∨ a = 1 ∨ a = -1` and call arithmetic terminals in each branch.
- Keep transport cleanup narrow and decompiler-side when possible; broad global rewrites in `Simplify.lean` have been fragile.
- Preserve the current output policy: avoid introducing `simp` as a generated tactic even if it makes some obligations easier.
- After more of the transport scaffolding is removed, re-run the two nightly slices above before broadening to larger mathlib folders.

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

### Architecture Notes For Handoff

- `LeanDecomp/Simplify.lean` performs Expr-level proof-term cleanup before decompilation.
- `LeanDecomp/Decompiler.lean` is the main structural term-to-tactic pass and contains the late theorem-app fallback.
- `LeanDecomp/EqDecomp.lean` is where equality, congruence, and proposition-transport handlers live.
- `LeanDecomp/Specialized/Grind.lean` is the right place for grind-specific structural handlers such as the `mt` case.
- When a recursive tactic block does not validate, the system should keep falling back to `exact` for that subproof rather than risk breaking the re-elaboration invariant.

