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

All three successes currently simplify to `apply Classical.byContradiction; intro hp; lia`.

Current failure mode in both files:
- the queries fail because the decompiler eventually reaches the exact-fallback size guard and refuses to emit a giant proof term
- this is progress compared to earlier generated-script breakage, because the current blocker is mostly "still too much low-level structure survives" rather than an obviously malformed tactic script

Current fallback-size failures from the saved result files:
- `results-nightly-int.json`: lines 47, 76, 79, 91 fail with proof terms sized `55567`, `16613`, `61538`, and `23007` nodes respectively
- `results-nightly-sum.json`: lines 36 and 70 fail with proof terms sized `17321` and `12039` nodes respectively

Useful debug artifacts:
- `dump-nightly-int/Mathlib/Algebra/Order/Group/Unbundled/Int/`
- `dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/`

### Main Open Blockers

- `Unbundled/Int.lean` still contains grind-specific proposition transport, `Lean.Grind.not_eq_prop`, `mt`, `byContradiction`, `Or.casesOn`, and arithmetic certificates. The `mt` case and the `byContradiction`-first structural pass improved L69, but not enough to get L47/L76/L79/L91 under the exact fallback limit.
- `Int/Sum.lean` remains blocked on `sum_nbij` obligations. The hard obligations are full of transport around interval-membership statements such as `Finset.mem_Ico` / `Finset.mem_Ioc`, plus `propext`, `congrArg`, and contradiction-driven arithmetic reasoning.
- The arithmetic-terminal fallback inside `byContradiction` continues to handle the easy obligations (lines 55 and 81 in `Sum.lean`, line 69 in `Int.lean`) before the decompiler would unfold the giant `Or.casesOn` / `Int.Linear` witness trees.
- The current decompiler can often preserve more structure than before, but it still lacks enough targeted handlers to turn those transported obligations into small recursive subgoals.
- There is still no stage-3 tactic simplifier. That means even successful structural decompilation would remain noisier than desired.

### Recommended Next Steps

- Focus on the remaining `Sum.lean` failures (lines 36 and 70) — the preserved `*.query.lean` files are the fastest starting point.
- Add targeted handling for transported interval-membership goals, especially proofs involving `Finset.mem_Ico`, `Finset.mem_Ioc`, and `Finset.mem_range` after `convert`.
- For `Int.lean`, the remaining failures (L47, L76, L79, L91) are dominated by `Or.casesOn` / `Int.Linear` witness trees. New structural handlers for those shapes would likely unblock multiple sites at once.
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

