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

Current state:
- The old `Omega.lean` path has been removed; the project is now exercising only the structural decompiler path.
- The `eagerReduce` / certificate re-elaboration blocker for the `Nat` arithmetic examples in `LeanDecomp/Test.lean` is fixed.
- Tests 6 and 7 in `LeanDecomp/Test.lean` now pass and are locked in with `#guard_msgs`.
- Low-level handlers now cover `let` bindings, `eagerReduce -> decide`, `Eq.refl -> rfl`, structural `Eq.mp`, and a late theorem-application fallback that turns proof arguments into recursive subgoals instead of collapsing everything into one `exact`.
- Hygiene artifacts such as `@Eq.mp✝` have been cleaned up in generated output.
- Specialized handling now has an extension point: `LeanDecomp/Specialized.lean` runs package-specific handlers, and grind-specific helpers live in `LeanDecomp/Specialized/Grind.lean`.

### Nightly Baseline Check: `Unbundled/Int.lean` and `Int/Sum.lean`

We re-ran the two historical baseline files with `scripts/nightly.py` using `--treatment decompile --no-benchmark`.

Current results:
- `mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`: 5 `grind` sites found, 0 decompile successes.
- `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean`: 4 `grind` sites found, 0 decompile successes.

Current blockers from those nightly runs:
- `Unbundled/Int.lean`: every decompile query currently fails during import/lint checking with `Declaration @Set.Subsingleton is not allowed to be imported by this file.` This is a query-generation/module-boundary problem, not yet a decompiler proof reconstruction failure.
- `Int/Sum.lean`: current failures are decompiler-side. We saw:
  - one heartbeat timeout during `whnf`
  - two cast/certificate re-elaboration failures involving arithmetic boolean certificates (`Eq.refl true` no longer matching the expected certificate type)
  - one generated-script bug with an unknown identifier `hEq`

The dumped nightly artifacts are useful for debugging these regressions:
- `dump-nightly-int/Mathlib/Algebra/Order/Group/Unbundled/Int/`
- `dump-nightly-sum/Mathlib/Algebra/Order/Group/Int/Sum/`

### Recent Milestone: Structural `Nat` Arithmetic Proofs Work

The key recent milestone was getting the `Nat` arithmetic `decompile grind` examples to validate without falling back to the original elaborated proof. The decompiler now reconstructs these proofs structurally, including the cast/certificate-heavy `Eq.mp` chains generated by grind.

Important techniques that made this work:
- decompile `Eq.mp` structurally with `refine @Eq.mp ... ?_ ?_`
- special-case `eagerReduce` as `decide`
- special-case cast-sensitive `Eq.refl`
- split theorem applications into theorem head plus recursively decompiled proof arguments

### Current Problem: Output Is Correct But Too Low-Level

The generated tactics are now valid, but they still expose low-level theorem scaffolding that a human would not usually write directly. For example, arithmetic contradictions often begin with terms like:

```lean
@Lean.Grind.Order.eq_trans_false
  (@LE.le Nat _ 5 n)
  (@LE.le Int _ 5 n)
  ?_ ?_
```

This is faithful to the proof term, but not pleasant output. The next cleanup pass should aim to compress such terms into something closer to the human mathematical statement they represent, for example by:
- pretty-printing proposition arguments instead of full elaborated `@LE.le ...` forms
- recognizing common transport/cast lemmas such as `Nat.ToInt.le_eq`
- collapsing theorem-head chains like `eq_trans_false` / `eq_trans_true'` into more direct contradiction steps
- cleaning up explicit coercions and numerals

This is exactly the kind of cleanup intended for the planned tactic-simplification stage, but some lightweight simplifications may also fit naturally in the term-to-tactic phase.

### Extension Architecture

We now have a small extensible layer for specialized decompilation logic:
- core structural handlers remain in `Decompiler.lean`
- package-specific hacks or cleanups can live under `LeanDecomp/Specialized/*`
- the first package is `LeanDecomp/Specialized/Grind.lean`

The intent is to keep the core decompiler generic while still making it easy to add targeted cleanup rules for particular proof producers such as `grind`.

### Immediate Next Steps

- Fix nightly query generation for restrictive module files such as `mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`, where the injected imports currently violate the file's allowed import boundary.
- Fix the `Int/Sum.lean` regressions: the `hEq` name leak, the arithmetic certificate re-elaboration failures, and the expensive `whnf` path.
- Simplify verbose theorem heads such as `Lean.Grind.Order.eq_trans_false` into output closer to what a human would write.
- Build the tactic-simplification pass (stage 3) to clean up structurally correct but noisy proofs.

