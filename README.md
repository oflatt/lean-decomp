# lean-decomp

A Lean 4 proof decompiler that converts low-level proof terms into readable tactic scripts. It avoids powerful automation in the output (no `grind`, `simp`, or `simp_all`), sticking to basic tactics like `cases`, `intro`, `apply`, `exact`, `contradiction`, and `decide`. `omega` is acceptable since it is predictable and scoped to integer/natural arithmetic.

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
2. **Term-to-tactic decompilation** (`Decompiler.lean`, `Omega.lean`) — Pattern-matches on proof term structure and maps it to tactics (`intro` for lambdas, `cases` for `casesOn`, `apply`/`exact` for applications, `contradiction` for `False` eliminations, `omega` for integer arithmetic, etc.). This stage should be a faithful structural translation — it should not change the proof strategy, only the representation. Omega-related decompilation (extracting facts from proof terms and closing goals with `omega`) lives in `Omega.lean`.
3. **Tactic simplification** (planned) — Will clean up the generated script (e.g., collapsing redundant steps).

After decompilation, the pipeline validates the generated tactics by re-elaborating them against the original goal, then suggests the result via Lean's "Try This" mechanism.

### Benchmarking

- **`scripts/nightly.py`** — Nightly evaluation: clones mathlib4, finds files containing `grind`, and benchmarks the decompiler on each grind call site.
- **[eval-live](https://github.com/oflatt/eval-live)** — Live HTML dashboard library for viewing benchmark results (installed via pip).

Use `--dump <dir>` to preserve generated inputs. The nightly script copies validated variants to `<dir>/Mathlib/.../<FileStem>/L<line>.<treatment>.lean` and failures to `*.query.lean` / `*.failed.lean`.



## Current Status

The current goal is **successful decompilation**. Pretty output is a non-goal for now and will be addressed later via tactic simplification.

**Baseline files (all pass)**
- `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean` (4 grind sites)
- `mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean` (5 grind sites)

Recent fixes:
- Skip grind-internal `casesOn` scrutinees to avoid unreadable `cases` output.
- Inject `Int.abs_eq_natAbs` facts for `|x| : ℤ` so `omega` can close abs goals.
- Force coercion-aware delab so integer inequalities re-elaborate.
- Handle `abs` by splitting on sign and rewriting with `abs_of_nonpos`/`abs_of_nonneg` (no `simp`).

Next steps:
- Tactic-level simplifier (stage 3).
- Pick a new mathlib file and extend nightly coverage.

