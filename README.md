# lean-decomp

A Lean 4 proof decompiler that converts low-level proof terms back into human-readable tactic scripts. Given a proof, often produced by an automated tactic (like `grind`), lean-decomp reconstructs a tactic proof using common, less automated tactics such as `cases`, `intro`, `apply`, `exact`, `contradiction`, and `decide`.

The goal is **not** to fall back on powerful automation like `grind` or `omega` in the output — instead, the decompiler aims to produce proofs that a human could read and understand, using only simple, widely-understood tactics.

## How it works

lean-decomp provides a `decompile` tactic that wraps any other tactic block:

```lean
import LeanDecomp

example : P := by
  decompile
    grind
```

When elaborated, `decompile` runs the wrapped tactic, captures the resulting proof term, then:

1. **Simplifies** the proof term — unfolds auxiliary definitions, eliminates identity wrappers (e.g. `Lean.Grind.alreadyNorm`, `Lean.Grind.nestedProof`), simplifies `Eq.rec`/`noConfusion` patterns, and beta-reduces.
2. **Decompiles** the simplified term into tactic syntax by pattern-matching on proof term structure (`intro` for lambdas, `cases` for `casesOn`, `apply`/`exact` for applications, `contradiction` for `False` eliminations, etc.).
3. **Validates** the generated tactics by re-elaborating them against the original goal.
4. **Suggests** the result via Lean's "Try This" mechanism.

### Benchmarking

- **`scripts/nightly.py`** — Nightly evaluation: clones mathlib4, finds files containing `grind`, and benchmarks the decompiler on each grind call site.
- **[eval-live](https://github.com/oflatt/eval-live)** — Live HTML dashboard library for viewing benchmark results (installed via pip).


## Current Status

Goal: run `scripts/nightly.py` across all mathlib grind call sites and produce a `results.json` with no decompiler failures. Currently using `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean` as the primary test file (4 grind sites).

**Current blocker:** `python3 scripts/nightly.py` hangs — need to investigate why.


### Future todos
- Make the nightly script faster- could we run individual theorems instead of the entire file? This might make nightly much faster.

