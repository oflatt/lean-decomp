# lean-decomp

A Lean 4 proof decompiler that converts low-level proof terms back into human-readable tactic scripts. Given a proof, often produced by an automated tactic (like `grind`), lean-decomp reconstructs a tactic proof using common, less automated tactics such as `cases`, `intro`, `apply`, `exact`, `contradiction`, and `decide`.

The goal is **not** to fall back on powerful automation like `grind`, `simp`, or `simp_all` in the output — instead, the decompiler aims to produce proofs that a human could read and understand, using only simple, widely-understood tactics. `omega` is acceptable since it is predictable and well-scoped (integer/natural number arithmetic only).

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
2. **Term-to-tactic decompilation** (`Decompiler.lean`) — Pattern-matches on proof term structure and maps it to tactics (`intro` for lambdas, `cases` for `casesOn`, `apply`/`exact` for applications, `contradiction` for `False` eliminations, etc.). This stage should be a faithful structural translation — it should not change the proof strategy, only the representation.
3. **Tactic simplification** (planned, not yet implemented) — Will simplify and clean up the generated tactic script at the tactic level, e.g. collapsing redundant steps, improving readability, or replacing verbose tactic sequences with simpler equivalents.

After decompilation, the pipeline validates the generated tactics by re-elaborating them against the original goal, then suggests the result via Lean's "Try This" mechanism.

### Benchmarking

- **`scripts/nightly.py`** — Nightly evaluation: clones mathlib4, finds files containing `grind`, and benchmarks the decompiler on each grind call site.
- **[eval-live](https://github.com/oflatt/eval-live)** — Live HTML dashboard library for viewing benchmark results (installed via pip).

You can also preserve the generated benchmark inputs with `--dump <dir>`. The nightly script will copy each validated variant to a path like `<dir>/Mathlib/.../<FileStem>/L<line>.<treatment>.lean` so you can inspect a specific file, grind line, and treatment afterward. Failed treatments are dumped too: query failures are saved as `L<line>.<treatment>.query.lean`, and failed suggestion attempts as `L<line>.<treatment>.failed.lean`.


## Current Status

The current goal is **successful decompilation** — getting proofs to decompile at all. Pretty, human-readable output is a non-goal for now and will be addressed later via the tactic simplification stage.

Goal: run `scripts/nightly.py` across all mathlib grind call sites and produce a `results.json` with no decompiler failures. Currently using `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean` as the primary test file (4 grind sites).

**nightly.py runs to completion.** Results on Sum.lean (4 grind call sites):

| Line | grind site | decompile status | issue |
|------|-----------|-----------------|-------|
| L36 | `sum_le_card_nsmul ... grind` | ✅ passes | — |
| L55 | `use (c - x).toNat; grind` | ❌ proof too large (28K chars, limit 10K) | decompiler lacks handlers for some proof constructs, falls through to raw `exact` |
| L70 | `decompile grind` (Ico lower bound) | ✅ passes | — |
| L81 | `use (x - c).toNat; grind` | ❌ proof too large (29K chars, limit 10K) | same as L55 |

**Next steps:**
- Investigate L55/L81 proof-too-large failures — grind produces massive proof terms with constructs the decompiler doesn't yet handle.
- Expand to more mathlib files beyond Sum.lean.


### Future big todos
- Make the nightly script faster- could we run individual theorems instead of the entire file? This might make nightly much faster.
- Can we see if any of our decompiler is dead code right now over our tests and sum.lean?
