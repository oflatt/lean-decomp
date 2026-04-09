# lean-decomp

A Lean 4 proof decompiler that converts low-level proof terms back into human-readable tactic scripts. Given a proof produced by an automated tactic (like `grind`, `simp`, `decide`, etc.), lean-decomp reconstructs a tactic proof using common, less automated tactics such as `cases`, `intro`, `apply`, `exact`, `contradiction`, and `decide`.

The goal is **not** to fall back on powerful automation like `grind` or `omega` in the output — instead, the decompiler aims to produce proofs that a human could read and understand, using only simple, widely-understood tactics.

## How it works

lean-decomp provides a `decompile` tactic that wraps any other tactic:

```lean
import LeanDecomp

example : P := by
  decompile grind
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

Working on decompiling grind proofs from mathlib, using `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean` as the primary test file (4 grind sites at lines 35, 54, 69, 80). Ultimate goal is to run `scripts/nightly.py` on `Int/Sum.lean` and get small proofs from the decompiler without any errors. Also check that the current tests still pass.

### What works
- **Basic proof constructs**: `intro`, `cases`, `apply`, `exact`, `contradiction`, `decide`, `absurd` — all working and tested via `#guard_msgs` in Test.lean, simple.lean, bigstep.lean.
- **Grind wrapper unfolding**: `Lean.Grind.alreadyNorm`, `nestedProof`, `Marker` (identity wrappers) are delta-expanded. `Lean.Grind.em` is translated to `Classical.em`. `Lean.Grind.intro_with_eq` is reduced.
- **Eq chain decomposition**: `congrArg`, `congr`, `Eq.symm`, `Eq.trans`, `Eq.mp` are decompiled into `calc` blocks.
- **Smart contradiction**: `tryDecompFalseType` only emits `contradiction` when the local context has an actual contradiction (False hyp or P/¬P pair), avoiding false positives.

### Current problem: grind proof terms are too large
All 4 Sum.lean grind sites produce proof terms of 80K–220K chars (with `pp.all`). After simplification (grind wrappers removed), still ~94K chars. Structure:
- 2 lambdas (intros) → `Classical.byContradiction` → huge `Eq.mp (chain of Eq.trans/congrArg/eq_true/eq_false) True.intro`
- Only ~60 proof-relevant constants but 94K chars because `pp.all` prints all implicit type args
- The chain contains `Int.Linear.*` normalization terms (grind's linear arithmetic kernel) which are opaque internal machinery

### Current approach: `tryDecompOmega` handler
Added a handler that detects grind internal constants (`Int.Linear.*`, `Lean.Grind.*`, `Lean.RArray.*`) and tries `omega` on the goal instead of decomposing the proof term. Placed early in the handler chain (after `cases` but before eq decomposition). Currently debugging — the omega call may need the right set of hypotheses, and the decompiler needs to avoid falling through to huge `exact` terms before omega gets a chance.

### Build & test
```sh
make test                    # Run #guard_msgs tests
lake build LeanDecompTest    # Same thing
```

### eval-live (benchmark dashboard)

Install the [eval-live](https://github.com/oflatt/eval-live) package for the interactive results viewer:

```sh
pip install git+https://github.com/oflatt/eval-live.git
```

Then serve results with:

```sh
python scripts/nightly.py --justserve
```

### Test file for Sum.lean
```sh
cd mathlib4 && lake env lean AnalyzeSum.lean
```