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
2. **Term-to-tactic decompilation** (`Decompiler.lean`, `Omega.lean`) — Pattern-matches on proof term structure and maps it to tactics (`intro` for lambdas, `cases` for `casesOn`, `apply`/`exact` for applications, `contradiction` for `False` eliminations, `omega` for integer arithmetic, etc.). This stage should be a faithful structural translation — it should not change the proof strategy, only the representation. Omega-related decompilation (extracting facts from proof terms and closing goals with `omega`) lives in `Omega.lean`.
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

| Line | grind site | decompile status | notes |
|------|-----------|-----------------|-------|
| L36 | `sum_le_card_nsmul ... grind` | ✅ passes | Decomposes into `intro`, `apply Classical.byContradiction`, `have` chains with `Iff.mp`, closes with `omega` |
| L55 | `use (c - x).toNat; grind` | ✅ passes | `cases Classical.em` on key inequality, each branch closed by `omega` |
| L70 | `decompile grind` (Ico lower bound) | ✅ passes | Similar to L36: `have` chains extracting facts from `mem_sdiff`/`mem_Ico`, closes with `omega` |
| L81 | `use (x - c).toNat; grind` | ✅ passes | Same structure as L55 with `cases Classical.em` + `omega` |

All 4 grind call sites in `Sum.lean` decompile successfully. The L55/L81 proofs are concise (5 lines, ~119 chars each), while L36/L70 produce longer but still readable tactic scripts with explicit fact extraction.

### Unbundled/Int.lean (5 grind call sites) — all pass

| Line | theorem | decompile status |
|------|---------|-----------------|
| L46 | `natAbs_abs` | ✅ passes |
| L68 | `natAbs_sub_pos_iff` | ✅ passes |
| L75 | `abs_lt_one_iff` | ✅ passes |
| L78 | `abs_le_one_iff` | ✅ passes |
| L90 | `abs_sub_lt_of_lt_lt` | ✅ passes |

Fixes that landed:

1. **Grind internals leaking (L68/L75/L78):** `tryDecompCasesOn` now returns `none` when the discriminant's head constant is in the `Lean.Grind.*` namespace, so grind-internal `casesOn` scrutinees no longer emit unreadable `cases` tactics — control falls through to `tryDecompOmega`.

2. **Omega vs abs (L46):** `tryDecompOmega` now injects `have fact := Int.abs_eq_natAbs x` for each `|x| : ℤ` found in the goal or context (`addAbsNatAbsFacts` in `Omega.lean`), giving `omega` the equality it needs to reason about integer abs.

3. **Coercion pretty-printing (L90):** Discriminant delab in `tryDecompCasesOn` now runs under `pp.coercions.types := true` and `pp.numericTypes := true`, so `-1 * ↑a + ↑b ≤ 0` renders as `(-1 : ℤ) * ↑a + ↑b ≤ (0 : ℤ)` with enough type anchors to re-elaborate.

**Next steps:**
- Tactic-level simplifier (stage 3 in the pipeline, still unwritten). Planned scope: always call the decompiler recursively at `have h := ...` sites, emitting `have h : T := by <tactics>`, then have the simplifier collapse trivial `:= by exact X` back to `:= X`. Separates concerns — the decompiler decides representation, the simplifier handles readability.
- Run nightly across more of `mathlib4/Mathlib/Algebra` to find the next failure class.


### Future big todos
- Make the nightly script faster- could we run individual theorems instead of the entire file? This might make nightly much faster.
- Can we see if any of our decompiler is dead code right now over our tests and sum.lean?
