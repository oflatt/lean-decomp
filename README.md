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
2. **Term-to-tactic decompilation** (`Decompiler.lean`) — Pattern-matches on proof term structure and maps it to tactics (`intro` for lambdas, `cases` for `casesOn`, `apply`/`exact`/`refine` for applications, `let` for let-bindings, `rfl` for `Eq.refl`, `decide` for `eagerReduce`, `contradiction` for `False` eliminations, etc.). This stage is a faithful structural translation — it does not change the proof strategy, only the representation. The `omega` pass in `Omega.lean` is currently disabled while we focus on no-omega, fully-structural decompilation.
3. **Tactic simplification** (planned) — Will clean up the generated script (e.g., collapsing redundant steps).

After decompilation, the pipeline validates the generated tactics by re-elaborating them against the original goal, then suggests the result via Lean's "Try This" mechanism.

### Benchmarking

- **`scripts/nightly.py`** — Nightly evaluation: clones mathlib4, finds files containing `grind`, and benchmarks the decompiler on each grind call site.
- **[eval-live](https://github.com/oflatt/eval-live)** — Live HTML dashboard library for viewing benchmark results (installed via pip).

Use `--dump <dir>` to preserve generated inputs. The nightly script copies validated variants to `<dir>/Mathlib/.../<FileStem>/L<line>.<treatment>.lean` and failures to `*.query.lean` / `*.failed.lean`.



## Current Status

**Goal**: a low-level decompiler from grind proof terms to basic tactics. Short term we want to decompile every `grind` call in mathlib; long term we will simplify the resulting proof via a tactic-level pass. Pretty output is not a short-term goal.

Active work:
- Omega pass disabled in `Decompiler.lean`; we are exercising the raw structural path.
- Low-level handlers added: `let` bindings, `eagerReduce → decide`, `Eq.refl → rfl`, and `refine`-based elaboration of `Grind.*` / `Lean.Grind.*` theorem applications (proof arguments become subgoals instead of collapsing into one monolithic `exact`).
- Fallback `decompExact` wraps the emitted term in `with_unfolding_all exact` when the term contains an `eagerReduce` subterm, but this is insufficient (see below).

### Handoff: `eagerReduce` certificates block re-elaboration

`LeanDecomp/Test.lean` tests 6 and 7 currently fail `lake build`. Both are `decompile grind` on `Nat`-arithmetic goals. The generated tactic re-elaboration fails with:

```
Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  Lean.Grind.CommRing.norm_cnstr_cert ... = true
in the application
  eagerReduce (Eq.refl true)
```

Why: `eagerReduce` is a `@[expose]` kernel gadget. It tells the **kernel** to eagerly reduce when checking argument types. Grind constructs the proof term directly (bypassing the elaborator), so the kernel accepts it. When we delab the term and re-elaborate it via `exact`, the **elaborator** performs `isDefEq` between `Eq.refl true : true = true` and the expected `norm_cnstr_cert ... = true` at default transparency. `norm_cnstr_cert` is a `noncomputable def` without `@[reducible]`, so defeq fails before the kernel ever sees it. `with_unfolding_all` does not fix this because the elaborator's argument-type check runs before kernel validation.

Confirmed by `LeanDecomp/TestProbe.lean` (handwritten copy of the decompile output wrapped in `with_unfolding_all exact`): same error, plus cascading coercion / instance-synthesis failures (`Lean.Grind.CommRing Nat`, `Eq.refl n : n = n` vs `↑n = ?m`). The full delab+re-elab roundtrip is fundamentally losing elaboration context that grind relied on.

What I tried (all in `decompExact` in `Decompiler.lean`):
1. Replace `eagerReduce (Eq.refl true)` subterms with fresh synthetic metavariables and emit `refine <term> <;> rfl`. Fixed the eagerReduce error but exposed coercion delab issues (`Eq.refl n` vs `↑n = ?m`).
2. Replace **all** `Eq.refl` subterms with metavariables. Fixed coercion but broke with `Expr.denote` reducibility issues during `rfl`.
3. Wrap the whole term in `with_unfolding_all exact` (current state on `main`). Manual probe confirms this is insufficient — the elaborator's arg-type check is the blocker, not kernel transparency.

Promising next directions for the handoff agent:
- **Bypass re-elaboration entirely.** Since we already have the fully-elaborated `Expr` in `MetaM`, emit a custom tactic (e.g. `decompile_assign`) that directly assigns the `Expr` to the goal metavariable via `MVarId.assign`. The delab+re-elab roundtrip only exists to let users see a syntactic proof — but for the validation step we could sidestep it for leaf certificate subterms.
- **Push the `refine`-with-holes strategy deeper.** `tryDecompLowLevelTheoremApp` already turns proof arguments into subgoals. Extend the same idea all the way down so that every `eagerReduce`, `Eq.refl true`, and raw `Bool`-equality certificate becomes its own hole, closed by a tactic (`with_unfolding_all decide`, `native_decide`, or a custom kernel-level `rfl`). The whole-term `exact` fallback is the problem — split it up.
- **Delab with `pp.all := true`** so implicit type arguments are explicit. This may fix the coercion/instance failures that showed up once `eagerReduce` was handled, even if it doesn't fix `eagerReduce` itself.

Test hygiene:
- Tests 6 and 7 in `LeanDecomp/Test.lean` are **uncommented** and currently fail `lake build`. Do not comment them out — fixing the decompiler is the task.
- `#guard_msgs` on tests 6 and 7 is omitted intentionally; once re-elaboration works, add a `#guard_msgs` block matching the new output.

Baseline files (previously passing with omega enabled):
- `mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean` (4 grind sites)
- `mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean` (5 grind sites)

Next steps after the `eagerReduce` blocker is resolved:
- Re-run the no-omega path on the baseline files and extend nightly coverage across mathlib grind sites.
- Tactic-level simplifier (stage 3) — the long-term readability pass.

