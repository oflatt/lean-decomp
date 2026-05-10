import Lean
import LeanDecomp.Helpers

namespace LeanDecomp
open Lean Elab Meta Tactic

/-- If a tactic sequence is exactly `exact t`, return `t`. -/
private def exactTermFromSeq (seq : TSyntax `Lean.Parser.Tactic.tacticSeq) : Option (TSyntax `term) := do
  match seq with
  | `(Lean.Parser.Tactic.tacticSeq| exact $term) => some term
  | _ => none

mutual

  /-- Simplify a tactic sequence by rewriting any nested `have` blocks. -/
  partial def simplifyTacticSeq (seq : TSyntax `Lean.Parser.Tactic.tacticSeq) : CoreM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
    match seq with
    | `(Lean.Parser.Tactic.tacticSeq| $[$tacs]*) =>
        let tacs' ← tacs.mapM simplifyTactic
        `(Lean.Parser.Tactic.tacticSeq| $[$tacs']*)
    | _ =>
        pure seq

  /-- Simplify a tactic by collapsing trivial `have ... := by exact t` blocks. -/
  partial def simplifyTactic (tac : TSyntax `tactic) : CoreM (TSyntax `tactic) := do
    match tac with
    | `(tactic| have $h:ident : $ty := by $seq:tacticSeq) =>
        let seq' ← simplifyTacticSeq seq
        match exactTermFromSeq seq' with
        | some term => `(tactic| have $h:ident : $ty := $term)
        | none => `(tactic| have $h:ident : $ty := by $seq')
    | `(tactic| have $h:ident := by $seq:tacticSeq) =>
        let seq' ← simplifyTacticSeq seq
        match exactTermFromSeq seq' with
        | some term => `(tactic| have $h:ident := $term)
        | none => `(tactic| have $h:ident := by $seq')
    | `(tactic| have : $ty := by $seq:tacticSeq) =>
        let seq' ← simplifyTacticSeq seq
        match exactTermFromSeq seq' with
        | some term => `(tactic| have : $ty := $term)
        | none => `(tactic| have : $ty := by $seq')
    | `(tactic| have := by $seq:tacticSeq) =>
        let seq' ← simplifyTacticSeq seq
        match exactTermFromSeq seq' with
        | some term => `(tactic| have := $term)
        | none => `(tactic| have := by $seq')
    | _ =>
        pure tac

end

/-- Simplify a list of tactics by rewriting nested `have` blocks. -/
def simplifyTactics (tacs : Array (TSyntax `tactic)) : CoreM (Array (TSyntax `tactic)) :=
  tacs.mapM simplifyTactic

-- Dead-`have` elimination
-- ───────────────────────
-- Drop `have h := X` whose binder `h` doesn't appear textually in any
-- subsequent top-level tactic AND whose removal still leaves a sequence
-- that closes the goal.  Conservative: pattern destructuring like
-- `⟨h, _⟩` rebinds `h` locally but our textual check treats that as a
-- reference, so we err on the side of keeping live haves.

/-- Extract the binder name from a `have h := …` style tactic.  Returns
    none for anonymous (`have := …`) and `have ⟨…⟩ := …` destructuring
    patterns.  Only matches the term-RHS forms (`have h := X`) — the
    `by`-RHS forms are collapsed by `simplifyTactic` before this pass
    runs, so the only `have h := by …` left would be one whose body
    didn't reduce to a single `exact`, and we conservatively skip those. -/
private def extractHaveBinderName (tac : TSyntax `tactic) : Option Name :=
  match tac with
  | `(tactic| have $h:ident : $_ty:term := $_v:term) => some h.getId
  | `(tactic| have $h:ident := $_v:term) => some h.getId
  | _ => none

/-- True iff `name` appears as an identifier anywhere in the syntax tree.
    Conservative: matches lexically, so a destructuring pattern that
    rebinds the same name still counts as a reference. -/
private partial def referencesName (s : Syntax) (name : Name) : Bool :=
  match s with
  | .ident _ _ n _ => n == name
  | _ => s.getArgs.any (referencesName · name)

private partial def eliminateDeadHavesAux (tacs : Array (TSyntax `tactic)) (i : Nat)
    (proofType : Expr) (lctx : LocalContext) (localInsts : LocalInstances)
    : TacticM (Array (TSyntax `tactic)) := do
  if i >= tacs.size then return tacs
  if let some haveName := extractHaveBinderName tacs[i]! then
    let downstreamReferences := (List.range (tacs.size - i - 1)).any fun k =>
      referencesName tacs[i + 1 + k]!.raw haveName
    if !downstreamReferences then
      let candidate := tacs.extract 0 i ++ tacs.extract (i + 1) tacs.size
      if ← LeanDecomp.candidateTacticsCloseGoal candidate proofType lctx localInsts then
        return ← eliminateDeadHavesAux candidate i proofType lctx localInsts
  eliminateDeadHavesAux tacs (i + 1) proofType lctx localInsts

/-- When `true`, run the stage-3 dead-`have` elimination pass.  Default
    `false`: while the pass is correct (validation guards correctness),
    per-have `candidateTacticsCloseGoal` calls compound on heartbeat-
    bound nightly sites — the 2026-05-09 broader-corpus measurement
    regressed from 26/42 → 20/45 (+11 wall-clock timeouts) when this
    pass ran on every `decompile` call.  Keep the code behind a flag
    for opt-in use (`decompile`-the-tactic in interactive sessions
    where output quality matters more than per-call cost) and document
    the cost so future investigation can tighten it. -/
register_option leanDecomp.eliminateDeadHaves : Bool := {
  defValue := false
  descr := "Run stage-3 dead-`have` elimination after simplifyTactics. \
    Off by default — see TacticSimplify.lean docstring for the cost \
    trade-off."
}

/-- Walk the top-level tactic array and drop `have h := X` entries whose
    binder isn't referenced downstream AND whose removal still validates.
    Skips focused subgoal blocks (`· …`) — top-level only.  No-op when
    no haves are present (zero validation calls in the common case).
    No-op when `leanDecomp.eliminateDeadHaves = false` (default). -/
def eliminateDeadHaves (tacs : Array (TSyntax `tactic))
    (proof : Expr) (lctx : LocalContext) (localInsts : LocalInstances)
    : TacticM (Array (TSyntax `tactic)) := do
  unless leanDecomp.eliminateDeadHaves.get (← getOptions) do
    return tacs
  let proofType ← instantiateMVars (← Meta.inferType proof)
  eliminateDeadHavesAux tacs 0 proofType lctx localInsts

end LeanDecomp
