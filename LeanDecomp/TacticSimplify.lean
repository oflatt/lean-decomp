import Lean

namespace LeanDecomp
open Lean

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

end LeanDecomp
