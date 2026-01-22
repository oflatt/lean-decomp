import Lean
import Lean.Meta.Tactic.TryThis
import LeanDecomp.Decompiler

namespace LeanDecomp
open Lean Elab Command Meta Tactic
open Lean.Meta.Tactic.TryThis (addSuggestion)

private def startsWithChars : List Char → List Char → Bool
  | [], _ => true
  | _, [] => false
  | c :: cs, d :: ds => c = d && startsWithChars cs ds

private def containsChars (needle haystack : List Char) : Bool :=
  match haystack with
  | [] => needle = []
  | _ :: hs =>
      startsWithChars needle haystack || containsChars needle hs

private def containsSubstring (haystack needle : String) : Bool :=
  let pattern := needle.toList
  let input := haystack.toList
  if pattern = [] then true else containsChars pattern input

private def isAuxiliaryProofName (name : Name) : Bool :=
  containsSubstring name.toString "_proof_"

private def expandAuxiliaryProofs (e : Expr) : MetaM Expr := do
  Meta.deltaExpand e isAuxiliaryProofName

/-- Validate that a generated tactic script actually proves a goal with the given type and local context. -/
private def validateTacticScript (tacticLines : List String) (suggestion : String)
    (goalType : Expr) (lctx : LocalContext) (localInstances : LocalInstances) : TacticM Unit := do
  let env ← getEnv
  -- Wrap in braces so it parses as a proper tactic sequence
  let trimmedLines := tacticLines.map (fun s => (s.dropWhile (· == ' ')).toString)
  let wrappedTactics := "{ " ++ String.intercalate "; " trimmedLines ++ " }"
  let tacticSyntax ←
    match Parser.runParserCategory (env := env) `tactic wrappedTactics with
    | Except.ok stx => pure stx
    | Except.error err => throwError s!"decompile: failed to parse generated tactic block:\n{err}\n\nGenerated:\n{suggestion}"
  -- Create a fresh goal with the same type and local context, then try to solve it
  let savedState ← saveState
  try
    let testGoal ← Meta.mkFreshExprMVarAt lctx localInstances goalType .syntheticOpaque `testGoal
    setGoals [testGoal.mvarId!]
    evalTactic tacticSyntax
    let remainingGoals ← getGoals
    unless remainingGoals.isEmpty do
      throwError s!"decompile: generated tactics did not close the goal\n\nGenerated:\n{suggestion}"
  catch err : Exception =>
    let msg ← err.toMessageData.format
    throwError s!"decompile: generated tactic block failed to elaborate:\n{msg.pretty}\n\nGenerated:\n{suggestion}"
  finally
    savedState.restore

/--
`decompile` wraps a tactic sequence, runs it, captures the proof term,
and suggests an equivalent tactic script.
Usage: `decompile simp [foo]` or `decompile { simp; ring }`
-/
elab (name := decompileTac) tk:"decompile " t:tacticSeq : tactic => withMainContext do
  let goalMVar ← getMainGoal
  let goalType ← goalMVar.getType
  evalTactic (← `(tacticSeq| $t))
  let proof ← instantiateMVars (mkMVar goalMVar)
  let expandedProof ← expandAuxiliaryProofs proof
  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  let (tactics, _) ← renderExprToTactics expandedProof lctx localInstances []
  let tacticLines := tactics.render
  let tacticBlock := String.intercalate "\n" tacticLines
  let suggestion := s!"by\n{tacticBlock}"
  validateTacticScript tacticLines suggestion goalType lctx localInstances
  addSuggestion tk suggestion (origSpan? := ← getRef)

end LeanDecomp
