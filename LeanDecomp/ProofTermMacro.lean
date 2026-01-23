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
private def validateTacticScript (tacticLines : List String)
    (goalType : Expr) (lctx : LocalContext) (localInstances : LocalInstances) : TacticM Unit := do
  let env ← getEnv
  -- Join tactic lines with semicolons (each line is a complete tactic)
  -- and wrap in braces for parsing as a single tactic block
  let trimmedLines := tacticLines.map (·.trimAscii.toString)
  let singleLine := String.intercalate "; " trimmedLines
  let wrappedTactics := "{" ++ singleLine ++ "}"
  let tacticBlock := String.intercalate "\n" tacticLines
  let tacticSyntax ←
    match Parser.runParserCategory (env := env) `tactic wrappedTactics with
    | Except.ok stx => pure stx
    | Except.error err => throwError s!"decompile: failed to parse generated tactic block:\n{err}\n\nGenerated:\n{tacticBlock}"
  -- Create a fresh goal with the same type and local context, then try to solve it
  let savedState ← saveState
  try
    let testGoal ← Meta.mkFreshExprMVarAt lctx localInstances goalType .syntheticOpaque `testGoal
    setGoals [testGoal.mvarId!]
    evalTactic tacticSyntax
    let remainingGoals ← getGoals
    unless remainingGoals.isEmpty do
      throwError s!"decompile: generated tactics did not close the goal\n\nGenerated:\n{tacticBlock}"
  catch err : Exception =>
    let msg ← err.toMessageData.format
    throwError s!"decompile: generated tactic block failed to elaborate:\n{msg.pretty}\n\nGenerated:\n{tacticBlock}"
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
  validateTacticScript tacticLines goalType lctx localInstances
  let tacticBlock := String.intercalate "\n" tacticLines
  addSuggestion tk tacticBlock (origSpan? := ← getRef)

end LeanDecomp
