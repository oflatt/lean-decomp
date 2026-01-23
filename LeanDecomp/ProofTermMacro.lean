import Lean
import Lean.Meta.Tactic.TryThis
import LeanDecomp.Decompiler

namespace LeanDecomp
open Lean Elab Command Meta Tactic
open Lean.Meta.Tactic.TryThis (addSuggestion)

private def isAuxiliaryProofName (name : Name) : Bool :=
  (name.toString.splitOn "_proof_").length > 1

private def expandAuxiliaryProofs (e : Expr) : MetaM Expr := do
  Meta.deltaExpand e isAuxiliaryProofName

/-- Validate that a generated tactic sequence actually proves a goal with the given type and local context. -/
private def validateTactics (tactics : Array (TSyntax `tactic))
    (goalType : Expr) (lctx : LocalContext) (localInstances : LocalInstances) : TacticM Unit := do
  -- Create a fresh goal with the same type and local context, then try to solve it
  let savedState ← saveState
  try
    let testGoal ← Meta.mkFreshExprMVarAt lctx localInstances goalType .syntheticOpaque `testGoal
    setGoals [testGoal.mvarId!]
    for tac in tactics do
      evalTactic tac
    let remainingGoals ← getGoals
    unless remainingGoals.isEmpty do
      throwError "decompile: generated tactics did not close the goal"
  catch err : Exception =>
    let msg ← err.toMessageData.format
    throwError s!"decompile: generated tactic block failed to elaborate:\n{msg.pretty}"
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
  -- Render to syntax with pp.all for re-elaboration
  let (tactics, _) ← withOptions (fun o => o.setBool `pp.all true) do
    renderExprToTactics expandedProof lctx localInstances []
  validateTactics tactics goalType lctx localInstances
  -- Build a tacticSeq from the array of tactics
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$tactics]*)
  addSuggestion tk tacticSeq (origSpan? := ← getRef)

end LeanDecomp
