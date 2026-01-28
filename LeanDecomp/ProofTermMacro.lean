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

/-- Run tactics, throwing a decompile error if they give an error -/
private def runDecompiled (tactics : Array (TSyntax `tactic)) : TacticM Unit := do
  -- Save initial message log to restore later (suppressing intermediate errors)
  let initialMsgs ← Core.getMessageLog
  let initialMsgCount := initialMsgs.toList.length

  for tac in tactics do
    evalTactic tac
  let remainingGoals ← getGoals
  unless remainingGoals.isEmpty do
    throwError "decompile: generated tactics did not close the goal"

  -- Check for logged errors
  let finalMsgs ← Core.getMessageLog
  let newMsgs := finalMsgs.toList.drop initialMsgCount
  let errorMsgs := newMsgs.filter (·.severity == .error)
  unless errorMsgs.isEmpty do
    -- Restore original message log to suppress the duplicate errors
    Core.setMessageLog initialMsgs
    let errorStr := String.intercalate "\n" (← errorMsgs.mapM (fun m => do return (← m.data.format).pretty))
    throwError s!"decompile: generated tactic block had errors:\n{errorStr}"

/--
`decompile` wraps a tactic sequence, runs it, captures the proof term,
and suggests an equivalent tactic script.
Usage: `decompile simp [foo]` or `decompile { simp; ring }`
-/
elab (name := decompileTac) tk:"decompile " t:tacticSeq : tactic => withMainContext do

  let goalMVar ← getMainGoal
  let stateBefore ← saveState

  evalTactic (← `(tacticSeq| $t))

  let stateAfter ← saveState
  let proof ← instantiateMVars (mkMVar goalMVar)

  let expandedProof ← expandAuxiliaryProofs proof
  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  -- Decompile to syntax with pp.all for re-elaboration
  let (tactics, _) ← withOptions (fun o => o.setBool `pp.all true) do
    decompileExpr expandedProof lctx localInstances []

  -- restore the original state with the original goal
  stateBefore.restore

  -- run the newly generated tactics to ensure they work
  runDecompiled tactics

  -- Build a tacticSeq from the array of tactics
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$tactics]*)
  addSuggestion tk tacticSeq (origSpan? := ← getRef)


end LeanDecomp
