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
private def runDecompiled (tactics : TSyntax `Lean.Parser.Tactic.tacticSeq) : TacticM Unit := do
  let savedState ← saveState
  let savedMsgs ← Core.getMessageLog
  -- Suppress intermediate error messages during validation
  Core.setMessageLog {}
  try
    withCurrHeartbeats do
      withoutRecover do
        evalTactic tactics
    -- Check if any errors were logged (e.g., by `cases` alternatives)
    let newMsgs ← Core.getMessageLog
    Core.setMessageLog savedMsgs
    if newMsgs.hasErrors then
      savedState.restore
      let errMsgs := newMsgs.toList.filter (·.severity == .error)
      let errStrs ← errMsgs.mapM (·.data.toString)
      logError m!"decompile failed: generated tactics did not re-elaborate\n{"\n".intercalate errStrs}"
  catch e =>
    savedState.restore
    Core.setMessageLog savedMsgs
    logError m!"decompile failed: generated tactics did not re-elaborate\n{← e.toMessageData.toString}"


/--
`decompile` wraps a tactic sequence, runs it, captures the proof term,
and suggests an equivalent tactic script.
Usage: `decompile simp [foo]` or `decompile { simp; ring }`
-/
elab (name := decompileTac) tk:"decompile " t:tacticSeq : tactic => withMainContext do

  let goalMVar ← getMainGoal
  let stateBefore ← saveState

  evalTactic t

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

  -- Build a tacticSeq from the array of tactics
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$tactics]*)

  runDecompiled tacticSeq
  addSuggestion tk tacticSeq (origSpan? := ← getRef)

/--
`showterm` wraps a tactic sequence, runs it, captures the proof term,
and prints it as a message.
Usage: `showterm simp [foo]` or `showterm { simp; ring }`
-/
elab "showterm " t:tacticSeq : tactic => withMainContext do
  let goalMVar ← getMainGoal
  evalTactic (← `(tacticSeq| $t))
  let proof ← instantiateMVars (mkMVar goalMVar)
  let expandedProof ← expandAuxiliaryProofs proof
  let fmt ← ppExpr expandedProof
  logInfo m!"proof term:\n{fmt}"


elab "showtermexpanded " t:tacticSeq : tactic => withMainContext do
  withOptions (fun o => o.setBool `pp.all true) do
    let goalMVar ← getMainGoal
    evalTactic (← `(tacticSeq| $t))
    let proof ← instantiateMVars (mkMVar goalMVar)
    let expandedProof ← expandAuxiliaryProofs proof
    let fmt ← ppExpr expandedProof
    logInfo m!"proof term:\n{fmt}"


end LeanDecomp
