import Lean
import Lean.Meta.Tactic.TryThis
import LeanDecomp.Decompiler
import LeanDecomp.Simplify
import LeanDecomp.TacticSimplify

namespace LeanDecomp
open Lean Elab Command Meta Tactic
open Lean.Meta.Tactic.TryThis (addSuggestion)

private def countLeadingSpaces (s : String) : Nat :=
  s.toList.takeWhile (· == ' ') |>.length

private def isAllSpaces (s : String) : Bool :=
  s.all (· == ' ')

/-- Reformat a pretty-printed multi-tactic string for use as a code action replacement.
    `col` is the absolute column of the `decompile` keyword.  VS Code replaces the
    original span literally: the first line inherits the column from context, so it
    must have no leading spaces; continuation lines must carry their absolute indent
    (col + their relative indent within the block) explicitly. -/
private def reindentForCodeAction (s : String) (col : Nat) : String :=
  let lines := s.splitOn "\n"
  let nonEmpty := lines.filter (!isAllSpaces ·)
  let minIndent := nonEmpty.foldl (fun acc l => min acc (countLeadingSpaces l))
    (nonEmpty.headD "" |> countLeadingSpaces)
  let colIndent := String.ofList (List.replicate col ' ')
  String.intercalate "\n" <| lines.mapIdx fun i l =>
    if isAllSpaces l then ""
    else if i == 0 then (l.drop minIndent).toString
    else colIndent ++ (l.drop minIndent).toString

private def isAuxiliaryProofName (name : Name) : Bool :=
  (name.toString.splitOn "_proof_").length > 1

private def expandAuxiliaryProofs (e : Expr) : MetaM Expr := do
  Meta.deltaExpand e isAuxiliaryProofName (allowOpaque := true)

/-- Try running tactics against the current goal state, always restoring the
    original state afterwards. Returns an error string on failure. -/
private def checkDecompiled (tactics : TSyntax `Lean.Parser.Tactic.tacticSeq) : TacticM (Option String) := do
  let tacticStr := toString (← PrettyPrinter.ppTactic ⟨tactics⟩)
  let savedState ← saveState
  let savedMsgs ← Core.getMessageLog
  -- Suppress intermediate error messages during validation
  Core.setMessageLog {}
  let result ← try
      withCurrHeartbeats do
        withoutRecover do
          evalTactic tactics
      let newMsgs ← Core.getMessageLog
      if newMsgs.hasErrors then
        let errMsgs := newMsgs.toList.filter (·.severity == .error)
        let errStrs ← errMsgs.mapM (·.data.toString)
        pure (some s!"generated tactics:\n{tacticStr}\n\n{"\n".intercalate errStrs}" )
      else
        pure none
    catch e =>
      pure (some s!"generated tactics:\n{tacticStr}\n\n{← e.toMessageData.toString}")
  savedState.restore
  Core.setMessageLog savedMsgs
  return result

private def buildDecompiledTactics (proof : Expr) (lctx : LocalContext)
    (localInstances : LocalInstances) : TacticM (Array (TSyntax `tactic)) := do
  let (tactics, _) ← decompileExpr proof lctx localInstances []
  simplifyTactics tactics


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
  let simplifiedProof ← simplifyProofTerm expandedProof
  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  let tactics ← buildDecompiledTactics simplifiedProof lctx localInstances
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$tactics]*)
  let probeStr := toString (← PrettyPrinter.ppTactic ⟨tacticSeq⟩)
  liftM (m := IO) (IO.FS.writeFile "/tmp/decompile_generated.txt" probeStr)

  -- restore the original state with the original goal before validating
  stateBefore.restore

  match ← checkDecompiled tacticSeq with
  | some err =>
      logError m!"decompile failed: generated tactics did not re-elaborate\n{err}"
      return
  | none => pure ()

  -- Check if the decompiled proof is too large, which indicates the decompiler
  -- fell through to raw `exact` terms for constructs it doesn't handle yet.
  let maxSize := 20000
  let tacticStr := toString (← PrettyPrinter.ppTactic ⟨tacticSeq⟩)
  -- (FileMap is available via CoreM which TacticM extends)
  let col : Nat ←
    match tk.getPos? true with
    | some pos =>
      let fileMap ← MonadFileMap.getFileMap
      pure (fileMap.toPosition pos).column
    | none =>
      -- Fallback: count leading spaces from source trivia
      match tk.getHeadInfo with
      | .original (leading := lead) .. =>
        pure (lead.toString.splitOn "\n").getLast!.length
      | _ => pure 0
  let codeActionStr := reindentForCodeAction tacticStr col
  if tacticStr.length > maxSize then
    logError m!"decompile failed: generated proof too large ({tacticStr.length} chars, max {maxSize}). The decompiler likely lacks handlers for some proof term constructs."
    return
  evalTactic tacticSeq
  addSuggestion tk { suggestion := .string codeActionStr } (origSpan? := ← getRef)

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

elab "showsimpl " t:tacticSeq : tactic => withMainContext do
  let goalMVar ← getMainGoal
  evalTactic (← `(tacticSeq| $t))
  let proof ← instantiateMVars (mkMVar goalMVar)
  let expandedProof ← expandAuxiliaryProofs proof
  let simplifiedProof ← simplifyProofTerm expandedProof
  let fmt ← ppExpr simplifiedProof
  logInfo m!"simplified proof term:\n{fmt}"

elab "showsimplexp " t:tacticSeq : tactic => withMainContext do
  withOptions (fun o => o.setBool `pp.all true) do
    let goalMVar ← getMainGoal
    evalTactic (← `(tacticSeq| $t))
    let proof ← instantiateMVars (mkMVar goalMVar)
    let expandedProof ← expandAuxiliaryProofs proof
    let simplifiedProof ← simplifyProofTerm expandedProof
    let fmt ← ppExpr simplifiedProof
    logInfo m!"simplified proof term:\n{fmt}"


end LeanDecomp
