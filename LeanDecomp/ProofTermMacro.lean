import Lean
import Lean.Meta.Tactic.TryThis
import LeanDecomp.Decompiler
import LeanDecomp.Simplify
import LeanDecomp.TacticSimplify

namespace LeanDecomp
open Lean Elab Command Meta Tactic
open Lean.Meta.Tactic.TryThis (addSuggestion)

/-- When `true`, the `decompile` macro writes the candidate tactic block,
    the simplified proof term, and the lctx to
    `/tmp/lean-decomp-debug-<timestamp>.{tac,proof,lctx}` whenever validation
    fails.  Replaces the "instrument the macro, build, run, revert" debugging
    loop — turn the option on, reproduce the failure, inspect the dumped
    files. -/
register_option leanDecomp.dumpOnFail : Bool := {
  defValue := false
  descr := "Dump candidate tactics + simplified proof + lctx to /tmp on \
    validation failure.  Useful for debugging decompile failures without \
    re-instrumenting the macro."
}

/-- When `true`, the `decompile` macro logs per-stage timing (simplifier,
    decompile, validation, emission) at the end of each call.  Pairs well
    with `set_option trace.leanDecomp true` (which tells you *which* handlers
    fired) to get a "where did the time go" picture.

    Per-handler timing is intentionally not measured here — the trace already
    surfaces which handlers fired, and threading a `ProfileMap` through
    `DecompM` would add state-monad complexity for limited dev-cycle
    benefit.  Stage-level totals are sufficient to spot which phase
    dominates on a slow `decompile` call. -/
register_option leanDecomp.profile : Bool := {
  defValue := false
  descr := "Log per-stage timing (simplifier, decompile, validation, emission) \
    at the end of each `decompile` call."
}

/-- Write the dump bundle to /tmp/lean-decomp-debug-<n>.{tac,proof,lctx}.
    Returns the path stem so the macro's error message can point at it. -/
private def writeFailureDump (tacticStr : String) (proof : Expr)
    (lctx : LocalContext) : MetaM String := do
  let stem := s!"/tmp/lean-decomp-debug-{← IO.monoMsNow}"
  IO.FS.writeFile s!"{stem}.tac" tacticStr
  let proofFmt ← Meta.ppExpr proof
  IO.FS.writeFile s!"{stem}.proof" (toString proofFmt)
  let mut lctxLines : Array String := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let tyFmt ← Meta.ppExpr decl.type
    lctxLines := lctxLines.push s!"{decl.userName} : {tyFmt}"
  IO.FS.writeFile s!"{stem}.lctx" (String.intercalate "\n" lctxLines.toList)
  return stem

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
  -- Run the DecompM pipeline with an empty initial used-name list.  `run'`
  -- discards the final state since the decompiler doesn't expose used names
  -- back to the macro layer.
  let tactics ← (decompileExpr proof lctx localInstances).run' []
  simplifyTactics tactics


/--
`decompile` wraps a tactic sequence, runs it, captures the proof term,
and suggests an equivalent tactic script.
Usage: `decompile simp [foo]` or `decompile { simp; ring }`
-/
elab (name := decompileTac) tk:"decompile " t:tacticSeq : tactic => withMainContext do
  let profileOn := leanDecomp.profile.get (← getOptions)
  -- Stage-level wall-clock measurement.  When profile mode is off we still
  -- query the clock but don't emit any messages — IO.monoMsNow is cheap.
  let t0 ← IO.monoMsNow

  let goalMVar ← getMainGoal
  let stateBefore ← saveState

  evalTactic t
  let tInner ← IO.monoMsNow

  let proof ← instantiateMVars (mkMVar goalMVar)
  let expandedProof ← expandAuxiliaryProofs proof
  let simplifiedProof ← simplifyProofTerm expandedProof
  let tSimplify ← IO.monoMsNow

  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  let tactics ← buildDecompiledTactics simplifiedProof lctx localInstances
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$tactics]*)
  let tDecomp ← IO.monoMsNow

  -- restore the original state with the original goal before validating
  stateBefore.restore

  let validateResult ← checkDecompiled tacticSeq
  let tValidate ← IO.monoMsNow

  match validateResult with
  | some err =>
      let dumpHint ← if leanDecomp.dumpOnFail.get (← getOptions) then
          let tacticStr := toString (← PrettyPrinter.ppTactic ⟨tacticSeq⟩)
          let stem ← writeFailureDump tacticStr simplifiedProof lctx
          pure m!"\n[dump: {stem}.tac / {stem}.proof / {stem}.lctx]"
        else
          pure m!""
      logError m!"decompile failed: generated tactics did not re-elaborate\n{err}{dumpHint}"
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
  let tEmit ← IO.monoMsNow
  addSuggestion tk { suggestion := .string codeActionStr } (origSpan? := ← getRef)
  if profileOn then
    logInfo m!"decompile profile: \
      inner={tInner - t0}ms · \
      simplify={tSimplify - tInner}ms · \
      decomp={tDecomp - tSimplify}ms · \
      validate={tValidate - tDecomp}ms · \
      emit={tEmit - tValidate}ms · \
      total={tEmit - t0}ms"

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

/--
`showdecomp <term>` (tactic form) runs `<term>` through the simplifier +
decompiler in the current goal context and prints the resulting tactic
block as a message.  Doesn't validate or emit a `Try this` suggestion —
strictly an inspection helper.

Useful for iterating on shape-specific handler changes — point it at a
specific subterm and see what shape comes out without the full `decompile`
round-trip (validation, suggestion emission).

Example:
```lean
example (P Q : Nat → Prop) (h_eq : ∀ x, P x = Q x) (h_uni : ∀ x, P x) (a : Nat) : Q a := by
  showdecomp (Eq.mp (forall_congr h_eq) h_uni a)
  sorry
```

Term-form (`#showdecomp`) is harder because `decompileExpr` runs in
`DecompM = StateRefT _ TacticM`, which needs a goal context the term
elaborator doesn't naturally provide.  Use the tactic form for now. -/
elab "showdecomp " t:term : tactic => withMainContext do
  let proof ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let expandedProof ← expandAuxiliaryProofs proof
  let simplifiedProof ← simplifyProofTerm expandedProof
  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  let tacs ← (decompileExpr simplifiedProof lctx localInstances).run' []
  let tactics ← simplifyTactics tacs
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$tactics]*)
  let tacticStr := toString (← PrettyPrinter.ppTactic ⟨tacticSeq⟩)
  logInfo m!"decompiled tactics:\n{tacticStr}"

end LeanDecomp
