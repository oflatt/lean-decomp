import Lean
import Lean.Meta.Tactic.TryThis
import LeanDecomp.Decompiler
import LeanDecomp.Simplify

namespace LeanDecomp
open Lean Elab Command Meta Tactic
open Lean.Meta.Tactic.TryThis (addSuggestion)

private def isAuxiliaryProofName (name : Name) : Bool :=
  (name.toString.splitOn "_proof_").length > 1

private def expandAuxiliaryProofs (e : Expr) : MetaM Expr := do
  Meta.deltaExpand e isAuxiliaryProofName (allowOpaque := true)

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
  let simplifiedProof ← simplifyProofTerm expandedProof
  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  -- Decompile to syntax (delabToRefinableSyntax has its own pp.all fallback)
  let (tactics, _) ← decompileExpr simplifiedProof lctx localInstances []

  -- restore the original state with the original goal
  stateBefore.restore

  -- run the newly generated tactics to ensure they work

  -- Build a tacticSeq from the array of tactics
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$tactics]*)

  -- Check if the decompiled proof is too large, which indicates the decompiler
  -- fell through to raw `exact` terms for constructs it doesn't handle yet.
  let maxSize := 200000
  let tacticStr := toString (← PrettyPrinter.ppTactic ⟨tacticSeq⟩)
  if tacticStr.length > maxSize then
    logError m!"decompile failed: generated proof too large ({tacticStr.length} chars, max {maxSize}). The decompiler likely lacks handlers for some proof term constructs."
    return

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

/-- Count occurrences of each top-level constant in an expression. -/
private def constFrequency (e : Expr) : Std.HashMap Name Nat := Id.run do
  let mut counts : Std.HashMap Name Nat := {}
  let mut stack : List Expr := [e]
  let mut visited : Nat := 0
  while !stack.isEmpty && visited < 100000 do
    let cur := stack.head!
    stack := stack.tail!
    visited := visited + 1
    match cur with
    | .const n _ => counts := counts.insert n ((counts.getD n 0) + 1)
    | .app f a => stack := f :: a :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .forallE _ t b _ => stack := t :: b :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | .mdata _ e => stack := e :: stack
    | .proj _ _ e => stack := e :: stack
    | _ => pure ()
  return counts

/-- `analyzeterm grind` — runs the tactic, simplifies the proof term, and reports
    size stats + top constant frequencies. -/
elab "analyzeterm " t:tacticSeq : tactic => withMainContext do
  let goalMVar ← getMainGoal
  evalTactic (← `(tacticSeq| $t))
  let proof ← instantiateMVars (mkMVar goalMVar)
  let expandedProof ← expandAuxiliaryProofs proof
  let simplifiedProof ← simplifyProofTerm expandedProof

  let ppStr ← withOptions (fun o => o.setBool `pp.all true) do
    let fmt ← ppExpr simplifiedProof
    pure (toString fmt)

  -- Collect constant frequencies
  let freqs := constFrequency simplifiedProof
  let sorted := freqs.toList.toArray.qsort (fun a b => a.2 > b.2)
  let top30 := sorted.toList.take 30

  let freqStr := top30.map (fun (n, c) => s!"  {n}: {c}") |>.foldl (· ++ "\n" ++ ·) ""

  -- Also analyze top-level structure
  let topConst := match simplifiedProof with
    | .app fn _ =>
      let (f, args) := peelArgs simplifiedProof
      let name := match f with
        | .const n _ => s!"{n}"
        | _ => s!"(non-const head)"
      s!"Top: {name} with {args.length} args"
    | .lam n _ _ _ => s!"Top: lambda ({n})"
    | .const n _ => s!"Top: const {n}"
    | _ => s!"Top: other ({simplifiedProof.ctorName})"

  -- Count lambdas at top level
  let mut lamCount := 0
  let mut cur := simplifiedProof
  while cur.isLambda do
    lamCount := lamCount + 1
    cur := cur.bindingBody!

  -- After lambdas, what's the head?
  let headInfo :=
    let (f, args) := peelArgs cur
    let name := match f with
      | .const n _ => s!"{n}"
      | .bvar i => s!"bvar({i})"
      | .fvar id => s!"fvar"
      | _ => s!"{f.ctorName}"
    s!"After {lamCount} lambdas: {name} with {args.length} args"

  -- Walk deeper: for each lambda/app, show first few levels
  let mut depth := 0
  let mut walk := simplifiedProof
  let mut structLines : Array String := #[]
  while depth < 8 do
    if walk.isLambda then
      structLines := structLines.push s!"depth {depth}: lambda ({walk.bindingName!})"
      walk := walk.bindingBody!
    else
      let (f, args) := peelArgs walk
      let name := match f with
        | .const n _ => s!"{n}"
        | .bvar i => s!"bvar({i + lamCount - depth})"
        | .fvar _ => s!"fvar"
        | _ => s!"{f.ctorName}"
      structLines := structLines.push s!"depth {depth}: {name} ({args.length} args)"
      -- Descend into last arg (usually the "body" of proof terms)
      if args.isEmpty then break
      walk := args[args.length - 1]!
    depth := depth + 1

  let structStr := structLines.toList.foldl (fun acc s => acc ++ "\n  " ++ s) ""

  -- Filter for proof-relevant constants (not types/instances)
  let proofConsts := [``Eq.mp, ``Eq.mpr, ``Eq.trans, ``Eq.symm, ``Eq.refl,
    ``eq_true, ``eq_false, ``eq_false', ``Classical.byContradiction,
    ``Classical.em, ``Or.casesOn, ``Or.elim, ``Or.inl, ``Or.inr,
    ``And.intro, ``And.casesOn, ``And.left, ``And.right,
    ``False.casesOn, ``False.elim, ``False.rec, ``absurd,
    ``Not, ``True.intro, ``propext, ``congrArg, ``congr,
    ``Lean.Grind.not_and, ``Lean.Grind.not_eq_of_eq_true,
    ``Lean.Grind.or_eq_of_eq_false_right, ``Lean.Grind.and_eq_of_eq_true_right,
    ``Lean.Grind.eq_true_of_and_eq_true_right,
    ``Lean.Grind.imp_eq,
    ``Int.le_antisymm, ``Int.lt_iff_add_one_le,
    ``of_eq_true, ``of_eq_false]
  let proofFreqs := proofConsts.filterMap fun n =>
    match freqs.get? n with
    | some c => some (n, c)
    | none => none
  let proofStr := proofFreqs.map (fun (n, c) => s!"  {n}: {c}") |>.foldl (· ++ "\n" ++ ·) ""

  logInfo m!"Simplified proof size: {ppStr.length} chars\n{topConst}\n{headInfo}\nStructure:{structStr}\nProof constants:{proofStr}\nTop constants:{freqStr}"


end LeanDecomp
