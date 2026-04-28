import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

/-- Type alias for the decompileExpr callback to avoid repetition -/
abbrev DecompileCallback := Expr → LocalContext → LocalInstances → List String →
  TacticM (Array (TSyntax `tactic) × List String)

/-- Type alias for the assignIntroNames callback -/
abbrev AssignIntroNamesCallback := Array Expr → List String →
  TacticM (List String × LocalContext × List String)

/-- Build a tactic sequence from an array of tactics. -/
def mkTacticSeq (tacs : Array (TSyntax `tactic)) : CoreM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  `(Lean.Parser.Tactic.tacticSeq| $[$tacs]*)

/-- Build a focused tactic block for one recursively decompiled subgoal. -/
def mkFocusedBlock (tacs : Array (TSyntax `tactic)) : CoreM (TSyntax `tactic) := do
  let seq ← mkTacticSeq tacs
  `(tactic| · $seq:tacticSeq)

/-- Replace parser-generated `?m.N` placeholders with anonymous holes. -/
private def anonymizeSyntheticMVars (s : String) : String := Id.run do
  let chars := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < chars.size do
    if chars[i]! == '?' && i + 2 < chars.size && chars[i + 1]! == 'm' && chars[i + 2]! == '.' then
      let mut j := i + 3
      let mut sawDigit := false
      while j < chars.size && chars[j]!.isDigit do
        sawDigit := true
        j := j + 1
      if sawDigit then
        out := out ++ "?_"
        i := j
      else
        out := out.push chars[i]!
        i := i + 1
    else
      out := out.push chars[i]!
      i := i + 1
  out

private def ppExprToTermSyntax (e : Expr) : MetaM Term := do
  let env ← getEnv
  let fmt ← Meta.ppExpr e
  let termStr := anonymizeSyntheticMVars fmt.pretty
  match Parser.runParserCategory env `term termStr with
  | .ok stx => pure ⟨stx⟩
  | .error err =>
    throwError "failed to parse pretty-printed term:\n{err}\n\n{termStr}"

private def ppExprToTermSyntaxWith (e : Expr) (usePpAll : Bool) : MetaM Term :=
  withOptions (fun o =>
      let o := pp.coercions.types.set o true
      let o := pp.numericTypes.set o true
      if usePpAll then
        pp.all.set o true
      else
        o
    ) do
      ppExprToTermSyntax e

private partial def containsConstName (e : Expr) (target : Name) : Bool :=
  Expr.find? (fun sub => sub.getAppFn.constName? == some target) e |>.isSome

private partial def containsEagerReduce (e : Expr) : Bool :=
  Expr.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some n => n == ``eagerReduce
    | none => false) e |>.isSome

partial def exprNodeCount (e : Expr) : Nat :=
  match e with
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => 1
  | .app f a => exprNodeCount f + exprNodeCount a + 1
  | .lam _ ty body _ => exprNodeCount ty + exprNodeCount body + 1
  | .forallE _ ty body _ => exprNodeCount ty + exprNodeCount body + 1
  | .letE _ ty val body _ => exprNodeCount ty + exprNodeCount val + exprNodeCount body + 1
  | .mdata _ body => exprNodeCount body + 1
  | .proj _ _ body => exprNodeCount body + 1

private def throwIfFallbackProofTooLarge (proof : Expr) : MetaM Unit := do
  let maxNodes := 5000
  let nodeCount := exprNodeCount proof
  if nodeCount > maxNodes then
    throwError
      "exact fallback proof too large ({nodeCount} nodes, max {maxNodes}); refusing to emit a giant exact term"

/-- Build a robust exact fallback for a subproof. Prefer direct delaboration when
    possible, but fall back to fully pretty-printed syntax for low-level proofs. -/
private def mkExactFallbackTactics (proof : Expr) : MetaM (Array (TSyntax `tactic)) := do
  throwIfFallbackProofTooLarge proof
  let usePrettyPrintedTerm :=
    containsEagerReduce proof || containsConstName proof ``propext || containsConstName proof ``Iff.intro
  let termStx ← if usePrettyPrintedTerm then
      try ppExprToTermSyntaxWith proof true
      catch _ => delabToRefinableSyntax proof
    else
      try delabToRefinableSyntax proof
      catch _ => ppExprToTermSyntaxWith proof true
  if containsEagerReduce proof then
    let tac ← `(tactic| with_unfolding_all exact $termStx)
    return #[tac]
  else
    let tac ← `(tactic| exact $termStx)
    return #[tac]

/-! **Decompiler invariant**: when any decomp action runs, the main TacticM goal
    must equal the type of the proof term being decompiled, with a lctx that
    reflects what the real run of the surrounding tactics would produce.
    `runInGoal` and `runInSubgoal` are the building blocks that uphold this. -/

/-- Allocate a fresh synthetic-opaque mvar of `goalType` in (lctx, localInsts),
    set it as the only main goal, run `k`, then restore the original goals.
    Use this when entering a recursive decomp call from a synthetic context
    (lambda telescope, let-binder, byContradiction binder, etc.). -/
def runInGoal (lctx : LocalContext) (localInsts : LocalInstances) (goalType : Expr)
    (k : TacticM α) : TacticM α := do
  let savedGoals ← getGoals
  try
    withLCtx lctx localInsts do
      let mvar ← Meta.mkFreshExprMVar (some goalType) .syntheticOpaque
      setGoals [mvar.mvarId!]
      k
  finally
    setGoals savedGoals

/-- Focus an existing mvarId as the sole main goal, run `k` in its local
    context, then restore the original goals.  Use this when the goal already
    exists (e.g. a subgoal returned by `MVarId.cases`). -/
def runInSubgoal (mvarId : MVarId) (k : TacticM α) : TacticM α := do
  let savedGoals ← getGoals
  try
    setGoals [mvarId]
    mvarId.withContext k
  finally
    setGoals savedGoals

/-- Recursively decompile a proof term, but preserve correctness by falling back
    to an exact proof term when the generated tactics do not re-elaborate or do
    not fully close a fresh goal of the same type. -/
private def subproofTacticsCloseGoal (tacs : Array (TSyntax `tactic)) (expectedType : Expr)
    (lctx : LocalContext) (localInsts : LocalInstances) : TacticM Bool := do
  let savedMsgs ← Core.getMessageLog
  Core.setMessageLog {}
  let ok ← try
      withoutModifyingState do
        runInGoal lctx localInsts expectedType do
          let seq ← mkTacticSeq tacs
          evalTactic seq
          let remainingGoals ← getGoals
          let newMsgs ← Core.getMessageLog
          pure (!newMsgs.hasErrors && remainingGoals.isEmpty)
    catch _ =>
      pure false
  Core.setMessageLog savedMsgs
  return ok

  /-- Check whether a candidate tactic block closes a fresh goal of the given type.
    This is useful for speculative terminal tactics where failure should simply
    let the decompiler continue trying other handlers. -/
  def candidateTacticsCloseGoal (tacs : Array (TSyntax `tactic)) (expectedType : Expr)
    (lctx : LocalContext) (localInsts : LocalInstances) : TacticM Bool :=
    subproofTacticsCloseGoal tacs expectedType lctx localInsts

/-- Validate a candidate tactic block against the full proof goal and fall back
    to an exact proof term if validation fails. -/
def validateOrExact (proof : Expr) (lctx : LocalContext) (localInsts : LocalInstances)
    (used : List String) (build : TacticM (Array (TSyntax `tactic) × List String))
    : TacticM (Array (TSyntax `tactic) × List String) := do
  let proofTy ← instantiateMVars (← Meta.inferType proof)
  try
    let (candidateTacs, used') ← build
    if ← subproofTacticsCloseGoal candidateTacs proofTy lctx localInsts then
      return (candidateTacs, used')
    else
      let fallbackTacs ← mkExactFallbackTactics proof
      return (fallbackTacs, used')
  catch _ =>
    let fallbackTacs ← mkExactFallbackTactics proof
    return (fallbackTacs, used)

def decompileOrExact (proof : Expr) (lctx : LocalContext) (localInsts : LocalInstances)
    (used : List String) (decompileExpr : DecompileCallback)
    : TacticM (Array (TSyntax `tactic) × List String) := do
  validateOrExact proof lctx localInsts used do
    decompileExpr proof lctx localInsts used

/-- Emit a tactic that may create multiple goals, then recursively decompile one
    proof term per generated goal into focused sub-blocks. This is the common
    shape used by theorem-style decompiler passes. -/
def emitTacticWithSubgoals (headTac : TSyntax `tactic) (subgoalProofs : Array Expr)
    (lctx : LocalContext) (localInsts : LocalInstances) (used : List String)
  (decompileExpr : DecompileCallback) : TacticM (Array (TSyntax `tactic) × List String) := do
  let mut allTacs : Array (TSyntax `tactic) := #[headTac]
  let mut used' := used
  for proof in subgoalProofs do
    let (chosenTacs, used'') ← decompileOrExact proof lctx localInsts used' decompileExpr
    let blockTac ← mkFocusedBlock chosenTacs
    allTacs := allTacs.push blockTac
    used' := used''
  return (allTacs, used')

def binderBaseName (idx : Nat) (name : Name) : String :=
  let raw := name.eraseMacroScopes.toString
  let lastSegment := (raw.splitOn ".").reverse.headD raw
  let cleaned := lastSegment.replace "'" ""
  if cleaned = "" || cleaned = "_" then s!"x{idx + 1}" else cleaned

def mkUniqueName (base : String) (used : List String) : String :=
  if !(used.contains base) then base
  else
    let rec loop (suffix remaining : Nat) : String :=
      let candidate := s!"{base}_{suffix}"
      match remaining with
      | 0 => candidate
      | Nat.succ remaining' =>
          if used.contains candidate then
            loop (suffix + 1) remaining'
          else
            candidate
    loop 1 (used.length + 1)

def chooseIntroName (idx : Nat) (userName : Name) (used : List String) : (String × List String) :=
  let base := binderBaseName idx userName
  let introName := mkUniqueName base used
  (introName, introName :: used)

def assignIntroNames (xs : Array Expr) (used0 : List String) : TacticM (List String × LocalContext × List String) := do
  let mut used : List String := used0
  let mut idx := 0
  let mut names : List String := []
  let mut lctx ← getLCtx
  for x in xs do
    let some fvarId := x.fvarId?
      | throwError "Unexpected non-fvar binder in proof term"
    let decl ← fvarId.getDecl
    let (introName, used') := chooseIntroName idx decl.userName used
    used := used'
    names := introName :: names
    let newName := Name.mkSimple introName
    lctx := lctx.setUserName fvarId newName
    idx := idx + 1
  return (names.reverse, lctx, used)

/-- Convert intro names to identifier syntax -/
def namesToIdents (names : List String) : Array Ident :=
  names.toArray.map (fun n => mkIdent (Name.mkSimple n))

/-- Check if an expression contains tactic-generated automation internals such
  as grind certificates or linear-arithmetic scaffolding. Walks at most 5000
  nodes. -/
def containsAutomationInternals (e : Expr) : Bool := Id.run do
  let mut stack : List Expr := [e]
  let mut count := 0
  while !stack.isEmpty && count < 5000 do
    let cur := stack.head!
    stack := stack.tail!
    count := count + 1
    match cur with
    | .const n _ =>
      let s := n.toString
      if s.startsWith "Int.Linear." || s.startsWith "Lean.Grind." || s.startsWith "Lean.RArray." then
        return true
    | .app f a => stack := f :: a :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .forallE _ t b _ => stack := t :: b :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | .mdata _ e => stack := e :: stack
    | _ => pure ()
  return false

/-- Check if a constant name is "structural" — i.e., part of the equality/congruence
    machinery that grind uses to chain proofs, not a meaningful library fact. -/
private def isStructuralConst (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Eq." || s.startsWith "congr" || s.startsWith "implies_congr" ||
  s.startsWith "forall_congr" || s.startsWith "eq_true" || s.startsWith "eq_false" ||
  s.startsWith "Classical." ||
  n == ``True.intro || n == ``False.rec || n == ``False.elim ||
  n == ``eagerReduce || n == ``id || n == ``funext || n == ``propext ||
  n == ``Iff.intro ||
  n == ``And.intro ||
  n == ``Or.inl || n == ``Or.inr || n == ``Not ||
  n == ``Bool.true || n == ``Bool.false ||
  n == ``Eq.refl || n == ``rfl

/-- Check if a constant name is grind-internal. -/
private def isGrindConst (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Int.Linear." || s.startsWith "Lean.Grind." || s.startsWith "Lean.RArray."

/-- Extract "interesting" subexpressions from a grind proof term.
  These are applications of library lemmas (not structural, not grind-internal)
  whose types are propositions. Callers can turn them into named `have` facts
  before continuing structural decompilation. -/
def extractGrindFacts (e : Expr) : MetaM (Array Expr) := do
  let mut result : Array Expr := #[]
  let mut stack : List Expr := [e]
  let mut seen : Std.HashSet UInt64 := {}
  let mut count := 0
  while !stack.isEmpty && count < 10000 do
    let cur := stack.head!
    stack := stack.tail!
    count := count + 1
    -- Deduplicate by pointer hash
    let h := cur.hash
    if seen.contains h then continue
    seen := seen.insert h
    match cur with
    | .app .. =>
      -- Peel to head constant
      let fn := cur.getAppFn
      let args := cur.getAppArgs
      match fn with
      | .const n _ =>
        if isGrindConst n then
          -- Don't collect grind applications, but DO recurse into their args
          -- because library facts may be passed as arguments to grind lemmas
          for a in args do stack := a :: stack
        else if isStructuralConst n then
          -- Recurse into args of structural constants
          for a in args do stack := a :: stack
        else
          -- Library/user lemma application — check if it's a Prop
          let ty ← try Meta.inferType cur catch _ => continue
          let sort ← try Meta.inferType ty catch _ => continue
          if sort.isProp then
            -- ty is a Prop — this is an interesting fact
            result := result.push cur
          -- Also recurse into args in case there are nested interesting facts
          for a in args do stack := a :: stack
      | .fvar .. =>
        -- fvar application — check if it's a Prop
        let ty ← try Meta.inferType cur catch _ => continue
        let sort ← try Meta.inferType ty catch _ => continue
        if sort.isProp then
          result := result.push cur
        for a in args do stack := a :: stack
      | _ =>
        for a in args do stack := a :: stack
        stack := fn :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .mdata _ e => stack := e :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | _ => pure ()
  return result

/-- Extract the names of library lemma constants from a grind proof term.
    Returns names that are not structural (Eq.*, congr*, etc.) and not grind-internal
    (Int.Linear.*, Lean.Grind.*, etc.). These represent the actual mathematical facts
    that grind used from the library. -/
def extractGrindLemmaNames (e : Expr) : Std.HashSet Name := Id.run do
  let mut result : Std.HashSet Name := {}
  let mut stack : List Expr := [e]
  let mut seen : Std.HashSet UInt64 := {}
  let mut count := 0
  while !stack.isEmpty && count < 10000 do
    let cur := stack.head!
    stack := stack.tail!
    count := count + 1
    let h := cur.hash
    if seen.contains h then continue
    seen := seen.insert h
    match cur with
    | .app .. =>
      let fn := cur.getAppFn
      let args := cur.getAppArgs
      match fn with
      | .const n _ =>
        if !isGrindConst n && !isStructuralConst n then
          result := result.insert n
        for a in args do stack := a :: stack
      | _ =>
        for a in args do stack := a :: stack
        stack := fn :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .mdata _ e => stack := e :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | _ => pure ()
  return result

end LeanDecomp
