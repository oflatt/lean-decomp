import Lean
import Lean.PrettyPrinter

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic

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

/-- Emit a tactic that may create multiple goals, then recursively decompile one
    proof term per generated goal into focused sub-blocks. This is the common
    shape used by theorem-style decompiler passes. -/
def emitTacticWithSubgoals (headTac : TSyntax `tactic) (subgoalProofs : Array Expr)
    (lctx : LocalContext) (localInsts : LocalInstances) (used : List String)
  (decompileExpr : DecompileCallback) : TacticM (Array (TSyntax `tactic) × List String) := do
  let mut allTacs : Array (TSyntax `tactic) := #[headTac]
  let mut used' := used
  for proof in subgoalProofs do
    let (subTacs, used'') ← decompileExpr proof lctx localInsts used'
    let blockTac ← mkFocusedBlock subTacs
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
