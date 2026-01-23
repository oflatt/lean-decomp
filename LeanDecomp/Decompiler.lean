import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

private def binderBaseName (idx : Nat) (name : Name) : String :=
  let raw := name.eraseMacroScopes.toString
  let lastSegment := (raw.splitOn ".").reverse.headD raw
  let cleaned := lastSegment.replace "'" ""
  if cleaned = "" || cleaned = "_" then s!"x{idx + 1}" else cleaned

private def mkUniqueName (base : String) (used : List String) : String :=
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

private def chooseIntroName (idx : Nat) (userName : Name) (used : List String) : (String × List String) :=
  let base := binderBaseName idx userName
  let introName := mkUniqueName base used
  (introName, introName :: used)

private def assignIntroNames (xs : Array Expr) (used0 : List String) : MetaM (List String × LocalContext × List String) := do
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

/-- AST representation of tactics for rendering. -/
inductive TacticAst where
  | intro (names : List String)
  | simple (text : String)
  | exact (term : String)
  | seq (tactics : List TacticAst)

namespace TacticAst

partial def render : TacticAst → List String
  | intro [] => []
  | intro names => [s!"  intro {String.intercalate " " names}"]
  | simple text => [s!"  {text}"]
  | exact term => [s!"  exact {term}"]
  | seq tactics => tactics.flatMap render

end TacticAst

mutual

  /-- Convert a proof term expression into a TacticAst. -/
  partial def renderExprToTactics (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (TacticAst × List String) := do
    withLCtx lctx localInsts do
      Meta.lambdaTelescope expr fun xs body => do
        if xs.size > 0 then
          -- Use the current local context from inside lambdaTelescope
          let telescopeLctx ← getLCtx
          let telescopeInsts ← getLocalInstances
          renderIntroCase xs body telescopeLctx telescopeInsts used
        else
          match ← renderByContradictionCase expr lctx localInsts used with
          | some res => pure res
          | none => do
              let termStx ← delabToRefinableSyntax expr
              let fmt ← ppTerm termStx
              let termStr := fmt.pretty
              return (TacticAst.exact termStr, used)

  private partial def renderIntroCase (xs : Array Expr) (body : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (TacticAst × List String) := do
    withLCtx lctx localInsts do
      let (introNames, newLctx, used') ← assignIntroNames xs used
      let newLocalInsts ← getLocalInstances
      let (bodyTactics, used'') ← renderExprToTactics body newLctx newLocalInsts used'
      let introNode :=
        if introNames.isEmpty then TacticAst.seq []
        else TacticAst.intro introNames
      return (TacticAst.seq [introNode, bodyTactics], used'')

  private partial def renderByContradictionCase (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : MetaM (Option (TacticAst × List String)) := do
    withLCtx lctx localInsts do
      let rec peel (e : Expr) (acc : List Expr) : Expr × List Expr :=
        match e with
        | Expr.app f arg => peel f (arg :: acc)
        | _ => (e, acc)
      let (fn, args) := peel expr []
      let some constName := Expr.constName? fn
        | return none
      if constName != ``Classical.byContradiction then
        return none
      let some handler := args.getLast?
        | return none
      let handlerType ← Meta.inferType handler
      Meta.forallTelescope handlerType fun binders _ => do
        if binders.size = 1 then
          let binder := binders[0]!
          let lctxWithBinder ← getLCtx
          let some fvarId := binder.fvarId?
            | throwError "Unexpected non-fvar binder in byContradiction handler"
          let decl ← fvarId.getDecl
          let (binderName, used') := chooseIntroName used.length decl.userName used
          let renamedBinderLctx := lctxWithBinder.setUserName fvarId (Name.mkSimple binderName)
          let binderLocalInsts ← getLocalInstances
          let applied := Expr.app handler binder
          let (bodyTactics, used'') ← renderExprToTactics applied renamedBinderLctx binderLocalInsts used'
          let header := TacticAst.seq
            [ TacticAst.simple "apply Classical.byContradiction",
              TacticAst.simple s!"intro {binderName}" ]
          return some (TacticAst.seq [header, bodyTactics], used'')
        else
          return none
end

end LeanDecomp
