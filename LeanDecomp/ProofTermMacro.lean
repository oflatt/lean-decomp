import Lean

namespace LeanDecomp
open Lean Elab Command Meta

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

private def assignIntroNames (xs : Array Expr) : MetaM (List String × LocalContext) := do
  let mut used : List String := []
  let mut idx := 0
  let mut names : List String := []
  let mut lctx ← getLCtx
  for x in xs do
    let some fvarId := x.fvarId?
      | throwError "Unexpected non-fvar binder in proof term"
    let decl ← fvarId.getDecl
    let base := binderBaseName idx decl.userName
    let introName := mkUniqueName base used
    used := introName :: used
    names := introName :: names
    let newName := Name.mkSimple introName
    lctx := lctx.setUserName fvarId newName
    idx := idx + 1
  return (names.reverse, lctx)

private def indentLines (s : String) (indent : Nat) : String :=
  let indentStr := String.ofList (List.replicate indent ' ')
  String.intercalate "\n" ((s.splitOn "\n").map (fun line => indentStr ++ line))

private def expandAuxiliaryProofs (e : Expr) : MetaM Expr := do
  Meta.deltaExpand e isAuxiliaryProofName


/--
`showProofTerm thmName` logs the kernel-level proof term associated with `thmName`.
This helps inspect what Lean actually stores for a theorem.
-/
elab "showProofTerm " thm:ident : command => do
  Command.liftTermElabM do
    let thmExpr ← Lean.Elab.Term.elabTerm thm none
    let some constName := thmExpr.getAppFn.constName?
      | throwError "{thm} does not refer to a constant"
    let env ← getEnv
    let some decl := env.find? constName
      | throwError "No declaration named {thm}"
    let some value := decl.value?
      | throwError "{thm} does not have an associated proof term"
      let expandedValue ← expandAuxiliaryProofs value
      Meta.lambdaTelescope expandedValue fun xs bodyExpr => do
        let (introNames, renamedLctx) ← assignIntroNames xs
        let localInstances ← getLocalInstances
        let bodyFmt ← withLCtx renamedLctx localInstances <|
          withOptions (fun o =>
            let o := o.setBool `pp.notation false
            o.setBool `pp.all true) <|
              Meta.ppExpr bodyExpr
        let bodyStr := bodyFmt.pretty
        let introsLine :=
          match introNames with
          | [] => ""
          | ns => s!"  intros {String.intercalate " " ns}\n"
        let exactSection := s!"  exact\n{indentLines bodyStr 4}"
        let tacticBlock := s!"{introsLine}{exactSection}"
        let typeFmt ← withOptions (fun o =>
          let o := o.setBool `pp.notation false
          o.setBool `pp.all true) <|
            Meta.ppExpr decl.type
        let typeStr := typeFmt.pretty
        let theoremStr := s!"theorem {constName} : {typeStr} := by\n{tacticBlock}"
        Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) theoremStr

end LeanDecomp
