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

private def chooseIntroName (idx : Nat) (userName : Name) (used : List String) : (String × List String) :=
  let base := binderBaseName idx userName
  let introName := mkUniqueName base used
  (introName, introName :: used)

private def assignIntroNames (xs : Array Expr) : MetaM (List String × LocalContext × List String) := do
  let mut used : List String := []
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

private def indentLines (s : String) (indent : Nat) : String :=
  let indentStr := String.ofList (List.replicate indent ' ')
  String.intercalate "\n" ((s.splitOn "\n").map (fun line => indentStr ++ line))

private def expandAuxiliaryProofs (e : Expr) : MetaM Expr := do
  Meta.deltaExpand e isAuxiliaryProofName

private def formatByContradiction? (bodyExpr : Expr) (renamedLctx : LocalContext)
    (usedNames : List String) (baseLocalInstances : LocalInstances) : MetaM (Option String) := do
  withLCtx renamedLctx baseLocalInstances do
    let rec peel (e : Expr) (acc : List Expr) : Expr × List Expr :=
      match e with
      | Expr.app f arg => peel f (arg :: acc)
      | _ => (e, acc)
    let (fn, args) := peel bodyExpr []
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
        let (binderName, _) := chooseIntroName usedNames.length decl.userName usedNames
        let renamedBinderLctx := lctxWithBinder.setUserName fvarId (Name.mkSimple binderName)
        let binderLocalInstances ← getLocalInstances
        let applied := Expr.app handler binder
        let bodyFmt ← withLCtx renamedBinderLctx binderLocalInstances <|
          withOptions (fun o =>
            let o := o.setBool `pp.notation false
            o.setBool `pp.all true) <|
              Meta.ppExpr applied
        let bodyStr := bodyFmt.pretty
        let block := s!"  classical\n  apply Classical.byContradiction\n  intro {binderName}\n  exact\n{indentLines bodyStr 4}"
        return some block
      else
        return none


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
        let (introNames, renamedLctx, usedNames) ← assignIntroNames xs
        let localInstances ← getLocalInstances
        let specialBlock? ← formatByContradiction? bodyExpr renamedLctx usedNames localInstances
        let exactSection ←
          match specialBlock? with
          | some block => pure block
          | none => do
              let bodyFmt ← withLCtx renamedLctx localInstances <|
                withOptions (fun o =>
                  let o := o.setBool `pp.notation false
                  o.setBool `pp.all true) <|
                    Meta.ppExpr bodyExpr
              let bodyStr := bodyFmt.pretty
              pure s!"  exact\n{indentLines bodyStr 4}"
        let introsLine :=
          match introNames with
          | [] => ""
          | ns => s!"  intros {String.intercalate " " ns}\n"
        let tacticBlock := s!"{introsLine}{exactSection}"
        let scriptTerm := s!"by\n{tacticBlock}"
        let scriptSyntax ←
          match Parser.runParserCategory (env := env) `term scriptTerm with
          | Except.ok stx => pure stx
          | Except.error err => throwError s!"Failed to parse generated tactic block:\n{err}"
        let savedState ← Meta.saveState
        try
          let elaborated ← Term.withDeclName constName <|
            Term.elabTerm scriptSyntax (some decl.type)
          Term.synthesizeSyntheticMVars
          _ ← instantiateMVars elaborated
        catch err =>
          let msg ← err.toMessageData.format
          throwError s!"Generated tactic block failed to elaborate:\n{msg.pretty}"
        finally
          savedState.restore
        let typeFmt ← withOptions (fun o =>
          let o := o.setBool `pp.notation false
          o.setBool `pp.all true) <|
            Meta.ppExpr decl.type
        let typeStr := typeFmt.pretty
        let theoremStr := s!"theorem {constName} : {typeStr} := by\n{tacticBlock}"
        Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) theoremStr

end LeanDecomp
