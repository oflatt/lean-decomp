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

private def nameHasPrefix (pref : String) (name : Name) : Bool :=
  name.toString.startsWith pref

private partial def exprContainsConst (p : Name → Bool) : Expr → Bool
  | .const name _ => p name
  | .app fn arg => exprContainsConst p fn || exprContainsConst p arg
  | .lam _ ty body _ => exprContainsConst p ty || exprContainsConst p body
  | .forallE _ ty body _ => exprContainsConst p ty || exprContainsConst p body
  | .letE _ ty val body _ =>
      exprContainsConst p ty || exprContainsConst p val || exprContainsConst p body
  | .mdata _ body => exprContainsConst p body
  | .proj _ _ body => exprContainsConst p body
  | _ => false

private partial def expandAuxiliaryProofsAux (env : Environment) (visited : NameSet)
    (e : Expr) : MetaM Expr := do
  match e with
  | .const name lvls =>
      if visited.contains name || !isAuxiliaryProofName name then
        return e
      else
    match env.find? name with
    | some decl =>
      match decl.value? with
      | some val =>
        let body := val.instantiateLevelParams decl.levelParams lvls
        expandAuxiliaryProofsAux env (visited.insert name) body
      | none => return e
    | none => return e
  | .app fn arg =>
      return .app (← expandAuxiliaryProofsAux env visited fn)
        (← expandAuxiliaryProofsAux env visited arg)
  | .lam n ty body bi =>
      return .lam n (← expandAuxiliaryProofsAux env visited ty)
        (← expandAuxiliaryProofsAux env visited body) bi
  | .forallE n ty body bi =>
      return .forallE n (← expandAuxiliaryProofsAux env visited ty)
        (← expandAuxiliaryProofsAux env visited body) bi
  | .letE n ty val body nonDep =>
      return .letE n (← expandAuxiliaryProofsAux env visited ty)
        (← expandAuxiliaryProofsAux env visited val)
        (← expandAuxiliaryProofsAux env visited body) nonDep
  | .mdata md body =>
      return .mdata md (← expandAuxiliaryProofsAux env visited body)
  | .proj type idx body =>
      return .proj type idx (← expandAuxiliaryProofsAux env visited body)
  | _ => return e

private def expandAuxiliaryProofs (e : Expr) : MetaM Expr := do
  expandAuxiliaryProofsAux (← getEnv) NameSet.empty e

/--
`showProofTerm thmName` logs the kernel-level proof term associated with `thmName`.
This helps inspect what Lean actually stores for a theorem.
-/
elab "showProofTerm " thm:ident : command => do
  Command.liftTermElabM do
    let thmExpr ← Lean.Elab.Term.elabTerm thm none
    let some constName := thmExpr.constName?
      | throwError "{thm} does not refer to a constant"
    let env ← getEnv
    let some decl := env.find? constName
      | throwError "No declaration named {thm}"
    let some value := decl.value?
      | throwError "{thm} does not have an associated proof term"
    let expandedValue ← expandAuxiliaryProofs value
    let typeFmt ← Meta.ppExpr decl.type
    let proofFmt ← Meta.ppExpr expandedValue
    logInfo m!"proof term for {thm}:\n{proofFmt}"
    let typeStr := typeFmt.pretty
    let proofStr := proofFmt.pretty
    let usesGrind := exprContainsConst (nameHasPrefix "Lean.Grind.") expandedValue
    let suggestion :=
      if usesGrind then
        s!"theorem {constName} : {typeStr} :=\n  by\n    grind"
      else
        s!"theorem {constName} : {typeStr} :=\n  {proofStr}"
    Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) suggestion
      (header := s!"Try rewriting `{constName}` to use the raw proof term:\n")

end LeanDecomp
