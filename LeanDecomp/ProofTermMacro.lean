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
    let proofFmt ← withOptions (fun o =>
      let o := o.setBool `pp.notation false
      o.setBool `pp.all true) <|
        Meta.ppExpr expandedValue
    let typeFmt ← withOptions (fun o =>
      let o := o.setBool `pp.notation false
      o.setBool `pp.all true) <|
        Meta.ppExpr decl.type
    let typeStr := typeFmt.pretty
    let proofStr := proofFmt.pretty
    Lean.Meta.Tactic.TryThis.addSuggestion (← getRef)
      s!"theorem {constName} : {typeStr} :=\n  {proofStr}"

end LeanDecomp
