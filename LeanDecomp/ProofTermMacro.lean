import Lean

namespace LeanDecomp
open Lean Elab Command Meta

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
    let typeFmt ← Meta.ppExpr decl.type
    let proofFmt ← Meta.ppExpr value
    logInfo m!"proof term for {thm}:\n{proofFmt}"
    let suggestion := m!"theorem {constName} : {typeFmt} :=\n  {proofFmt}"
    logInfo m!"Try rewriting `{constName}` to use the raw proof term:\n{suggestion}"

end LeanDecomp
