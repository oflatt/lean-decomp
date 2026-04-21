import Lean
import LeanDecomp.Helpers
import LeanDecomp.Specialized.Grind

namespace LeanDecomp
open Lean Elab Meta Tactic

/-- Specialized decompilation hook. These handlers sit alongside the core
    decompiler and are intended for package-specific logic such as grind-only
    proof-term cleanup. -/
abbrev SpecializedDecompHandler :=
  Expr → LocalContext → LocalInstances → List String → DecompileCallback →
    TacticM (Option (Array (TSyntax `tactic) × List String))

def specializedDecompHandlers : List SpecializedDecompHandler :=
  LeanDecomp.Specialized.Grind.handlers

/-- Run specialized handlers in order, returning the first successful result. -/
def trySpecializedDecompHandlers (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  for handler in specializedDecompHandlers do
    if let some result ← handler expr lctx localInsts used decompileExpr then
      return some result
  return none

end LeanDecomp
