import Lean
import LeanDecomp.Helpers

namespace LeanDecomp

open Lean Elab Meta Tactic

/-- Handle the lambda-binder case at the top of `decompileExpr`: emit
    `intro x1 x2 ...` for the telescoped binders, then recurse into the
    body via the callback.  Extracted from `Decompiler.lean`'s mutual
    block so handler-only edits don't trigger a full Decompiler.lean
    recompile. -/
def tryDecompIntro (xs : Array Expr) (body : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
    : DecompM (Array (TSyntax `tactic)) := do
  withLCtx lctx localInsts do
    let (introNames, newLctx) ← assignIntroNames xs
    let newLocalInsts ← getLocalInstances
    let bodyTactics ← decompileExpr body newLctx newLocalInsts
    let introTac ← if introNames.isEmpty then
        pure #[]
      else
        let idents := namesToIdents introNames
        let tac ← `(tactic| intro $[$idents]*)
        pure #[tac]
    return introTac ++ bodyTactics

end LeanDecomp
