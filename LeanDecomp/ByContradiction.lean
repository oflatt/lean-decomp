import Lean
import LeanDecomp.Helpers
import LeanDecomp.Helpers.ArithTerminal
import LeanDecomp.Specialized

namespace LeanDecomp

open Lean Elab Meta Tactic

/-- Handle `Classical.byContradiction <handler>` proofs by emitting
    `apply Classical.byContradiction; intro <neg-hyp>` and recursively
    decompiling the body.  Four-phase fallback (specialized → structural →
    arithmetic terminal → validateOrExact) — see inline comments for the
    rationale.  Extracted from `Decompiler.lean`'s mutual block so handler-
    only edits don't trigger a full Decompiler.lean recompile. -/
def tryDecompByContradiction (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (decompileExpr : DecompileCallback)
    : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
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
        let binderName ← chooseIntroName (← getUsed).length decl.userName
        let renamedBinderLctx := lctxWithBinder.setUserName fvarId (Name.mkSimple binderName)
        let binderLocalInsts ← getLocalInstances
        let applied := Expr.app handler binder
        let binderIdent := mkIdent (Name.mkSimple binderName)
        -- Use mkIdent with no info to avoid hygiene marks (✝) in pretty-printed output
        let byContradictionIdent : Ident := ⟨mkIdent ``Classical.byContradiction |>.raw.setInfo .none⟩
        let applyTac ← `(tactic| apply $byContradictionIdent:ident)
        let introTac ← `(tactic| intro $binderIdent:ident)
        let exprTy ← instantiateMVars (← Meta.inferType expr)
        let savedUsed ← getUsed
        -- Phase A — specialized handler short-circuit.  When grind's
        -- contradiction body is something like a deeply-nested `Or.casesOn`
        -- tree that ultimately resolves to an `abs`-case-split or a single
        -- `lia` (think Int L47 — `natAbs |a| = natAbs a`), the structural
        -- recursion below would emit ~50 lines of nested `cases hOr_N`
        -- with 6+ inner `lia` calls.  But our specialized handlers
        -- (`tryDecompAbsCaseSplitContradiction`, `tryDecompFalseFromLia`,
        -- etc.) can recognize the OUTER shape and emit a flat 5-line
        -- equivalent.  Try them first — if the candidate validates,
        -- skip the structural recursion entirely.  Big wins on
        -- arithmetic-leaf contradictions where grind's case-split tree
        -- is decoration over a single decidable predicate.
        if let some branchTactics ←
            trySpecializedDecompHandlers applied renamedBinderLctx binderLocalInsts decompileExpr then
          let candidate := #[applyTac, introTac] ++ branchTactics
          if ← LeanDecomp.candidateTacticsCloseGoal candidate exprTy lctx localInsts then
            return some candidate
          set savedUsed
        -- Phase B — structural decompilation of the contradiction body.
        -- Keeps contradiction-shaped proofs stable when no specialized
        -- handler matches the outer shape.  When the candidate fails
        -- *tight* validation (`candidateTacticsCloseGoal`, capped at
        -- `candidateMaxHeartbeats`), cache the body tactics for Phase D
        -- to retry under looser validation rather than recomputing.
        let mut phaseBBodyTactics : Option (Array (TSyntax `tactic)) := none
        try
          let bodyTactics ← decompileExpr applied renamedBinderLctx binderLocalInsts
          let candidate := #[applyTac, introTac] ++ bodyTactics
          if ← LeanDecomp.candidateTacticsCloseGoal candidate exprTy lctx localInsts then
            return some candidate
          phaseBBodyTactics := some bodyTactics
        catch _ =>
          set savedUsed
        set savedUsed
        -- Phase C — arithmetic terminal fallback (`lia` / `grind_order` / etc).
        if let some branchTactics ←
            tryDecompArithmeticTerminalPasses applied renamedBinderLctx binderLocalInsts then
          return some (#[applyTac, introTac] ++ branchTactics)
        -- Phase D — final fallback through validateOrExact.  Reuse
        -- Phase B's body tactics when available: validateOrExact's
        -- `subproofTacticsCloseGoal` has no heartbeat cap, so a candidate
        -- that failed Phase B only due to budget exhaustion has a second
        -- chance here.  When phaseBBodyTactics is none (Phase B threw),
        -- recompute — the throw means we have nothing to reuse.
        let result ← LeanDecomp.validateOrExact expr lctx localInsts do
          match phaseBBodyTactics with
          | some cached => return #[applyTac, introTac] ++ cached
          | none =>
            let bodyTactics ← decompileExpr applied renamedBinderLctx binderLocalInsts
            return #[applyTac, introTac] ++ bodyTactics
        return some result
      else
        return none

end LeanDecomp
