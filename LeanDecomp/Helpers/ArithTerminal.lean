import Lean
import LeanDecomp.Helpers

namespace LeanDecomp

open Lean Elab Meta Tactic

partial def containsArithRelevantConst (e : Expr) : Bool :=
  Expr.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some n =>
        n == ``Int || n == ``Nat || n == ``LE.le || n == ``LT.lt ||
          n == ``GE.ge || n == ``GT.gt || n == ``Dvd.dvd ||
          n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul ||
          n == ``OfNat.ofNat || n == ``Nat.succ || n == ``Nat.sub || n == ``Int.sub ||
          n == ``Int.add || n == ``Int.mul || n == ``Nat.add || n == ``Nat.mul
    | none => false) e |>.isSome

partial def containsArithmeticAutomationConst (e : Expr) : Bool :=
  Expr.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some n =>
        let s := toString n
        s.startsWith "Int.Linear." ||
          s.startsWith "Nat.Linear." ||
          s.startsWith "Lean.Grind.Order." ||
          s.startsWith "Lean.Grind.CommRing."
    | none => false) e |>.isSome

def isArithmeticLikeGoal (expr : Expr) : MetaM Bool := do
  let ty ← instantiateMVars (← Meta.inferType expr)
  pure <|
    containsArithRelevantConst ty ||
      containsArithRelevantConst expr ||
      containsArithmeticAutomationConst expr

def tryValidatedTerminalTactic (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (tac : TSyntax `tactic)
    : DecompM (Option (Array (TSyntax `tactic))) := do
  let expectedType ← instantiateMVars (← Meta.inferType expr)
  if ← LeanDecomp.candidateTacticsCloseGoal #[tac] expectedType lctx localInsts then
    return some #[tac]
  return none

def tryDecompArithmeticTerminalPasses (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances)
    : DecompM (Option (Array (TSyntax `tactic))) := do
  withLCtx lctx localInsts do
    if !(← isArithmeticLikeGoal expr) then
      return none
    let liaTac ← `(tactic| lia)
    if let some result ← tryValidatedTerminalTactic expr lctx localInsts liaTac then
        return some result
    let orderTac ← `(tactic| grind_order)
    if let some result ← tryValidatedTerminalTactic expr lctx localInsts orderTac then
      return some result
    let linarithTac ← `(tactic| grind_linarith)
    tryValidatedTerminalTactic expr lctx localInsts linarithTac

end LeanDecomp
