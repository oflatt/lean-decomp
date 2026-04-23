import Lean
import LeanDecomp.Helpers

namespace LeanDecomp.Specialized.Grind
open Lean Elab Meta Tactic

private def peelArgs (e : Expr) : Expr × List Expr :=
  let rec go (cur : Expr) (acc : List Expr) : Expr × List Expr :=
    match cur with
    | .app f arg => go f (arg :: acc)
    | _ => (cur, acc)
  go e []

/-- Strip `Eq.mp <cast> inner` when the cast is automation-generated junk and
    the inner proof already has the goal type. This is grind-specific today, so
    it lives in the grind specialization package rather than the core decompiler. -/
def tryDecompEqMpAutomationCast (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  let (fn, args) := peelArgs expr
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp then return none
  if args.length < 4 then return none
  let eqProof := args[2]!
  let inner := args[3]!
  if !containsAutomationInternals eqProof then return none
  let (innerFn, _) := peelArgs inner
  if innerFn.isConstOf ``True.intro then return none
  let innerWithArgs := (args.drop 4).foldl (init := inner) fun acc arg => mkApp acc arg
  withLCtx lctx localInsts do
    let goalType ← Meta.inferType expr
    let innerType ← Meta.inferType innerWithArgs
    if ← Meta.isDefEq goalType innerType then
      let (tactics, used') ← LeanDecomp.decompileOrExact innerWithArgs lctx localInsts used decompileExpr
      return some (tactics, used')
    return none

/-- `mt` takes an implication proof as a function-typed argument, so the generic
    theorem-app fallback treats it as an ordinary term and embeds it raw. Expose
    both arguments as subgoals instead so the decompiler can recurse into the
    implication proof structurally. -/
def tryDecompMt (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  let (fn, args) := peelArgs expr
  let some cname := fn.constName? | return none
  if cname != ``mt then return none
  if args.length < 4 then return none
  let impProof := args[2]!
  let negProof := args[3]!
  let mtIdent : Ident := ⟨mkIdent ``mt |>.raw.setInfo .none⟩
  let headTac ← `(tactic| apply $mtIdent:ident)
  let result ← LeanDecomp.emitTacticWithSubgoals headTac #[impProof, negProof] lctx localInsts used decompileExpr
  return some result

def handlers : List (Expr → LocalContext → LocalInstances → List String → DecompileCallback →
    TacticM (Option (Array (TSyntax `tactic) × List String))) := [
  tryDecompEqMpAutomationCast,
  tryDecompMt
]

end LeanDecomp.Specialized.Grind
