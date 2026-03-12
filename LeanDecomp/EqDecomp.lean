import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.Helpers

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

/-- Local argument peeler to avoid cross-module utility coupling. -/
private def peelApps (e : Expr) : Expr × List Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × List Expr :=
    match e with
    | Expr.app f arg => go f (arg :: acc)
    | _ => (e, acc)
  go e []

private def inferEqType? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← Meta.inferType e
  let (fn, args) := peelApps ty
  if fn.isConstOf ``Eq && args.length >= 3 then
    return some (args[0]!, args[1]!, args[2]!)
  return none

/-- Handle `congr` by naming function/argument equalities and recombining them. -/
def tryDecompCongr (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``congr then
      return none
    if args.length < 2 then
      return none

    let hEqFn := args[args.length - 2]!
    let hEqArg := args[args.length - 1]!
    let some _ ← inferEqType? hEqFn
      | return none
    let some _ ← inferEqType? hEqArg
      | return none

    let (eqFnTactics, used1) ← decompileExpr hEqFn lctx localInsts used
    let (eqFnName, used2) := chooseIntroName used1.length `hEqFn used1
    let eqFnIdent := mkIdent (Name.mkSimple eqFnName)
    let eqFnTyStx ← delabToRefinableSyntax (← Meta.inferType hEqFn)
    let eqFnSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqFnTactics]*)
    let letEqFnTac ← `(tactic| let $eqFnIdent : $eqFnTyStx := by $eqFnSeq)

    let (eqArgTactics, used3) ← decompileExpr hEqArg lctx localInsts used2
    let (eqArgName, used4) := chooseIntroName used3.length `hEqArg used3
    let eqArgIdent := mkIdent (Name.mkSimple eqArgName)
    let eqArgTyStx ← delabToRefinableSyntax (← Meta.inferType hEqArg)
    let eqArgSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqArgTactics]*)
    let letEqArgTac ← `(tactic| let $eqArgIdent : $eqArgTyStx := by $eqArgSeq)

    let exactTac ← `(tactic| exact congr $eqFnIdent $eqArgIdent)
    return some (#[letEqFnTac, letEqArgTac, exactTac], used4)

/-- Handle `congrArg` by naming the input equality and applying `congrArg`. -/
def tryDecompCongrArg (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``congrArg then
      return none
    if args.length < 2 then
      return none

    let f := args[args.length - 2]!
    let hEq := args[args.length - 1]!
    let some _ ← inferEqType? hEq
      | return none

    let (eqTactics, used1) ← decompileExpr hEq lctx localInsts used
    let (eqName, used2) := chooseIntroName used1.length `hEq used1
    let eqIdent := mkIdent (Name.mkSimple eqName)
    let eqTyStx ← delabToRefinableSyntax (← Meta.inferType hEq)
    let eqSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqTactics]*)
    let letEqTac ← `(tactic| let $eqIdent : $eqTyStx := by $eqSeq)

    let fStx ← delabToRefinableSyntax f
    let exactTac ← `(tactic| exact congrArg $fStx $eqIdent)
    return some (#[letEqTac, exactTac], used2)

/-- Handle `Eq.symm` by naming the input equality and reusing `Eq.symm`. -/
def tryDecompEqSymm (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``Eq.symm then
      return none

    let some inEq := args.getLast?
      | return none
    let some (_α, _lhs, _rhs) ← inferEqType? inEq
      | return none

    let (eqTactics, used') ← decompileExpr inEq lctx localInsts used
    let (eqName, used'') := chooseIntroName used'.length `hEq used'
    let eqIdent := mkIdent (Name.mkSimple eqName)
    let eqTyStx ← delabToRefinableSyntax (← Meta.inferType inEq)
    let eqTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqTactics]*)
    let letEqTac ← `(tactic| let $eqIdent : $eqTyStx := by $eqTacticSeq)

    let exactTac ← `(tactic| exact Eq.symm $eqIdent)
    return some (#[letEqTac, exactTac], used'')

/-- Handle `Eq.trans` by naming both sides and chaining them. -/
def tryDecompEqTrans (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``Eq.trans then
      return none
    if args.length < 2 then
      return none

    let eq1 := args[args.length - 2]!
    let eq2 := args[args.length - 1]!

    let some (_α1, _lhs, mid1) ← inferEqType? eq1
      | return none
    let some (_α2, mid2, _rhs) ← inferEqType? eq2
      | return none
    if !(← Meta.isDefEq mid1 mid2) then
      return none

    let (eq1Tactics, used1) ← decompileExpr eq1 lctx localInsts used
    let (name1, used2) := chooseIntroName used1.length `hEq used1
    let id1 := mkIdent (Name.mkSimple name1)
    let eq1TyStx ← delabToRefinableSyntax (← Meta.inferType eq1)
    let eq1Seq ← `(Lean.Parser.Tactic.tacticSeq| $[$eq1Tactics]*)
    let letEq1Tac ← `(tactic| let $id1 : $eq1TyStx := by $eq1Seq)

    let (eq2Tactics, used3) ← decompileExpr eq2 lctx localInsts used2
    let (name2, used4) := chooseIntroName used3.length `hEq used3
    let id2 := mkIdent (Name.mkSimple name2)
    let eq2TyStx ← delabToRefinableSyntax (← Meta.inferType eq2)
    let eq2Seq ← `(Lean.Parser.Tactic.tacticSeq| $[$eq2Tactics]*)
    let letEq2Tac ← `(tactic| let $id2 : $eq2TyStx := by $eq2Seq)

    let exactTac ← `(tactic| exact Eq.trans $id1 $id2)
    return some (#[letEq1Tac, letEq2Tac, exactTac], used4)

/-- Handle `Eq.mp` casts to `False` by naming the equality proof and applying
    it to the source proof (e.g. `True.intro`). -/
def tryDecompEqMp (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelApps expr
    let some constName := Expr.constName? fn
      | return none
    if constName != ``Eq.mp then
      return none

    let falseTy := mkConst ``False
    let exprTy ← Meta.inferType expr
    if !(← Meta.isDefEq exprTy falseTy) then
      return none

    let mut eqProofArg? : Option Expr := none
    let mut sourceTy? : Option Expr := none
    for a in args do
      let aTy ← Meta.inferType a
      let (tyFn, tyArgs) := peelApps aTy
      if tyFn.isConstOf ``Eq && tyArgs.length >= 3 then
        let lhs := tyArgs[1]!
        let rhs := tyArgs[2]!
        if (← Meta.isDefEq rhs falseTy) then
          eqProofArg? := some a
          sourceTy? := some lhs
          break

    let some eqProofArg := eqProofArg?
      | return none
    let some sourceTy := sourceTy?
      | return none

    let mut sourceProofArg? : Option Expr := none
    for a in args do
      if a == eqProofArg then
        continue
      let aTy ← Meta.inferType a
      if (← Meta.isDefEq aTy sourceTy) then
        sourceProofArg? := some a
        break

    let some sourceProofArg := sourceProofArg?
      | return none

    let (eqTactics, used') ← decompileExpr eqProofArg lctx localInsts used
    let (eqName, used'') := chooseIntroName used'.length `hEq used'
    let eqIdent := mkIdent (Name.mkSimple eqName)
    let eqTyStx ← delabToRefinableSyntax (← Meta.inferType eqProofArg)
    let eqTacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$eqTactics]*)
    let letEqTac ← `(tactic| let $eqIdent : $eqTyStx := by $eqTacticSeq)

    let sourceProofStx ← delabToRefinableSyntax sourceProofArg
    let exactTac ← `(tactic| exact Eq.mp $eqIdent $sourceProofStx)
    return some (#[letEqTac, exactTac], used'')

end LeanDecomp
