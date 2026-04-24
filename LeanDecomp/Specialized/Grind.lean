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

/-- Collect arguments of `abs.eq_1 x` subterms. grind's proof terms use
    `abs.eq_1 x` to unfold `|x|` into `max x (-x)` inside arithmetic
    certificates; that const flagging tells us the arg whose sign matters. -/
private partial def collectAbsEq1Args (e : Expr) : List Expr := Id.run do
  let mut result : List Expr := []
  let mut stack : List Expr := [e]
  let mut iters : Nat := 0
  while !stack.isEmpty && iters < 5000 do
    iters := iters + 1
    let cur := stack.head!
    stack := stack.tail!
    match cur with
    | .app .. =>
      let fn := cur.getAppFn
      let args := cur.getAppArgs
      if fn.isConstOf `abs.eq_1 && !args.isEmpty then
        result := args[args.size - 1]! :: result
      for a in args do stack := a :: stack
    | .lam _ _ b _ => stack := b :: stack
    | .letE _ _ v b _ => stack := v :: b :: stack
    | .mdata _ b => stack := b :: stack
    | _ => pure ()
  return result

/-- Check whether `e` is definitionally zero in its own type. -/
private def isZero (e : Expr) : MetaM Bool := do
  try
    let ty ← Meta.inferType e
    let zero ← Meta.mkAppOptM ``OfNat.ofNat #[some ty, some (mkNatLit 0), none]
    Meta.isDefEq e zero
  catch _ => pure false

/-- Structured description of a sign hypothesis for some expression `x`. -/
private structure SignHyp where
  /-- Name of the hypothesis in the local context. -/
  hypName : Name
  /-- Name of the `abs_of_*` lemma that matches this sign. -/
  absLemma : Name
  /-- If the hypothesis is the negation of an inequality, this is the helper
      lemma (e.g. `not_le.mp`, `not_lt.mp`) used to strip the negation. `none`
      means the hypothesis is already in positive form. -/
  negHelper : Option Name

/-- Find a hypothesis in the current local context that fixes the sign of `x`.
    Accepts the four direct inequality forms (`x ≤ 0`, `0 ≤ x`, `x < 0`, `0 < x`)
    and their negations, with an appropriate `not_le.mp` / `not_lt.mp` wrapper. -/
private def findSignHypForAbs (x : Expr) : MetaM (Option SignHyp) := do
  let lctx ← getLCtx
  let checkIneq (ty : Expr) : MetaM (Option (Name × Name)) := do
    let (fn, args) := peelArgs ty
    let some constName := fn.constName? | return none
    if args.length < 4 then return none
    let a := args[args.length - 2]!
    let b := args[args.length - 1]!
    if constName == ``LE.le then
      if (← Meta.isDefEq a x) && (← isZero b) then
        return some (constName, `abs_of_nonpos)
      if (← isZero a) && (← Meta.isDefEq b x) then
        return some (constName, `abs_of_nonneg)
    else if constName == ``LT.lt then
      if (← Meta.isDefEq a x) && (← isZero b) then
        return some (constName, `abs_of_neg)
      if (← isZero a) && (← Meta.isDefEq b x) then
        return some (constName, `abs_of_pos)
    return none
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some (_, absLemma) ← checkIneq ty then
      return some { hypName := decl.userName, absLemma, negHelper := none }
    -- Handle negated forms: `¬(x ≤ 0)`, `¬(0 < x)`, etc.
    let (notFn, notArgs) := peelArgs ty
    if notFn.isConstOf ``Not && notArgs.length == 1 then
      let inner := notArgs[0]!
      if let some (innerConst, _) ← checkIneq inner then
        -- Flip: `¬(a ≤ b) → b < a` via `not_le.mp`, `¬(a < b) → b ≤ a` via `not_lt.mp`.
        -- After flipping we need the corresponding abs_of_* for the flipped sign.
        let (_, innerArgs) := peelArgs inner
        let a := innerArgs[innerArgs.length - 2]!
        let b := innerArgs[innerArgs.length - 1]!
        let helper := if innerConst == ``LE.le then `not_le else `not_lt
        if innerConst == ``LE.le then
          -- `¬(x ≤ 0)` ↦ `0 < x` ↦ `abs_of_pos`
          if (← Meta.isDefEq a x) && (← isZero b) then
            return some { hypName := decl.userName, absLemma := `abs_of_pos,
                          negHelper := some helper }
          -- `¬(0 ≤ x)` ↦ `x < 0` ↦ `abs_of_neg`
          if (← isZero a) && (← Meta.isDefEq b x) then
            return some { hypName := decl.userName, absLemma := `abs_of_neg,
                          negHelper := some helper }
        else  -- LT.lt
          -- `¬(x < 0)` ↦ `0 ≤ x` ↦ `abs_of_nonneg`
          if (← Meta.isDefEq a x) && (← isZero b) then
            return some { hypName := decl.userName, absLemma := `abs_of_nonneg,
                          negHelper := some helper }
          -- `¬(0 < x)` ↦ `x ≤ 0` ↦ `abs_of_nonpos`
          if (← isZero a) && (← Meta.isDefEq b x) then
            return some { hypName := decl.userName, absLemma := `abs_of_nonpos,
                          negHelper := some helper }
  return none

/-- Return the names of hypotheses whose type syntactically contains `abs x`. -/
private def findHypsWithAbsOf (x : Expr) : MetaM (List Name) := do
  let lctx ← getLCtx
  let mut result : List Name := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let found := Expr.find? (fun sub =>
      let fn := sub.getAppFn
      let args := sub.getAppArgs
      match fn.constName? with
      | some name =>
        name == `abs && args.size >= 1 && args[args.size - 1]! == x
      | _ => false) ty
    if found.isSome then
      result := decl.userName :: result
  return result

/-- When grind's proof term uses `abs.eq_1 x` inside an arithmetic certificate
    and the local context has a sign hypothesis for `x`, emit
    `rw [abs_of_<sign> h] at <hyps>; lia`. This turns grind's opaque `abs`
    unfolding chain into a clean rewrite that `lia` can close. -/
def tryDecompAbsLeaf (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (_decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let absArgs := collectAbsEq1Args expr
    if absArgs.isEmpty then return none
    let x := absArgs[0]!
    let some sign ← findSignHypForAbs x | return none
    let targets ← findHypsWithAbsOf x
    let lemmaIdent : Ident := ⟨mkIdent sign.absLemma |>.raw.setInfo .none⟩
    let hypIdent : Ident := ⟨mkIdent sign.hypName |>.raw.setInfo .none⟩
    -- Build the rewrite term. For negated sign hyps, wrap with the negHelper
    -- so `abs_of_<sign>` sees a positive inequality.
    let appliedTerm : Term ← match sign.negHelper with
      | none => `($lemmaIdent:ident $hypIdent:ident)
      | some helper =>
        let helperMpIdent : Ident := ⟨mkIdent (Name.str helper "mp") |>.raw.setInfo .none⟩
        `($lemmaIdent:ident ($helperMpIdent:ident $hypIdent:ident))
    let rule ← `(Parser.Tactic.rwRule| $appliedTerm:term)
    let mut rwTacs : Array (TSyntax `tactic) := #[]
    for target in targets do
      let targetIdent : Ident := ⟨mkIdent target |>.raw.setInfo .none⟩
      let loc ← `(Lean.Parser.Tactic.location| at $targetIdent:term)
      let rwTac ← `(tactic| rw [$rule] $loc)
      rwTacs := rwTacs.push rwTac
    let rwGoalTac ← `(tactic| rw [$rule])
    let liaTac ← `(tactic| lia)
    let exprTy ← Meta.inferType expr
    let cand1 := rwTacs ++ #[liaTac]
    if ← LeanDecomp.candidateTacticsCloseGoal cand1 exprTy lctx localInsts then
      return some (cand1, used)
    let cand2 := rwTacs ++ #[rwGoalTac, liaTac]
    if ← LeanDecomp.candidateTacticsCloseGoal cand2 exprTy lctx localInsts then
      return some (cand2, used)
    return none

def handlers : List (Expr → LocalContext → LocalInstances → List String → DecompileCallback →
    TacticM (Option (Array (TSyntax `tactic) × List String))) := [
  tryDecompEqMpAutomationCast,
  tryDecompMt,
  tryDecompAbsLeaf
]

end LeanDecomp.Specialized.Grind
