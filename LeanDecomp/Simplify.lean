import Lean
import LeanDecomp.CasesOn

/-! # Proof term simplification pass

This module provides a recursive simplification pass over proof term `Expr`s
*before* the decompiler converts them to tactic syntax. Each simplification
rewrites a proof term into a simpler, logically equivalent term so that the
decompiler can produce cleaner output.

Note: some simplifications (like contradiction detection in casesOn branches)
require tactic-level context and live in the decompiler instead — the types
only match after `cases` unification.
-/

namespace LeanDecomp
open Lean Meta

-- ═══════════════════════════════════════════════════════
-- Analysis helpers (exported for use by the decompiler)
-- ═══════════════════════════════════════════════════════

/-- Extract a contradiction pair from an `Eq.mp (eq_true/eq_false chain) True.intro`
    proof of `False`. Returns `some (h, h')` where `h : P` and `h' : ¬P`. -/
def extractContradiction (falseProof : Expr) : Option (Expr × Expr) := do
  let (fn, args) := peelArgs falseProof
  let cname ← fn.constName?
  guard (cname == ``Eq.mp)
  guard (args.length == 4)
  let he := args[2]!
  let witness := args[3]!
  let (witFn, _) := peelArgs witness
  let witName ← witFn.constName?
  guard (witName == ``True.intro)
  let mut eqTrueArg : Option Expr := none
  let mut eqFalseArg : Option Expr := none
  let mut worklist := [he]
  while !worklist.isEmpty do
    let e := worklist.head!
    worklist := worklist.tail!
    let (efn, eargs) := peelArgs e
    if let some ename := efn.constName? then
      if ename == ``Eq.trans then
        if eargs.length >= 6 then
          worklist := eargs[4]! :: eargs[5]! :: worklist
      else if ename == ``Eq.symm then
        if eargs.length >= 4 then
          worklist := eargs[3]! :: worklist
      else if ename == ``eq_true then
        if eargs.length >= 2 then
          eqTrueArg := some eargs[1]!
      else if ename == ``eq_false then
        if eargs.length >= 2 then
          eqFalseArg := some eargs[1]!
      else if ename == ``eq_false' then
        if eargs.length >= 2 then
          eqFalseArg := some eargs[1]!
  let h ← eqTrueArg
  let h' ← eqFalseArg
  return (h, h')

/-- Extract the "core" fvar application from an expression by stripping
    `Eq.mp normalization` wrappers. Returns `some (coreExpr, extraArgs)` where
    `coreExpr` is the fvar application and `extraArgs` are arguments applied after
    the transport. For `Eq.mp <norm_eq> (f x₁ ... xₙ) y₁ ... yₘ`, returns
    `(f x₁ ... xₙ, #[y₁, ..., yₘ])`. Returns `none` if no fvar core is found. -/
def extractCoreFVarApp (e : Expr) : Option (Expr × Array Expr) := Id.run do
  let mut cur := e
  let mut allExtraArgs : Array Expr := #[]
  for _ in List.range 20 do  -- bounded iteration
    let (fn, args) := peelArgs cur
    let some cname := fn.constName? | break
    if cname != ``Eq.mp || args.length < 4 then break
    let base := args[3]!
    let extraArgs := (args.drop 4).toArray
    allExtraArgs := allExtraArgs ++ extraArgs
    -- Check if base is a fvar application
    if base.getAppFn.isFVar then
      return some (base, allExtraArgs)
    cur := base
  -- Check if the final `cur` is a fvar application
  if cur.getAppFn.isFVar then
    return some (cur, allExtraArgs)
  return none

/-- Collect all proof arguments from `eq_true` nodes in an equality chain.
    Also walks through `Eq.trans`, `Eq.symm`, `congrArg`, `congr`, and
    grind-specific lemmas like `imp_eq_of_eq_true_left`, `and_eq_of_eq_true_right`, etc.
    Returns the list of proof expressions found as `eq_true` arguments. -/
def collectEqTrueProofs (eqChain : Expr) : Array Expr := Id.run do
  let mut result : Array Expr := #[]
  let mut worklist := [eqChain]
  let mut visited := 0
  while !worklist.isEmpty && visited < 5000 do
    let e := worklist.head!
    worklist := worklist.tail!
    visited := visited + 1
    let (efn, eargs) := peelArgs e
    let some ename := efn.constName? | continue
    -- Standard equality chain nodes
    if ename == ``Eq.trans then
      if eargs.length >= 6 then
        worklist := eargs[4]! :: eargs[5]! :: worklist
    else if ename == ``Eq.symm then
      if eargs.length >= 4 then
        worklist := eargs[3]! :: worklist
    else if ename == ``eq_true then
      if eargs.length >= 2 then
        result := result.push eargs[1]!
    else if ename == ``eq_false || ename == ``eq_false' then
      if eargs.length >= 2 then
        result := result.push eargs[1]!
    -- congrArg f (h : a = b) : f a = f b — walk the equality argument
    else if ename == ``congrArg then
      if eargs.length >= 5 then
        worklist := eargs[4]! :: worklist
    -- congr (h₁ : f = g) (h₂ : a = b) : f a = g b
    else if ename == ``congr then
      if eargs.length >= 6 then
        worklist := eargs[4]! :: eargs[5]! :: worklist
    -- congrFun (h : f = g) (a) : f a = g a / congrFun' is the same
    else if ename == ``congrFun || ename == ``congrFun' then
      if eargs.length >= 5 then
        worklist := eargs[3]! :: worklist
    -- Grind lemmas: all take an eq proof as an argument, follow it
    else if ename == ``Lean.Grind.imp_eq_of_eq_true_left then
      -- imp_eq_of_eq_true_left {a b} (h : a = True) : (a → b) = b
      if eargs.length >= 3 then
        worklist := eargs[2]! :: worklist
    else if ename == ``Lean.Grind.and_eq_of_eq_true_right then
      -- and_eq_of_eq_true_right {a b} (h : b = True) : (a ∧ b) = a
      if eargs.length >= 3 then
        worklist := eargs[2]! :: worklist
    else if ename == ``Lean.Grind.and_eq_of_eq_true_left then
      -- and_eq_of_eq_true_left {a b} (h : a = True) : (a ∧ b) = b
      if eargs.length >= 3 then
        worklist := eargs[2]! :: worklist
    else if ename == ``Lean.Grind.eq_true_of_and_eq_true_right then
      -- eq_true_of_and_eq_true_right {a b} (h : (a ∧ b) = True) : b = True
      if eargs.length >= 3 then
        worklist := eargs[2]! :: worklist
    else if ename == ``Lean.Grind.eq_true_of_and_eq_true_left then
      -- eq_true_of_and_eq_true_left {a b} (h : (a ∧ b) = True) : a = True
      if eargs.length >= 3 then
        worklist := eargs[2]! :: worklist
    else if ename == ``Lean.Grind.eq_false_of_not_eq_true then
      -- eq_false_of_not_eq_true {a} (h : (¬a) = True) : a = False
      if eargs.length >= 2 then
        worklist := eargs[1]! :: worklist
    else if ename == ``Lean.Grind.iff_eq then
      -- iff_eq (p q) : (p ↔ q) = (p = q) — no proof arg to follow
      pure ()
    -- Eq.mp itself can appear nested
    else if ename == ``Eq.mp then
      if eargs.length >= 4 then
        worklist := eargs[2]! :: eargs[3]! :: worklist
    -- forall_congr, implies_congr — walk their proof arguments
    else if ename == ``forall_congr then
      if eargs.length >= 4 then
        worklist := eargs[3]! :: worklist
    else if ename == ``implies_congr then
      if eargs.length >= 5 then
        worklist := eargs[3]! :: eargs[4]! :: worklist
  return result

-- ═══════════════════════════════════════════════════════
-- Individual simplification rules (Expr → Option Expr)
-- ═══════════════════════════════════════════════════════

/-- Simplify `False.rec/False.elim/False.casesOn (Eq.mp eq_chain True.intro)`
    into `absurd h h'` when the types are definitionally equal. -/
private def simplifyFalseElim (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``False.rec && cname != ``False.elim && cname != ``False.casesOn then
    return none
  let some falseArg := args.findSome? (fun arg =>
    let (afn, _) := peelArgs arg
    if afn.constName? == some ``Eq.mp then some arg else none) | return none
  let some (h, h') := extractContradiction falseArg | return none
  try
    let result ← mkAppM ``absurd #[h, h']
    return some result
  catch _ =>
    return none


/-- Strip `@id T body` → `body`. -/
private def simplifyId (e : Expr) : Option Expr := do
  let .app fn body := e | failure
  let .app idConst _typeArg := fn | failure
  let cname ← idConst.constName?
  guard (cname == ``id)
  return body

/-- Unfold grind marker wrappers that are just identity functions.
    `Lean.Grind.alreadyNorm p` → `p` (it's `def alreadyNorm (p : Prop) : Prop := p`)
    `Lean.Grind.nestedProof p h` → `h` (it's `def nestedProof (p : Prop) {h : p} : p := h`)
    `Lean.Grind.Marker a` → `a` (it's `@[inline] def Marker {α} (a : α) : α := a`)
    `Lean.Grind.em p` → `Classical.em p` (it's `theorem em (p) : alreadyNorm p ∨ alreadyNorm (¬ p) := Classical.em p`) -/
private def simplifyGrindWrappers (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname == ``Lean.Grind.alreadyNorm then
    -- alreadyNorm p := p, so just delta-expand
    let reduced ← Meta.deltaExpand e (· == ``Lean.Grind.alreadyNorm)
    if reduced != e then return some reduced
    return none
  if cname == ``Lean.Grind.nestedProof then
    let reduced ← Meta.deltaExpand e (· == ``Lean.Grind.nestedProof)
    if reduced != e then return some reduced
    return none
  if cname == ``Lean.Grind.Marker then
    let reduced ← Meta.deltaExpand e (· == ``Lean.Grind.Marker)
    if reduced != e then return some reduced
    return none
  if cname == ``Lean.Grind.em then
    -- em p : alreadyNorm p ∨ alreadyNorm (¬ p) := Classical.em p
    -- After unfolding alreadyNorm, this is just Classical.em p
    if args.length >= 1 then
      let p := args[0]!
      return some (mkApp (mkConst ``Classical.em []) p)
    return none
  return none

/-- Reduce `intro_with_eq p p' q he k hp` → `k (Eq.mp he hp)` (or `k hp` when p ≡ p'). -/
private def simplifyIntroWithEq (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Lean.Grind.intro_with_eq && cname != ``Lean.Grind.intro_with_eq' then
    return none
  if args.length == 6 then
    -- Fully applied: intro_with_eq p p' q he k hp
    let p := args[0]!; let p' := args[1]!; let k := args[4]!; let hp := args[5]!
    let arg ← if (← Meta.withDefault <| Meta.isDefEq p p') then
      pure hp
    else
      let he := args[3]!
      pure (mkApp4 (mkConst ``Eq.mp [Level.zero]) p p' he hp)
    return some (Expr.app k arg).headBeta
  else if args.length == 5 then
    -- Partially applied: returns p → q, construct lambda
    let p := args[0]!; let p' := args[1]!; let k := args[4]!
    let body ← if (← Meta.withDefault <| Meta.isDefEq p p') then
      pure (Expr.lam `hp p
        (Expr.app (k.liftLooseBVars 0 1) (.bvar 0))
        .default)
    else
      let he := args[3]!
      pure (Expr.lam `hp p
        (Expr.app (k.liftLooseBVars 0 1)
          (mkApp4 (mkConst ``Eq.mp [Level.zero])
            (p.liftLooseBVars 0 1) (p'.liftLooseBVars 0 1)
            (he.liftLooseBVars 0 1) (.bvar 0)))
        .default)
    return some body
  return none

/-- Reduce `*.noConfusion` applications via whnf. -/
private def simplifyNoConfusion (e : Expr) : MetaM (Option Expr) := do
  let (fn, _) := peelArgs e
  let some cname := fn.constName? | return none
  if !cname.toString.endsWith ".noConfusion" then return none
  let reduced ← Meta.whnf e
  if reduced != e then return some reduced
  return none

/-- Reduce `Eq.ndrec`/`Eq.rec` applications where the eq proof computes to `Eq.refl`.
    This handles the common pattern from generalized equation motives in casesOn:
    `Eq.ndrec motive base (Eq.symm (Eq.refl a)) (Eq.refl a)` reduces to `base (Eq.refl a)`.
    We use whnf to perform the reduction. -/
private def simplifyEqRec (e : Expr) : MetaM (Option Expr) := do
  let (fn, _) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.ndrec && cname != ``Eq.rec && cname != ``Eq.mpr then return none
  let reduced ← Meta.whnf e
  if reduced != e then return some reduced
  return none

/-- Collapse `Eq.mp (Eq.refl _) body → body` (identity transport).
    This is common in grind proofs where normalization produces
    `Eq.mp (Eq.refl T) x` which is just `x`. -/
private def simplifyEqMpRefl (e : Expr) : Option Expr := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | failure
  guard (cname == ``Eq.mp)
  guard (args.length == 4)
  let eqProof := args[2]!
  let body := args[3]!
  let (eqFn, _) := peelArgs eqProof
  let some eqName := eqFn.constName? | failure
  guard (eqName == ``Eq.refl)
  return body

-- ═══════════════════════════════════════════════════════
-- Main traversal
-- ═══════════════════════════════════════════════════════

/-- Pre-step: cheap pure rewrites applied before recursing into children.
    Returns `.visit` to re-traverse after rewriting, `.continue` to recurse normally. -/
private def simplifyPre (e : Expr) : MetaM TransformStep := do
  -- Beta reduction (all beta redexes, not just fvar args)
  if e.isHeadBetaTarget then return .visit e.headBeta
  -- Strip `@id T body`
  if let some r := simplifyId e then return .visit r
  -- Collapse Eq.mp (Eq.refl _) body → body
  if let some r := simplifyEqMpRefl e then return .visit r
  return .continue

/-- Post-step: MetaM rewrites applied after children are simplified.
    Returns `.visit` to re-traverse after rewriting, `.done` to keep as-is. -/
private def simplifyPost (e : Expr) : MetaM TransformStep := do
  if let some r ← simplifyGrindWrappers e then return .visit r
  if let some r ← simplifyIntroWithEq e then return .visit r
  if let some r ← simplifyNoConfusion e then return .visit r
  if let some r ← simplifyEqRec e then return .visit r
  if let some r ← simplifyFalseElim e then return .visit r
  return .done e

/-- Recursively simplify a proof term bottom-up using `Meta.transform`.
    Uses `withLocalDecl` internally (not `lambdaTelescope`) so definitions
    like `intro_with_eq` are not unfolded during binder opening. -/
def simplifyProofTerm (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := simplifyPre) (post := simplifyPost)

end LeanDecomp
