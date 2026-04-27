import Lean
import LeanDecomp.CasesOn
import LeanDecomp.Simplify.Grind

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

/-- Reduce lightweight equality/heterogeneous-equality transport wrappers produced by
    `convert` and generalized-equation elaboration. These are often definitionally
    reducible once their proof arguments have been simplified, and exposing the
    transported body lets the decompiler recover theorem structure instead of
    falling back to a giant exact term. -/
private def simplifyEqTransport (e : Expr) : MetaM (Option Expr) := do
  let (fn, _) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.casesOn && cname != ``eq_of_heq && cname != ``heq_of_eq then
    return none
  let reduced ← Meta.whnf e
  if reduced != e then return some reduced
  return none

/-- Simplify HEq transport proofs enough for `eq_of_heq` to collapse. This is a
    lightweight copy of the convert/generalized-equality reductions we need in the
    main proof-term simplifier, without pulling in the full equality decompiler. -/
private partial def simplifyHEqTransportProof (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  let (fn, args) := peelArgs e
  match fn.constName? with
  | some ``HEq.refl =>
      pure e
  | some ``heq_of_eq =>
      let some hEq := args.getLast? | pure e
      let hEq' ← simplifyHEqTransportProof hEq
      let (hEqFn, hEqArgs) := peelArgs hEq'
      match hEqFn.constName? with
      | some ``Eq.refl =>
          let some x := hEqArgs.getLast? | pure e
          mkHEqRefl x
      | _ =>
          if hEq' != hEq then
            mkAppM ``heq_of_eq #[hEq']
          else
            pure e
  | some ``Eq.ndrec | some ``Eq.rec | some ``Eq.casesOn =>
      let reduced ← Meta.whnf e
      if reduced != e then
        simplifyHEqTransportProof reduced
      else
        pure e
  | _ =>
      pure e

/-- Collapse `eq_of_heq` once its HEq witness has simplified to either `heq_of_eq`
    or `HEq.refl`. This removes convert-generated transport wrappers and exposes
    the underlying equality proof to the decompiler. -/
private def simplifyEqOfHEq (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  if fn.constName? != some ``eq_of_heq then
    return none
  let some hHeq := args.getLast? | return none
  let hHeq' ← simplifyHEqTransportProof hHeq
  let (hFn, hArgs) := peelArgs hHeq'
  match hFn.constName? with
  | some ``HEq.refl =>
      let some x := hArgs.getLast? | return none
      return some (← mkEqRefl x)
  | some ``heq_of_eq =>
      let some hEq := hArgs.getLast? | return none
      return some hEq
  | _ =>
      if hHeq' != hHeq then
        return some (mkAppN fn ((args.dropLast ++ [hHeq']).toArray))
      return none

/-- Collapse `Eq.mp (Eq.refl _) body → body` (identity transport).
    This is common in grind proofs where normalization produces
    `Eq.mp (Eq.refl T) x` which is just `x`. -/
private def simplifyEqMpRefl (e : Expr) : Option Expr := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | failure
  guard (cname == ``Eq.mp || cname == ``Eq.mpr)
  guard (args.length == 4)
  let eqProof := args[2]!
  let body := args[3]!
  let (eqFn, _) := peelArgs eqProof
  let some eqName := eqFn.constName? | failure
  guard (eqName == ``Eq.refl)
  return body

/-- Collapse `Eq.mp (Eq.trans (Eq.symm (eq_true h)) heq) True.intro` to
    `Eq.mp heq h`. Grind often packages a local hypothesis `h : P` as
    `True = P` via `Eq.symm (eq_true h)` and then transports `True.intro`
    through it before applying a second cast. Replacing the prefix with `h`
    exposes the direct hypothesis to the decompiler. -/
private def simplifyEqMpTrueIntroEqTrue (e : Expr) : MetaM (Option Expr) := do
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp || args.length != 4 then return none
  let witness := args[3]!
  let (witnessFn, _) := peelArgs witness
  if witnessFn.constName? != some ``True.intro then return none
  let eqProof := args[2]!
  let (eqFn, eqArgs) := peelArgs eqProof
  if eqFn.constName? != some ``Eq.trans || eqArgs.length < 6 then return none
  let eq1 := eqArgs[4]!
  let eq2 := eqArgs[5]!
  let (eq1Fn, eq1Args) := peelArgs eq1
  if eq1Fn.constName? != some ``Eq.symm || eq1Args.length < 4 then return none
  let inner := eq1Args[3]!
  let (innerFn, innerArgs) := peelArgs inner
  if innerFn.constName? != some ``eq_true || innerArgs.length < 2 then return none
  let h := innerArgs[1]!
  let p ← instantiateMVars (← Meta.inferType h)
  return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) p args[1]! eq2 h)

-- ═══════════════════════════════════════════════════════
-- Propositional cast simplification (congr-chain interpreter)
-- ═══════════════════════════════════════════════════════

/-- Handle `Eq.mp (congrArg f h) evidence` for known Prop connectives.
    f : Prop → Prop, h : a₁ = a₂, evidence : f a₁ → result : f a₂ -/
private def simplifyCongrArgTransport (a₁ a₂ f h evidence : Expr)
    : MetaM (Option Expr) := do
  let mkIffCongrRight (lhs rhs : Expr) : MetaM Expr := do
    let fwd := Expr.lam `h lhs
      (mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h
        (mkApp4 (mkConst ``Iff.mp) lhs a₁ evidence (.bvar 0))) .default
    let bwd := Expr.lam `h rhs
      (mkApp4 (mkConst ``Iff.mpr) lhs a₁ evidence
        (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a₁ a₂ h (.bvar 0))) .default
    pure (mkApp4 (mkConst ``Iff.intro) lhs rhs fwd bwd)
  let mkIffCongrLeft (lhs rhs : Expr) : MetaM Expr := do
    let fwd := Expr.lam `h lhs
      (mkApp4 (mkConst ``Iff.mp) a₁ rhs evidence
        (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a₁ a₂ h (.bvar 0))) .default
    let bwd := Expr.lam `h rhs
      (mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h
        (mkApp4 (mkConst ``Iff.mpr) a₁ rhs evidence (.bvar 0))) .default
    pure (mkApp4 (mkConst ``Iff.intro) lhs rhs fwd bwd)
  -- f is a lambda: fun x => body
  if let .lam _ _ body _ := f then
    if !body.hasLooseBVars then return some evidence  -- constant function
    if body == .bvar 0 then  -- identity
      return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h evidence)
    -- fun x => (P ↔ x) represented as proposition equality P = x
    let (bodyFn, bodyArgs) := peelArgs body
    if bodyFn.isConstOf ``Iff && bodyArgs.length == 2
        && bodyArgs[1]! == .bvar 0 && !bodyArgs[0]!.hasLooseBVars then
      let lhs := bodyArgs[0]!
      return some (← mkIffCongrRight lhs a₂)
    -- fun x => (x ↔ P) represented as proposition equality x = P
    if bodyFn.isConstOf ``Iff && bodyArgs.length == 2
        && bodyArgs[0]! == .bvar 0 && !bodyArgs[1]!.hasLooseBVars then
      let rhs := bodyArgs[1]!
      return some (← mkIffCongrLeft a₂ rhs)
    let (bodyFn, bodyArgs) := peelArgs body
    -- fun x => x ∧ Q  (And on left)
    if bodyFn.isConstOf ``And && bodyArgs.length == 2
        && bodyArgs[0]! == .bvar 0 && !bodyArgs[1]!.hasLooseBVars then
      let Q := bodyArgs[1]!
      let left := mkApp3 (mkConst ``And.left) a₁ Q evidence
      let right := mkApp3 (mkConst ``And.right) a₁ Q evidence
      let newLeft := mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h left
      return some (mkApp4 (mkConst ``And.intro) a₂ Q newLeft right)
    -- fun x => P ∧ x  (And on right)
    if bodyFn.isConstOf ``And && bodyArgs.length == 2
        && bodyArgs[1]! == .bvar 0 && !bodyArgs[0]!.hasLooseBVars then
      let P := bodyArgs[0]!
      let left := mkApp3 (mkConst ``And.left) P a₁ evidence
      let right := mkApp3 (mkConst ``And.right) P a₁ evidence
      let newRight := mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h right
      return some (mkApp4 (mkConst ``And.intro) P a₂ left newRight)
    -- fun x => ¬x  (Not)
    if bodyFn.isConstOf ``Not && bodyArgs.length == 1
        && bodyArgs[0]! == .bvar 0 then
      let mprFn := mkApp3 (mkConst ``Eq.mpr [Level.zero]) a₁ a₂ h
      return some (mkApp4 (mkConst ``mt) a₂ a₁ mprFn evidence)
    return none
  -- f = Not (not a lambda, bare constant)
  if f.isConstOf ``Not then
    let mprFn := mkApp3 (mkConst ``Eq.mpr [Level.zero]) a₁ a₂ h
    return some (mkApp4 (mkConst ``mt) a₂ a₁ mprFn evidence)
  -- f = And P (partially applied)
  let fHead := f.getAppFn
  let fArgs := f.getAppArgs
  -- Iff P (partially applied): transport equality evidence via transitivity.
  if fHead.isConstOf ``Iff && fArgs.size == 1 then
    let lhs := fArgs[0]!
    return some (← mkIffCongrRight lhs a₂)
  if fHead.isConstOf ``And && fArgs.size == 1 then
    let P := fArgs[0]!
    let left := mkApp3 (mkConst ``And.left) P a₁ evidence
    let right := mkApp3 (mkConst ``And.right) P a₁ evidence
    let newRight := mkApp4 (mkConst ``Eq.mp [Level.zero]) a₁ a₂ h right
    return some (mkApp4 (mkConst ``And.intro) P a₂ left newRight)
  return none

/-- Simplify propositional casts: `Eq.mp`/`Eq.mpr` with propext, Eq.trans, congr chains.
    Converts grind's equality-based propositional transport into Iff-based operations.
    Inspired by lean-calcify's approach of flattening congruence chains. -/
private def simplifyPropCast (e : Expr) : MetaM (Option Expr) := do
  if let some r ← simplifyGrindPropCast e then
    return some r
  let (fn, args) := peelArgs e
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp && cname != ``Eq.mpr then return none
  if args.length != 4 then return none
  unless fn.isConst do return none
  let levels := fn.constLevels!
  let isForward := (cname == ``Eq.mp)
  let eqProof := args[2]!
  let evidence := args[3]!
  let (eqFn, eqArgs) := peelArgs eqProof
  let some eqName := eqFn.constName? | return none
  -- All remaining cases require Prop-level transport (u = 0)
  match levels with
  | [Level.zero] => pure ()
  | _ => return none
  match eqName with
  | ``propext =>
    if eqArgs.length < 3 then return none
    let iff := eqArgs[2]!
    if isForward
    then return some (mkApp4 (mkConst ``Iff.mp) eqArgs[0]! eqArgs[1]! iff evidence)
    else return some (mkApp4 (mkConst ``Iff.mpr) eqArgs[0]! eqArgs[1]! iff evidence)
  | ``Eq.trans =>
    if eqArgs.length < 6 then return none
    -- args of @Eq.trans.{u} {α} {a b c} h₁ h₂: [α, a, b, c, h₁, h₂]
    let a := eqArgs[1]!; let b := eqArgs[2]!; let c := eqArgs[3]!
    let eq1 := eqArgs[4]!; let eq2 := eqArgs[5]!
    if isForward then
      let inner := mkApp4 (mkConst ``Eq.mp [Level.zero]) a b eq1 evidence
      return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) b c eq2 inner)
    else
      let inner := mkApp4 (mkConst ``Eq.mpr [Level.zero]) b c eq2 evidence
      return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a b eq1 inner)
  | ``Eq.symm =>
    if eqArgs.length < 4 then return none
    -- @Eq.symm.{u} {α} {a b} h: [α, a, b, h]
    let a := eqArgs[1]!; let b := eqArgs[2]!; let h := eqArgs[3]!
    if isForward
    then return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) a b h evidence)
    else return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) a b h evidence)
  | ``eq_true =>
    if eqArgs.length < 2 then return none
    if isForward then return some (mkConst ``True.intro)
    else return some eqArgs[1]!
  | ``eq_false | ``eq_false' =>
    if eqArgs.length < 2 then return none
    if isForward then return some (mkApp eqArgs[1]! evidence)
    else return some (mkApp2 (mkConst ``False.elim [Level.zero]) args[0]! evidence)
  | ``congr =>
    -- @congr.{u,v} {α β} {f₁ f₂} {a₁ a₂} h₁ h₂: [α, β, f₁, f₂, a₁, a₂, h₁, h₂]
    if eqArgs.length < 8 then return none
    if !isForward then return none
    let f₂ := eqArgs[3]!; let a₁ := eqArgs[4]!
    let h₁ := eqArgs[6]!; let h₂ := eqArgs[7]!
    -- Decompose: Eq.mp (congr h₁ h₂) e
    --   → Eq.mp (congrArg f₂ h₂) (Eq.mp (congrFun' h₁ a₁) e)
    let levels := eqFn.constLevels!
    -- @congrFun'.{u,v} {α β f g} h a — same universe params as congr
    let step1 := mkAppN (mkConst ``congrFun' levels)
      #[eqArgs[0]!, eqArgs[1]!, eqArgs[2]!, eqArgs[3]!, h₁, a₁]
    -- @congrArg.{u,v} {α β a₁ a₂} f h
    let step2 := mkAppN (mkConst ``congrArg levels)
      #[eqArgs[0]!, eqArgs[1]!, eqArgs[4]!, eqArgs[5]!, f₂, h₂]
    let midType := mkApp f₂ a₁
    let inner := mkApp4 (mkConst ``Eq.mp [Level.zero]) args[0]! midType step1 evidence
    return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) midType args[1]! step2 inner)
  | ``congrArg =>
    -- @congrArg.{u,v} {α β} {a₁ a₂} f h: [α, β, a₁, a₂, f, h]
    if eqArgs.length < 6 then return none
    if !isForward then return none
    simplifyCongrArgTransport eqArgs[2]! eqArgs[3]! eqArgs[4]! eqArgs[5]! evidence
  | ``congrFun' | ``congrFun =>
    -- @congrFun'.{u,v} {α β} {f g} h a: [α, β, f, g, h, a]
    if eqArgs.length < 6 then return none
    if !isForward then return none
    let h := eqArgs[4]!; let a := eqArgs[5]!
    -- If h = congrArg bigF innerEq, convert congrFun'(congrArg bigF innerEq, a)
    --   to congrArg (fun x => bigF x a) innerEq
    let (hFn, hArgs) := peelArgs h
    if hFn.constName? == some ``congrArg && hArgs.length >= 6 then
      let innerA₁ := hArgs[2]!; let innerA₂ := hArgs[3]!
      let bigF := hArgs[4]!; let innerEq := hArgs[5]!
      -- Handle And specifically: congrFun' (congrArg And innerEq) a → congrArg (fun x => x ∧ a) innerEq
      if bigF.isConstOf ``And then
        let prop := mkSort Level.zero  -- Prop
        let newF := Expr.lam `x prop
          (mkApp2 (mkConst ``And) (.bvar 0) (a.liftLooseBVars 0 1)) .default
        -- @congrArg.{1,1} Prop Prop a₁ a₂ newF innerEq (Prop : Sort 1)
        let one := Level.succ Level.zero
        let newEqProof := mkAppN (mkConst ``congrArg [one, one])
          #[prop, prop, innerA₁, innerA₂, newF, innerEq]
        let srcType := mkApp2 (mkConst ``And) innerA₁ a
        let dstType := mkApp2 (mkConst ``And) innerA₂ a
        return some (mkApp4 (mkConst ``Eq.mp [Level.zero]) srcType dstType newEqProof evidence)
    return none
  | _ => return none

-- ═══════════════════════════════════════════════════════
-- Main traversal
-- ═══════════════════════════════════════════════════════

/-- Reduce projection-of-constructor patterns:
    - `And.left/right (And.intro _ _ pa pb) → pa/pb`
    - `Iff.mp (Iff.intro f g) ev → f ev`
    - `Iff.mpr (Iff.intro f g) ev → g ev`
    The kernel does this reduction on demand, but the simplifier needs it
    explicit so downstream handlers see the projected component (e.g. an
    `Eq.mp` hidden under `(And.intro ... ).left`, or grind's iff transport
    written as `Iff.mp (Iff.intro f g) ev` rather than just `f ev`). -/
private def simplifyProjOfIntro (e : Expr) : Option Expr :=
  let (fn, args) := peelArgs e
  match fn.constName? with
  | some name =>
    -- And.left/right: args = [a, b, h, extra...], pick from inner And.intro
    if (name == ``And.left || name == ``And.right) && args.length >= 3 then
      let andProof := args[2]!
      let extra := args.drop 3
      let (innerFn, innerArgs) := peelArgs andProof
      if innerFn.isConstOf ``And.intro && innerArgs.length >= 4 then
        let component := if name == ``And.left then innerArgs[2]! else innerArgs[3]!
        some (extra.foldl (init := component) fun acc a => mkApp acc a)
      else none
    -- Iff.mp/mpr: args = [a, b, iff, ev, extra...], beta-apply the iff branch
    else if (name == ``Iff.mp || name == ``Iff.mpr) && args.length >= 4 then
      let iffProof := args[2]!
      let ev := args[3]!
      let extra := args.drop 4
      let (innerFn, innerArgs) := peelArgs iffProof
      if innerFn.isConstOf ``Iff.intro && innerArgs.length >= 4 then
        let branch := if name == ``Iff.mp then innerArgs[2]! else innerArgs[3]!
        let result := mkApp branch ev
        some (extra.foldl (init := result) fun acc a => mkApp acc a)
      else none
    else none
  | none => none

/-- Pre-step: cheap pure rewrites applied before recursing into children.
    Returns `.visit` to re-traverse after rewriting, `.continue` to recurse normally. -/
private def simplifyPre (e : Expr) : MetaM TransformStep := do
  -- Beta reduction (all beta redexes, not just fvar args)
  if e.isHeadBetaTarget then return .visit e.headBeta
  -- Strip `@id T body`
  if let some r := simplifyId e then return .visit r
  -- Collapse Eq.mp/Eq.mpr (Eq.refl _) body → body
  if let some r := simplifyEqMpRefl e then return .visit r
  -- Reduce And.left/And.right of explicit And.intro and Iff.mp/mpr of Iff.intro
  if let some r := simplifyProjOfIntro e then return .visit r
  -- Simplify propositional casts (propext/congr chains → Iff operations)
  if let some r ← simplifyPropCast e then return .visit r
  return .continue

/-- Post-step: MetaM rewrites applied after children are simplified.
    Returns `.visit` to re-traverse after rewriting, `.done` to keep as-is. -/
private def simplifyPost (e : Expr) : MetaM TransformStep := do
  if let some r ← simplifyEqMpTrueIntroEqTrue e then return .visit r
  -- Convert grind theorem-based combinators to standard eq_true/eq_false/propext forms.
  if let some r ← simplifyGrindCombinators e then return .visit r
  -- Re-check propositional casts: child simplification may have revealed
  -- handleable eq proof heads (e.g. iff_eq → propext in children).
  if let some r ← simplifyPropCast e then return .visit r
  if let some r ← simplifyGrindWrappers e then return .visit r
  if let some r ← simplifyGrindIntroWithEq e then return .visit r
  if let some r ← simplifyNoConfusion e then return .visit r
  if let some r ← simplifyEqRec e then return .visit r
  if let some r ← simplifyEqTransport e then return .visit r
  if let some r ← simplifyEqOfHEq e then return .visit r
  if let some r ← simplifyFalseElim e then return .visit r
  return .done e

/-- Recursively simplify a proof term bottom-up using `Meta.transform`.
    Uses `withLocalDecl` internally (not `lambdaTelescope`) so definitions
    like `intro_with_eq` are not unfolded during binder opening. -/
def simplifyProofTerm (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := simplifyPre) (post := simplifyPost)

end LeanDecomp
