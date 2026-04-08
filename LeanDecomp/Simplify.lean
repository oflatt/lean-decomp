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

/-- Beta-reduce `(fun x => body) arg` only when arg is an fvar (size-preserving).
    Complex arguments are left for the decompiler to handle with `let` bindings. -/
private def simplifyBetaRedexFVar (e : Expr) : Option Expr := do
  let .app fn arg := e | failure
  let .lam _name _type body _bi := fn | failure
  guard arg.isFVar
  return body.instantiate1 arg

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

-- ═══════════════════════════════════════════════════════
-- Main traversal
-- ═══════════════════════════════════════════════════════

/-- Apply all simplification rules to a single node. -/
private def simplifyNode (e : Expr) : MetaM (Option Expr) := do
  -- Pure rules first (cheap)
  if let some r := simplifyId e then return some r
  if let some r := simplifyBetaRedexFVar e then return some r
  -- MetaM rules
  if let some r ← simplifyIntroWithEq e then return some r
  if let some r ← simplifyNoConfusion e then return some r
  if let some r ← simplifyFalseElim e then return some r
  return none

/-- Recursively simplify a proof term bottom-up, using `lambdaTelescope` so that
    bound variables become fvars with proper types in the MetaM context. -/
partial def simplifyProofTerm (e : Expr) : MetaM Expr := do
  -- For lambdas, open ONE binder at a time WITHOUT whnf (preserving intro_with_eq etc.)
  if let .lam n t body bi := e then
    let t' ← simplifyProofTerm t
    withLocalDecl n bi t' fun fvar => do
      let body' := body.instantiate1 fvar
      let simplified ← simplifyProofTerm body'
      return .lam n t' (simplified.abstract #[fvar]) bi
  else
    -- Recurse into subexpressions
    let e' ← match e with
      | .app f a => do
        pure (.app (← simplifyProofTerm f) (← simplifyProofTerm a))
      | .forallE n t b bi => do
        pure (.forallE n (← simplifyProofTerm t) (← simplifyProofTerm b) bi)
      | .letE n t v b nd => do
        pure (.letE n (← simplifyProofTerm t) (← simplifyProofTerm v) (← simplifyProofTerm b) nd)
      | .mdata m b => do
        pure (.mdata m (← simplifyProofTerm b))
      | .proj t i s => do
        pure (.proj t i (← simplifyProofTerm s))
      | _ => pure e
    -- Apply simplification rules to the node, then re-simplify if it changed
    match ← simplifyNode e' with
    | some simplified => simplifyProofTerm simplified
    | none => pure e'

end LeanDecomp
