import Lean
import Lean.Meta.Tactic.TryThis
import LeanDecomp.Helpers

namespace LeanDecomp.Specialized.Grind
open Lean Elab Meta Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

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

/-- Peel `Eq.mp <named-grind-cast> inner`: when the cast is a fully-applied
    `Lean.Grind.<castName>` const, emit `refine Eq.mp <cast> ?_` and recurse
    on `inner`. The cast term is small (just the const + its Prop args), so
    delabbing it inline avoids a recursive descent into a structural cast that
    the generic `tryDecompEqMp` would otherwise do. -/
private def tryDecompEqMpKnownGrindCast (castName : Name) (expr : Expr)
    (lctx : LocalContext) (localInsts : LocalInstances) (used : List String)
    (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  let (fn, args) := peelArgs expr
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp then return none
  if args.length < 4 then return none
  let castProof := args[2]!
  let inner := args[3]!
  let (castFn, _) := peelArgs castProof
  let some n := castFn.constName? | return none
  if n != castName then return none
  withLCtx lctx localInsts do
    let castStx ← delabToRefinableSyntax castProof
    let eqMpIdent : Ident := ⟨mkIdent ``Eq.mp |>.raw.setInfo .none⟩
    let headTac ← `(tactic| refine $eqMpIdent:ident $castStx ?_)
    let result ← LeanDecomp.emitTacticWithSubgoals headTac #[inner] lctx localInsts used decompileExpr
    return some result

/-- Walk a proof term for occurrences of `Finset.mem_<Shape>.mp <fvar>` (which
    desugars to `Iff.mp Finset.mem_<Shape> <fvar>`). For each such occurrence,
    return a `rw [Finset.mem_<Shape>] at <fvar>` tactic. `lia` does not unfold
    Finset memberships on its own, so this preprocessing exposes the
    underlying arithmetic conjunction.

    We walk the proof term (rather than the lctx) because `set r := Finset.Ico …`
    leaves an opaque fvar `r` in the lctx, but the proof itself uses
    `Finset.mem_Ico.mp h` against the destructured form, telling us exactly
    which `mem_*` lemma applies. -/
private partial def collectFinsetMemRewrites (proof : Expr) : MetaM (Array (TSyntax `tactic)) := do
  let memLemmas : List String := [
    "Finset.mem_Ico", "Finset.mem_Ioc", "Finset.mem_Icc", "Finset.mem_Ioo",
    "Finset.mem_Iic", "Finset.mem_Iio", "Finset.mem_Ici", "Finset.mem_Ioi",
    "Finset.mem_range", "Finset.mem_sdiff", "Finset.mem_inter", "Finset.mem_union"
  ]
  let mut found : Std.HashSet (Name × Name) := {}
  let mut stack : List Expr := [proof]
  let mut iters := 0
  while !stack.isEmpty && iters < 5000 do
    iters := iters + 1
    let cur := stack.head!
    stack := stack.tail!
    -- Look for `Iff.mp <memLemma> <fvar>` patterns.
    let (fn, args) := peelArgs cur
    if fn.isConstOf ``Iff.mp && args.length >= 4 then
      let iffArg := args[2]!
      let hypArg := args[3]!
      let (iffFn, _) := peelArgs iffArg
      if let some iffName := iffFn.constName? then
        if memLemmas.contains iffName.toString then
          if let some fid := hypArg.fvarId? then
            let hypDecl ← fid.getDecl
            found := found.insert (iffName, hypDecl.userName)
    match cur with
    | .app f a => stack := f :: a :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .forallE _ t b _ => stack := t :: b :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | .mdata _ b => stack := b :: stack
    | .proj _ _ b => stack := b :: stack
    | _ => pure ()
  let mut rwTacs : Array (TSyntax `tactic) := #[]
  for (lemmaName, hypName) in found do
    let lemmaIdent : Ident := mkIdent lemmaName
    let hypIdent : Ident := mkIdent hypName
    let rwRule ← `(Parser.Tactic.rwRule| $lemmaIdent:ident)
    let loc ← `(Lean.Parser.Tactic.location| at $hypIdent:term)
    rwTacs := rwTacs.push (← `(tactic| rw [$rwRule] $loc))
  return rwTacs

/-- Check whether a type is arithmetic-shaped (LE/LT/Eq of integer/natural
    expressions). Used to decide whether `lia` is a plausible terminal. -/
private def isArithLeafGoal (ty : Expr) : MetaM Bool := do
  let (fn, _) := peelArgs ty
  let some n := fn.constName? | return false
  return n == ``LE.le || n == ``LT.lt || n == ``GE.ge || n == ``GT.gt || n == ``Eq

/-- Try `lia` after introducing each extracted "interesting" sub-fact of the
    proof as a `have`. This handles leaves whose proof applies a forall hyp
    `hs : ∀ y ∈ S, P y` to a membership witness — `lia` cannot apply such
    hypotheses on its own, so we precompute the result via `have` before
    handing the goal to `lia`. -/
private def tryHavesPlusLia (expr exprTy : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (memRws : Array (TSyntax `tactic))
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  -- Only attempt this for moderately-sized proofs. Walking and delabbing all
  -- subterms of giant proofs is itself expensive; the handler is intended for
  -- arithmetic leaves where `lia` failed but a small set of forall-membership
  -- applications would close.
  if LeanDecomp.exprNodeCount expr > 1500 then return none
  let facts ← LeanDecomp.extractGrindFacts expr
  if facts.isEmpty then return none
  -- Only keep facts that:
  --   * are application proofs of an arithmetic statement (LE/LT/Eq), so
  --     adding them to lctx actually helps `lia`,
  --   * are small (so delab is fast and the resulting `have` body
  --     re-elaborates cheaply),
  --   * do not contain `eagerReduce` (which forces `with_unfolding_all`
  --     transparency at re-elaboration time and is the original cause of the
  --     timeout we are trying to avoid).
  let isArithType : Expr → Bool := fun ty =>
    match ty.getAppFn.constName? with
    | some n => n == ``LE.le || n == ``LT.lt || n == ``GE.ge || n == ``GT.gt || n == ``Eq
    | none => false
  let mut haveTacs : Array (TSyntax `tactic) := #[]
  let mut used := used
  let mut count := 0
  for fact in facts do
    if count >= 4 then break
    if LeanDecomp.exprNodeCount fact > 80 then continue
    if Lean.Expr.find? (fun sub => sub.getAppFn.isConstOf ``eagerReduce) fact |>.isSome then
      continue
    let factTy ← Meta.inferType fact
    unless isArithType factTy do continue
    let factStx ← try
      withOptions (fun o =>
        (o.setBool `pp.coercions.types true).setBool `pp.numericTypes true) <|
        Lean.Meta.Tactic.TryThis.delabToRefinableSyntax fact
    catch _ => continue
    let factTyStx ← try
      withOptions (fun o =>
        (o.setBool `pp.coercions.types true).setBool `pp.numericTypes true) <|
        Lean.Meta.Tactic.TryThis.delabToRefinableSyntax factTy
    catch _ => continue
    let hName := LeanDecomp.mkUniqueName "h_fact" used
    used := hName :: used
    let hIdent : Ident := mkIdent (Name.mkSimple hName)
    let haveTac ← `(tactic| have $hIdent:ident : $factTyStx := $factStx)
    haveTacs := haveTacs.push haveTac
    count := count + 1
  if haveTacs.isEmpty then return none
  let liaTac ← `(tactic| lia)
  let candidate := memRws ++ haveTacs ++ #[liaTac]
  if ← LeanDecomp.candidateTacticsCloseGoal candidate exprTy lctx localInsts then
    return some (candidate, used)
  return none

/-- `Eq.mp (Int.Linear.norm_le ...) <ev>` produces a user-form arithmetic
    inequality from grind's polynomial-normalization certificate. The cast
    proof itself carries `eagerReduce (Eq.refl true)` polynomial-equality
    witnesses, which the generic `tryDecompEqMp` would propagate as `pp.all`
    + `with_unfolding_all exact` blocks. Those re-elaborate slowly because
    the explicit polynomial coefficients have to be re-checked.

    Instead, try `lia` directly on the result type. If it does not close, walk
    the proof for `Iff.mp Finset.mem_*` references and emit
    `rw [Finset.mem_*] at <hyp>` before retrying — `lia` does not unfold
    Finset membership lemmas. -/
def tryDecompEqMpIntLinearNormLe (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (_decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  let (fn, args) := peelArgs expr
  let some cname := fn.constName? | return none
  if cname != ``Eq.mp then return none
  if args.length < 4 then return none
  let castProof := args[2]!
  let (castFn, _) := peelArgs castProof
  let some castName := castFn.constName? | return none
  if castName != ``Int.Linear.norm_le then return none
  withLCtx lctx localInsts do
    let exprTy ← Meta.inferType expr
    let liaTac ← `(tactic| lia)
    if ← LeanDecomp.candidateTacticsCloseGoal #[liaTac] exprTy lctx localInsts then
      return some (#[liaTac], used)
    let memRws ← collectFinsetMemRewrites expr
    if memRws.isEmpty then return none
    let candidate := memRws ++ #[liaTac]
    if ← LeanDecomp.candidateTacticsCloseGoal candidate exprTy lctx localInsts then
      return some (candidate, used)
    return none

/-- `Eq.mp (Lean.Grind.iff_eq p q) (h : p ↔ q) : p = q`. -/
def tryDecompEqMpIffEq (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) :=
  tryDecompEqMpKnownGrindCast ``Lean.Grind.iff_eq expr lctx localInsts used decompileExpr

/-- `Eq.mp (Lean.Grind.not_eq_prop p q) (h : ¬p = q) : p = ¬q`. -/
def tryDecompEqMpNotEqProp (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) :=
  tryDecompEqMpKnownGrindCast ``Lean.Grind.not_eq_prop expr lctx localInsts used decompileExpr

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

/-- Return the names of hypotheses whose type syntactically contains `abs x`.
    Skips compound hypotheses (And/Or-headed) because the surrounding decompiler
    typically destructures these via `cases`, removing them before any rewrite
    against them would run. -/
private def findHypsWithAbsOf (x : Expr) : MetaM (List Name) := do
  let lctx ← getLCtx
  let mut result : List Name := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let tyHead := ty.getAppFn.constName?
    if tyHead == some ``And || tyHead == some ``Or then
      continue
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

/-- When the goal is `False` and the local context contains a hypothesis whose
    type mentions `abs x` for some `x`, do a sign case split on `x`, rewrite
    the abs in every relevant hypothesis, and close with `lia`. This is broader
    than `tryDecompAbsLeaf`: it does not require `abs.eq_1` to appear in the
    proof term, which lets it discharge `Int.Linear.*` arithmetic certificates
    whose end result is False but which never explicitly unfold abs. -/
def tryDecompAbsCaseSplitContradiction (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (_decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let exprTy ← Meta.inferType expr
    unless exprTy.isConstOf ``False do return none
    let lctx' ← getLCtx
    let mut absX? : Option Expr := none
    for decl in lctx' do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      let tyHead := ty.getAppFn.constName?
      if tyHead == some ``And || tyHead == some ``Or then continue
      let found := Expr.find? (fun sub =>
        match sub.getAppFn.constName? with
        | some name => name == `abs && sub.getAppArgs.size >= 1
        | _ => false) ty
      if let some absExpr := found then
        let absArgs := absExpr.getAppArgs
        if absArgs.size >= 1 then
          absX? := some absArgs[absArgs.size - 1]!
          break
    let some x := absX? | return none
    let targets ← findHypsWithAbsOf x
    if targets.isEmpty then return none
    let xStx ← delabToRefinableSyntax x
    let xTy ← Meta.inferType x
    let xTyStx ← delabToRefinableSyntax xTy
    let hName := LeanDecomp.mkUniqueName "h_abs" used
    let hIdent : Ident := mkIdent (Name.mkSimple hName)
    let nonposLemma : Ident := mkIdent `abs_of_nonpos
    let posLemma : Ident := mkIdent `abs_of_pos
    let notLeMp : Ident := mkIdent (Name.mkStr2 "not_le" "mp")
    let liaTac ← `(tactic| lia)
    -- Build rewrites for each branch.
    let mut nonposRws : Array (TSyntax `tactic) := #[]
    let mut posRws : Array (TSyntax `tactic) := #[]
    for target in targets do
      let targetIdent : Ident := mkIdent target
      let loc ← `(Lean.Parser.Tactic.location| at $targetIdent:term)
      let nonposRule ← `(Parser.Tactic.rwRule| $nonposLemma:ident $hIdent:ident)
      let posInner ← `(($notLeMp:ident $hIdent:ident))
      let posRule ← `(Parser.Tactic.rwRule| $posLemma:ident $posInner)
      nonposRws := nonposRws.push (← `(tactic| rw [$nonposRule] $loc))
      posRws := posRws.push (← `(tactic| rw [$posRule] $loc))
    let nonposBlock ← `(tactic| · $[$nonposRws]* ; $liaTac)
    let posBlock ← `(tactic| · $[$posRws]* ; $liaTac)
    -- Type-annotate the predicate so Lean does not infer the wrong arithmetic
    -- type (e.g. picking ℕ when the abs argument is ℤ-typed in the proof).
    let byCasesTac ← `(tactic| by_cases $hIdent:ident : ($xStx : $xTyStx) ≤ 0)
    let cand : Array (TSyntax `tactic) := #[byCasesTac, nonposBlock, posBlock]
    if ← LeanDecomp.candidateTacticsCloseGoal cand exprTy lctx localInsts then
      return some (cand, hName :: used)
    return none

/-- When the goal is `x ∈ Finset.<Interval> a b` for an arithmetic interval
    constructor (Ico, Ioc, Icc, Ioo, range, …), bypass any structural transport
    that grind built between user-form and its polynomial form by emitting
    `rw [Finset.mem_<Interval>]; lia`. `lia` handles And-shaped arithmetic
    goals directly, so we don't need to `refine ⟨?_, ?_⟩ <;> lia` — fewer
    `lia` invocations during validation, and a tighter generated tactic.

    This is goal-shape-driven, not proof-term-driven: any proof that has a
    Finset interval membership at the top is a candidate. If `lia` cannot
    discharge the resulting arithmetic from the local hypotheses, the handler
    returns `none` and dispatch falls through. -/
def tryDecompFinsetIntervalMembership (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (_decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let exprTy ← Meta.inferType expr
    let (fn, args) := peelArgs exprTy
    if !fn.isConstOf ``Membership.mem || args.length < 5 then return none
    let setExprRaw := args[args.length - 1]!
    let setExpr ← match setExprRaw.fvarId? with
      | some fid =>
        let fdecl ← fid.getDecl
        match fdecl.value? with
        | some v => pure v
        | none => pure setExprRaw
      | none => pure setExprRaw
    let (setFn, _) := peelArgs setExpr
    -- Determine which Finset interval we're dealing with. Prefer the const
    -- name on the goal's RHS (if visible). When `set r := Finset.<X> …`
    -- introduced an opaque fvar, walk the proof term for an `Iff.mp/mpr
    -- Finset.mem_<X>` reference, which tells us the membership lemma.
    let goalConstName : Option String := setFn.constName?.map (·.toString)
    let probeProofForMemLemma : MetaM (Option String) := do
      let memNames : List String := [
        "Finset.mem_Ico", "Finset.mem_Ioc", "Finset.mem_Icc", "Finset.mem_Ioo",
        "Finset.mem_Iic", "Finset.mem_Iio", "Finset.mem_Ici", "Finset.mem_Ioi",
        "Finset.mem_range"
      ]
      let mut stack : List Expr := [expr]
      let mut iters := 0
      while !stack.isEmpty && iters < 5000 do
        iters := iters + 1
        let cur := stack.head!
        stack := stack.tail!
        let (cfn, cargs) := peelArgs cur
        if (cfn.isConstOf ``Iff.mp || cfn.isConstOf ``Iff.mpr) && cargs.length >= 3 then
          let iffArg := cargs[2]!
          let (iffFn, _) := peelArgs iffArg
          if let some n := iffFn.constName? then
            let s := n.toString
            if memNames.contains s then
              -- Convert "Finset.mem_<X>" → "Finset.<X>" to align with goalConstName check.
              let setShape := s.replace "mem_" ""
              return some setShape
        match cur with
        | .app f a => stack := f :: a :: stack
        | .lam _ t b _ => stack := t :: b :: stack
        | .forallE _ t b _ => stack := t :: b :: stack
        | .letE _ t v b _ => stack := t :: v :: b :: stack
        | .mdata _ b => stack := b :: stack
        | .proj _ _ b => stack := b :: stack
        | _ => pure ()
      return none
    let setShape ← match goalConstName with
      | some s => pure (some s)
      | none => probeProofForMemLemma
    let some setShape := setShape | return none
    -- Map Finset interval constructor to its `mem_*` lemma.
    let memLemma? : Option Name := match setShape with
      | "Finset.Ico" => some (Name.mkStr2 "Finset" "mem_Ico")
      | "Finset.Ioc" => some (Name.mkStr2 "Finset" "mem_Ioc")
      | "Finset.Icc" => some (Name.mkStr2 "Finset" "mem_Icc")
      | "Finset.Ioo" => some (Name.mkStr2 "Finset" "mem_Ioo")
      | "Finset.Iic" => some (Name.mkStr2 "Finset" "mem_Iic")
      | "Finset.Iio" => some (Name.mkStr2 "Finset" "mem_Iio")
      | "Finset.Ici" => some (Name.mkStr2 "Finset" "mem_Ici")
      | "Finset.Ioi" => some (Name.mkStr2 "Finset" "mem_Ioi")
      | "Finset.range" => some (Name.mkStr2 "Finset" "mem_range")
      | _ => none
    let some memLemma := memLemma? | return none
    let lemmaIdent : Ident := mkIdent memLemma
    let rwRule ← `(Parser.Tactic.rwRule| $lemmaIdent:ident)
    let rwTac ← `(tactic| rw [$rwRule])
    let liaTac ← `(tactic| lia)
    -- Also include any Finset interval memberships in the hypotheses.
    let memRws ← collectFinsetMemRewrites expr
    let cand := memRws.push rwTac |>.push liaTac
    if ← LeanDecomp.candidateTacticsCloseGoal cand exprTy lctx localInsts then
      return some (cand, used)
    return none

/-- When the goal is `False` and the proof carries grind automation (so the
    contradiction is via the arithmetic engine), preprocess Finset interval
    memberships in the lctx via `rw [Finset.mem_*] at <hyp>` and try `lia`.
    A single `lia` call after the rewrites avoids the per-leaf elaboration
    cost of decomposing the structural contradiction. -/
def tryDecompFalseFromLia (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (_decompileExpr : DecompileCallback)
  : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let exprTy ← Meta.inferType expr
    unless exprTy.isConstOf ``False do return none
    unless LeanDecomp.containsAutomationInternals expr do return none
    let liaTac ← `(tactic| lia)
    if ← LeanDecomp.candidateTacticsCloseGoal #[liaTac] exprTy lctx localInsts then
      return some (#[liaTac], used)
    let memRws ← collectFinsetMemRewrites expr
    if memRws.isEmpty then return none
    let candidate := memRws ++ #[liaTac]
    if ← LeanDecomp.candidateTacticsCloseGoal candidate exprTy lctx localInsts then
      return some (candidate, used)
    return none

def handlers : List (Expr → LocalContext → LocalInstances → List String → DecompileCallback →
    TacticM (Option (Array (TSyntax `tactic) × List String))) := [
  tryDecompFinsetIntervalMembership,
  tryDecompFalseFromLia,
  tryDecompEqMpIntLinearNormLe,
  tryDecompEqMpIffEq,
  tryDecompEqMpNotEqProp,
  tryDecompEqMpAutomationCast,
  tryDecompMt,
  tryDecompAbsLeaf,
  tryDecompAbsCaseSplitContradiction
]

end LeanDecomp.Specialized.Grind
