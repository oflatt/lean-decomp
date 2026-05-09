import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

/-- Trace class for the decompiler's handler dispatch.  Enable with
    `set_option trace.leanDecomp true` to see which handler fired at each
    recursion point in the InfoView.  Hugely useful when investigating
    "why didn't handler X fire?" or "which handler emitted this tactic?".

    Use `traceFire` at the top of each `tryDecompXxx` body to log a
    handler-name + whether it returned some/none, plus a one-line summary
    of the matched expression head.  See examples in
    `Decompiler.lean` / `EqDecomp.lean`. -/
initialize Lean.registerTraceClass `leanDecomp

/-- Log a single handler-fire trace event.  Cheap when trace is off
    (Lean's `trace[]` machinery short-circuits on the trace-class flag). -/
def traceFire (handler : String) (expr : Expr) (result : Bool) : MetaM Unit := do
  trace[leanDecomp] "{handler}: {if result then "✓" else "✗"}  head={expr.getAppFn} arity={expr.getAppNumArgs}"

/-- The decompiler's monad: `TacticM` plus a state-ref of names introduced so
    far (so subsequent `intro` / `have` / `let` choose fresh non-shadowing
    names).  Replaces the old "thread `used : List String` through every
    handler signature, return `(tactics, used')` tuples" pattern.

    Handlers are `... → DecompM (Option (Array (TSyntax `tactic)))`; the
    macro entry point unwraps the state at the top with `(decompileExpr …).run' []`. -/
abbrev DecompM := StateRefT (List String) TacticM

/-- Type alias for the decompileExpr callback to avoid repetition -/
abbrev DecompileCallback := Expr → LocalContext → LocalInstances →
  DecompM (Array (TSyntax `tactic))

/-- Type alias for the assignIntroNames callback -/
abbrev AssignIntroNamesCallback := Array Expr →
  DecompM (List String × LocalContext)

/-- Read the current used-name list. -/
def getUsed : DecompM (List String) := get

/-- Push a name onto the used-name list (no-op if already present). -/
def addUsed (name : String) : DecompM Unit :=
  modify fun used => if used.contains name then used else name :: used

/-- Build a tactic sequence from an array of tactics. -/
def mkTacticSeq (tacs : Array (TSyntax `tactic)) : CoreM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  `(Lean.Parser.Tactic.tacticSeq| $[$tacs]*)

/-- Build a focused tactic block for one recursively decompiled subgoal. -/
def mkFocusedBlock (tacs : Array (TSyntax `tactic)) : CoreM (TSyntax `tactic) := do
  let seq ← mkTacticSeq tacs
  `(tactic| · $seq:tacticSeq)

/-- Replace parser-generated `?m.N` placeholders with anonymous holes. -/
def anonymizeSyntheticMVars (s : String) : String := Id.run do
  let chars := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < chars.size do
    if chars[i]! == '?' && i + 2 < chars.size && chars[i + 1]! == 'm' && chars[i + 2]! == '.' then
      let mut j := i + 3
      let mut sawDigit := false
      while j < chars.size && chars[j]!.isDigit do
        sawDigit := true
        j := j + 1
      if sawDigit then
        out := out ++ "?_"
        i := j
      else
        out := out.push chars[i]!
        i := i + 1
    else
      out := out.push chars[i]!
      i := i + 1
  out

def ppExprToTermSyntax (e : Expr) : MetaM Term := do
  let env ← getEnv
  let fmt ← Meta.ppExpr e
  let termStr := anonymizeSyntheticMVars fmt.pretty
  match Parser.runParserCategory env `term termStr with
  | .ok stx => pure ⟨stx⟩
  | .error err =>
    throwError "failed to parse pretty-printed term:\n{err}\n\n{termStr}"

def ppExprToTermSyntaxWith (e : Expr) (usePpAll : Bool) : MetaM Term :=
  withOptions (fun o =>
      let o := pp.coercions.types.set o true
      let o := pp.numericTypes.set o true
      -- `pp.maxSteps` defaults to 5000 — large proof terms overflow this
      -- and get tail-truncated as `⋯` even with `pp.all := true` (which
      -- doesn't override maxSteps).  L599 hit this exactly: the binder
      -- type was elided as `(h_2 : ⋯)` because the counter ran out
      -- before the printer reached the binder annotation.
      let o := pp.maxSteps.set o 1000000
      if usePpAll then
        pp.all.set o true
      else
        o
    ) do
      ppExprToTermSyntax e

/-- Three PrettyPrinter options control terminal-source truncation; we
    lift all three for any rendering of generated source so emitted
    suggestions survive re-elaboration.  Lean's defaults are tuned for
    interactive goal display, not source emission — for our use, `⋯` is
    fatal because the parser rejects it.

    - `pp.deepTerms := true` (default false, threshold 50): general
      depth-based subterm elision.
    - `pp.proofs := true` (default false, threshold 0): elides Prop-typed
      sub-terms regardless of depth, including binder type annotations.
    - `pp.maxSteps := 1000000` (default 5000): the printer maintains a
      visited-expression counter; everything visited after the budget is
      `⋯`.  L599's `(h_2 : ⋯)` came from this path — proof was big, the
      counter overflowed before reaching the binder, so the binder type
      annotation got `⋯` even though it was relatively shallow.

    Concrete failure this addresses: `Mathlib/Algebra/Order/BigOperators/
    Group/Finset.lean:599`'s `exact @Classical.byContradiction (Eq.{1}
    Nat ...) (fun (h_2 : ⋯) => ...)`. -/
def liftPPTruncationOptions (o : Lean.Options) : Lean.Options :=
  let o := pp.deepTerms.set o true
  let o := pp.proofs.set o true
  pp.maxSteps.set o 1000000

/-- `delabToRefinableSyntax` wrapper that disables PrettyPrinter
    truncation (all three paths — see `liftPPTruncationOptions`).  Use
    this everywhere we delab a proof term destined for emitted source.
    `pp.all := true` (via `ppExprToTermSyntaxWith _ true`) already implies
    `deepTerms`/`proofs`, but NOT `maxSteps`, so the alternate pp.all
    path also benefits from the maxSteps lift in `ppTacticFull`. -/
def delabRefinable (e : Expr) : MetaM Term :=
  withOptions liftPPTruncationOptions (delabToRefinableSyntax e)

/-- `PrettyPrinter.ppTactic` wrapper that lifts the same truncation options
    as `delabRefinable`.  Even when the Syntax tree has no `⋯` (because we
    delabbed with the lifts), the FORMATTING step in `ppTactic` re-applies
    the truncation logic when rendering large sub-terms inside the tactic
    syntax (notably arg lists and binder type annotations in `exact <giant>`
    fallbacks).  Use this everywhere we format a generated tactic seq for
    emission as a suggestion or for re-elaboration validation.

    Concrete failure this addresses: `BigOperators/Group/Finset.lean:599`'s
    `exact @Classical.byContradiction (Eq.{1} Nat ...) (fun (h_2 : ⋯) => ...)`
    where `(h_2 : ⋯)` was being injected by ppTactic, not by delab. -/
def ppTacticFull (stx : TSyntax `Lean.Parser.Tactic.tacticSeq) : CoreM Format :=
  withOptions liftPPTruncationOptions (PrettyPrinter.ppTactic ⟨stx⟩)

/-- True iff `n` is the Name of an inaccessible binder — one Lean's pretty
    printer renders with the `✝` marker.  Two stored representations both
    qualify:
    1. **Macro scopes attached** (the common case): a hygienic name like
       `Lean.Name.num "inst" 12345` from `Macro.addMacroScope`.
       `Name.hasMacroScopes` detects these.
    2. **Literal `✝` in a component string**: rare, but happens when a name
       was constructed via the printer's renaming pass and re-fed into the
       elaborator.  Caught by the component-string check.

    `inst✝`, `inst✝¹`, …, `h✝`, `a✝²` all qualify; ordinary `foo`, `inst_1`
    don't. -/
def isInaccessibleName (n : Name) : Bool :=
  n.hasMacroScopes ||
    n.components.any fun comp => comp.toString.contains '✝'

/-- Walk `stx` and replace identifier references that resolve to
    inaccessibly-named typeclass-instance fvars in `lctx` with `_` holes.
    Cross-file re-elaboration of decompiled scripts fails on `refine @foo
    R inst✝ ...` and `exact inst✝¹` — the `✝` marks the ident as
    inaccessible (Lean's hygiene scheme).  Typeclass inference can re-fill
    these positions, so `_` works.

    Three-condition narrow trigger so we don't over-fire on hygienic but
    accessible binders (which would substitute `_` for a real reference
    and fail validation):
    1. ident has macro scopes OR a literal `✝` component;
    2. the name resolves to an FVar in `lctx`;
    3. that FVar's type is a typeclass instance (`Meta.isClass?`).

    Returns the input unchanged when no qualifying idents are present.

    Substitutes `inferInstance` (not bare `_`) because `_` in tactic
    `exact` position becomes an unfilled term mvar (raises "internal
    exception #5" under `exact _`).  `inferInstance` works in BOTH term
    position (`refine @foo R inferInstance …`) and tactic position
    (`exact inferInstance`) by explicitly invoking typeclass synthesis. -/
def sanitizeInaccessibleIdents (lctx : LocalContext) (stx : Syntax) : MetaM Syntax := do
  -- Build via `mkIdent` rather than `\`(inferInstance)` quotation: the
  -- quotation form attaches a fresh macro scope which PrettyPrinter would
  -- then sanitize back to `inferInstance✝` — defeating the purpose.
  let inferInst : Syntax := mkIdent ``inferInstance
  let isInaccessibleClassRef (name : Name) : MetaM Bool := do
    if !name.hasMacroScopes && !name.isInaccessibleUserName then return false
    let some decl := lctx.findFromUserName? name | return false
    return (← Meta.isClass? decl.type).isSome
  -- Walk down chained projections (`inst✝.foo.bar`) to find the receiver
  -- ident at the bottom.  Returns the bottom ident's name iff the chain
  -- is purely `.proj` nodes terminating in an ident.
  let rec projRoot : Syntax → Option Name
    | .node _ ``Lean.Parser.Term.proj #[receiver, _, _] => projRoot receiver
    | .ident _ _ name _ => some name
    | _ => none
  Meta.withLCtx lctx #[] do
    stx.replaceM fun s => do
      match s with
      -- Whole-projection replacement: `inst✝.toLE` → `inferInstance`.
      -- Without this, the inner ident swap would produce `inferInstance.toLE`,
      -- which fails with "type class instance expected ?m" because Lean
      -- can't infer the type to synthesize for the bare `inferInstance`
      -- before descending into `.toLE`.  Replacing the whole projection
      -- works because the projection's RESULT type is also a class
      -- (e.g. `(inst : LinearOrder M).toLE : LE M`).
      | .node _ ``Lean.Parser.Term.proj _ =>
        match projRoot s with
        | some name =>
          if (← isInaccessibleClassRef name) then pure (some inferInst)
          else pure none
        | none => pure none
      | .ident _ _ name _ =>
        if (← isInaccessibleClassRef name) then pure (some inferInst)
        else pure none
      | _ => pure none

/-- Peel off all applications from an expression to get the head and arguments.
    Returns (head, args) where args is in left-to-right order. -/
def peelArgs (e : Expr) : Expr × List Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × List Expr :=
    match e with
    | Expr.app f arg => go f (arg :: acc)
    | _ => (e, acc)
  go e []

/-- Match an expression `e` against the shape `<constName> a₁ a₂ … aₙ` with
    `n ≥ minArity`.  Returns the argument list on match, `none` otherwise.
    Replaces the boilerplate `let (fn, args) := peelArgs e; let some name :=
    fn.constName? | return none; if name != ``Foo then return none; if
    args.length < N then return none` that every `tryDecompXxx` handler
    repeats.  Use as `let some args := matchConstApp? e ``Foo N | return none`. -/
def matchConstApp? (e : Expr) (constName : Name) (minArity : Nat) : Option (List Expr) :=
  let (fn, args) := peelArgs e
  if fn.isConstOf constName && args.length >= minArity then
    some args
  else
    none

partial def containsConstName (e : Expr) (target : Name) : Bool :=
  Expr.find? (fun sub => sub.getAppFn.constName? == some target) e |>.isSome

partial def containsEagerReduce (e : Expr) : Bool :=
  Expr.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some n => n == ``eagerReduce
    | none => false) e |>.isSome

partial def exprNodeCount (e : Expr) : Nat :=
  match e with
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => 1
  | .app f a => exprNodeCount f + exprNodeCount a + 1
  | .lam _ ty body _ => exprNodeCount ty + exprNodeCount body + 1
  | .forallE _ ty body _ => exprNodeCount ty + exprNodeCount body + 1
  | .letE _ ty val body _ => exprNodeCount ty + exprNodeCount val + exprNodeCount body + 1
  | .mdata _ body => exprNodeCount body + 1
  | .proj _ _ body => exprNodeCount body + 1

private def throwIfFallbackProofTooLarge (proof : Expr) : MetaM Unit := do
  let maxNodes := 500000
  let nodeCount := exprNodeCount proof
  if nodeCount > maxNodes then
    throwError
      "exact fallback proof too large ({nodeCount} nodes, max {maxNodes}); refusing to emit a giant exact term"

/-! **Decompiler invariant**: when any decomp action runs, the main TacticM goal
    must equal the type of the proof term being decompiled, with a lctx that
    reflects what the real run of the surrounding tactics would produce.
    `runInGoal` and `runInSubgoal` are the building blocks that uphold this. -/

/-- Allocate a fresh synthetic-opaque mvar of `goalType` in (lctx, localInsts),
    set it as the only main goal, run `k`, then restore the original goals.
    Use this when entering a recursive decomp call from a synthetic context
    (lambda telescope, let-binder, byContradiction binder, etc.). -/
def runInGoal (lctx : LocalContext) (localInsts : LocalInstances) (goalType : Expr)
    (k : TacticM α) : TacticM α := do
  let savedGoals ← getGoals
  try
    withLCtx lctx localInsts do
      let mvar ← Meta.mkFreshExprMVar (some goalType) .syntheticOpaque
      setGoals [mvar.mvarId!]
      k
  finally
    setGoals savedGoals

/-- Focus an existing mvarId as the sole main goal, run `k` in its local
    context, then restore the original goals.  Use this when the goal already
    exists (e.g. a subgoal returned by `MVarId.cases`). -/
def runInSubgoal (mvarId : MVarId) (k : TacticM α) : TacticM α := do
  let savedGoals ← getGoals
  try
    setGoals [mvarId]
    mvarId.withContext k
  finally
    setGoals savedGoals

/-- Run a speculative elaboration step that should not affect the surrounding
    proof state or message log:

    - **State**: wraps `act` in `withoutModifyingState` so any tactic execution
      it performs is rolled back regardless of outcome.
    - **Messages**: saves and restores the message log around `act`, so error
      messages emitted while testing a candidate don't leak to the user.
    - **Errors**: catches any exception from `act` and returns `default`, since
      the caller is using a `Bool`/`Option` answer to decide what to do next.

    All five "does this candidate work?" checkers in the decompiler share this
    boilerplate (`subproofTacticsCloseGoal`, `refineTacProducesGoals`,
    `refineTacMatchesProofArgs`, plus the `decide` and `lia` speculative
    attempts in handlers).  Routing them through one helper keeps the
    state/message-log/error invariants in one place. -/
def silentTry (default : α) (act : TacticM α) : TacticM α := do
  let savedMsgs ← Core.getMessageLog
  Core.setMessageLog {}
  let result ← try
    withoutModifyingState act
  catch _ =>
    pure default
  Core.setMessageLog savedMsgs
  return result

/-- Recursively decompile a proof term, but preserve correctness by falling back
    to an exact proof term when the generated tactics do not re-elaborate or do
    not fully close a fresh goal of the same type. -/
private def subproofTacticsCloseGoal (tacs : Array (TSyntax `tactic)) (expectedType : Expr)
    (lctx : LocalContext) (localInsts : LocalInstances) : TacticM Bool :=
  silentTry false do
    runInGoal lctx localInsts expectedType do
      let seq ← mkTacticSeq tacs
      evalTactic seq
      let remainingGoals ← getGoals
      let newMsgs ← Core.getMessageLog
      pure (!newMsgs.hasErrors && remainingGoals.isEmpty)

  /-- Check whether a candidate tactic block closes a fresh goal of the given type.
    This is useful for speculative terminal tactics where failure should simply
    let the decompiler continue trying other handlers.

    Each speculative attempt is bounded to `candidateMaxHeartbeats` so that a
    single pathological candidate (e.g. a `refine @Eq.mp` over natCast-heavy
    propext+Iff.intro chains, or a `lia` over the wrong polynomial form) cannot
    consume the entire ambient heartbeat budget and starve every subsequent
    handler attempt. The bound is intentionally generous (well above what a
    fast-path `lia` needs in practice) but tight enough that a single Eq.mp
    refine that times out at 6+s on the default 200k file budget can no longer
    block downstream handlers in the same recursion. Validation in
    `validateOrExact` / `subproofTacticsCloseGoal` directly is *not* bounded
    — that is the workhorse final check and must reflect the real elaborator.

    The value is in user-visible units (Lean multiplies internally by 1000
    to get the actual heartbeat counter threshold).  Default 100000 — half of
    Lean's default per-command budget of 200000 — and adjustable via the
    `leanDecomp.candidateMaxHeartbeats` option for nightly tuning without a
    rebuild. -/
  register_option leanDecomp.candidateMaxHeartbeats : Nat := {
    defValue := 100000
    descr := "Per-call heartbeat cap on speculative validation in \
      `candidateTacticsCloseGoal`. Tighter values fail more candidates fast \
      (more `exact` fallbacks); looser values let one slow candidate eat the \
      ambient budget. Default 100000 (= 100k user-visible heartbeats)."
  }

  def candidateTacticsCloseGoal (tacs : Array (TSyntax `tactic)) (expectedType : Expr)
    (lctx : LocalContext) (localInsts : LocalInstances) : TacticM Bool := do
    let bound := leanDecomp.candidateMaxHeartbeats.get (← getOptions)
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := bound * 1000 }) do
      Core.withCurrHeartbeats <|
        subproofTacticsCloseGoal tacs expectedType lctx localInsts

/-- True iff the type has shape `(_ : Bool) = (Bool.true : Bool)`.  This is the
    type of eagerReduce certificates emitted by grind's polynomial normalizers
    (`Int.Linear.norm_le`, etc.) — a Bool equality whose RHS is `true`.  Always
    decidable, so `decide` is a safe candidate. -/
private def isBoolEqTrue (ty : Expr) : Bool :=
  match ty.eq? with
  | some (α, _, rhs) => α.isConstOf ``Bool && rhs.isConstOf ``Bool.true
  | none => false

/-- Walk `lctx`, identify every inaccessible non-implementation-detail
    fvar in `lctx`, return a fresh accessible name.  The result is a
    pair:
    - `idents` (lctx order): the new accessible idents, suitable for
      `rename_i` (after reversing — see `chooseExactStrategy` for why).
    - `oldToNew`: a `Std.HashMap Name Name` from each inaccessible
      userName to its replacement.  Use with `replaceInaccessibleRefs`
      to post-process delabbed `Syntax` so references to old userNames
      become references to new accessible ones.  This is safer than
      mutating `lctx` and using `withLCtx` around the delab — that
      approach regressed the L234 structural decomp (the renamed lctx
      leaked into upstream validation paths).

    Use case: emitting an `exact <term>` fallback where the proof term
    references inaccessible hypotheses (e.g. `a✝` from a previous
    elaborator-implicit `intro`).  Without renaming, the rendered source
    contains `a✝` literally and fails re-elaboration with a type-mismatch
    on a free reference.  Concrete failure: `Mathlib/Algebra/Order/Ring/
    IsNonarchimedean.lean:216`. -/
def renameInaccessibleHyps (lctx : LocalContext) :
    Array Ident × Std.HashMap Name Name := Id.run do
  let mut idents : Array Ident := #[]
  let mut oldToNew : Std.HashMap Name Name := {}
  let mut idx := 0
  for declOpt in lctx.decls.toList do
    let some decl := declOpt | continue
    if decl.isImplementationDetail then continue
    -- Match the same set Lean's PrettyPrinter sanitizer would render as
    -- `name✝`: literal `✝` in any string component OR macro scopes.
    let needsRename := decl.userName.isInaccessibleUserName
                       || decl.userName.hasMacroScopes
    if !needsRename then continue
    idx := idx + 1
    let newName := Name.mkSimple s!"h_inacc_{idx}"
    oldToNew := oldToNew.insert decl.userName newName
    idents := idents.push (mkIdent newName)
  return (idents, oldToNew)

/-- Walk `stx` and replace each `Syntax.ident` whose name appears in
    `oldToNew` with a fresh ident bearing the new name.  Used to retarget
    delab output at renamed (now-accessible) bindings without having to
    delab inside a `withLCtx renamedLctx`. -/
def replaceInaccessibleRefs (stx : Syntax) (oldToNew : Std.HashMap Name Name) : Syntax :=
  if oldToNew.isEmpty then stx else
  Id.run <| stx.replaceM fun s =>
    match s with
    | .ident _ _ name _ =>
      match oldToNew.get? name with
      | some newName => pure (some (mkIdent newName).raw)
      | none => pure none
    | _ => pure none

/-- True iff `n` is a "user lemma" name worth handing to `grind only [...]`
    as a hint when reconstructing a proof.  Heuristic: reject names in the
    grind-internal certificate namespaces (Lean.Grind, Lean.Omega,
    Int.Linear, Lean.RArray) and structural primitives (Eq, Or, And, Iff,
    propext, eagerReduce, …).  Accept anything else — `grind only [a, b]`
    will silently ignore lemmas it can't make use of, so a few extras
    don't hurt.

    The point is to surface the lemmas grind ITSELF used during proof
    search (the original `grind [<hint>]` ones, plus any auto-discovered
    rewrites that show up in the proof term).  When all our structural
    handlers fail, re-running grind with EXACTLY this lemma set is the
    last-resort fallback — see `chooseExactStrategy`. -/
def isUserLemmaName (n : Name) : Bool :=
  let s := n.toString
  let internalPrefixes := [
    "Lean.Grind.", "Lean.Omega.", "Int.Linear.", "Lean.RArray.",
    "Lean.Parser.", "Lean.Elab.", "Lean.Meta."
  ]
  if internalPrefixes.any (s.startsWith ·) then false
  else if n.components.any (fun c =>
      let cs := c.toString
      -- Reject typeclass instance / projection names (`instLT`, `instAdd`,
      -- `instOfNatNat`, `Rat.instAdd`, `instIsPreorder_mathlib`, etc.).
      -- These pollute `grind only [...]` lists without contributing —
      -- grind synthesizes instances itself.
      cs.startsWith "inst" ||
      -- Reject typeclass projections (`Lattice.toSemilatticeInf`,
      -- `PartialOrder.toPreorder`, etc.).
      cs.startsWith "to") then false
  else
    let structuralExact := [
      "Eq", "Eq.refl", "Eq.trans", "Eq.symm", "Eq.mp", "Eq.mpr", "Eq.rec",
      "Eq.ndrec", "Eq.subst", "HEq", "HEq.refl",
      "Or", "Or.inl", "Or.inr", "Or.casesOn", "Or.elim", "Or.rec",
      "And", "And.intro", "And.left", "And.right", "And.casesOn", "And.rec",
      "Iff", "Iff.intro", "Iff.mp", "Iff.mpr", "Iff.casesOn", "Iff.refl",
      "Not", "False", "False.elim", "False.rec", "True", "True.intro",
      "Classical.byContradiction", "Classical.em", "Classical.byCases",
      "Classical.choice", "Classical.choose",
      "Exists", "Exists.intro", "Exists.casesOn", "Exists.elim",
      "id", "funext", "propext", "cast", "eagerReduce",
      "congrArg", "congrFun", "congr", "congrFun'",
      "eq_true", "eq_false", "of_eq_true", "of_eq_false",
      "absurd", "mt", "implies_congr", "forall_congr",
      -- Operator/literal classes (typeclass-related but caught by name).
      "LT.lt", "LE.le", "HAdd.hAdd", "HMul.hMul", "HSub.hSub",
      "OfNat.ofNat", "Neg.neg", "IntCast.intCast", "NatCast.natCast",
      "Membership.mem", "DFunLike.coe",
      -- Common type names that pass the above filter.
      "Nat", "Int", "Bool", "Bool.true", "Bool.false", "Rat", "Real",
      "Ne"
    ]
    !(structuralExact.any (· == s))

/-- Walk a proof term and collect distinct const names that look like
    user-callable lemmas (per `isUserLemmaName`).  Bounded walk (5000
    nodes) so giant proofs don't burn the heartbeat budget here.  Used by
    `chooseExactStrategy` to construct a `grind only [<extracted>]`
    last-resort fallback.

    Capped at 64 unique lemmas so the resulting `grind only` invocation
    has bounded parse/elaboration cost.  In practice typical proofs name
    1-5 user lemmas. -/
def extractGrindOnlyLemmas (e : Expr) : Array Name := Id.run do
  let mut found : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : List Expr := [e]
  let mut count := 0
  -- 100k node cap — large enough to walk a typical multi-KB grind proof
  -- (Rat L89 is ~13k nodes); small enough that pathological inputs don't
  -- burn the heartbeat budget.  A previous 5k cap missed `mkRat_pos_iff`
  -- in L89 because the user lemma appears past the 5k mark.
  while !stack.isEmpty && count < 100000 && order.size < 64 do
    count := count + 1
    let cur := stack.head!
    stack := stack.tail!
    match cur with
    | .const n _ =>
      if isUserLemmaName n && !found.contains n then
        found := found.insert n
        order := order.push n
    | .app f a => stack := f :: a :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .forallE _ t b _ => stack := t :: b :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | .mdata _ b => stack := b :: stack
    | .proj _ _ b => stack := b :: stack
    | _ => pure ()
  return order

/-- Configuration for `chooseExactStrategy`.  The three fallback sites differ
    only in this config (size check on/off, decide-first on/off, and whether
    propext/Iff.intro forces pp.all rendering). -/
structure ExactStrategyConfig where
  /-- Throw if the proof exceeds `throwIfFallbackProofTooLarge`'s node-count
      cap.  Used by `validateOrExact` (where the proof was meant to be a
      structural decomp result, not a giant raw term) but not by the final
      `decompExact` (where falling through to a giant `exact` is the
      last-resort behaviour anyway). -/
  enforceMaxSize : Bool := false
  /-- Try `decide` before `with_unfolding_all exact` when the proof contains
      `eagerReduce` and has type `_ = (true : Bool)` (the certificate shape).
      Same kernel work, much smaller residual term.  Gated on type shape
      because `decide` would fail on transport-wrapped forms and the
      validation attempt itself is expensive. -/
  tryDecideFirst : Bool := false
  /-- Extra predicates that force `pp.all` rendering on top of the always-on
      `containsEagerReduce` gate.  `mkExactFallbackTactics` adds propext /
      Iff.intro because validation just failed and the candidate is more
      likely to need full disambiguation; `decompExact` doesn't because
      pp.all on propext-containing proofs is dramatically slower to
      re-elaborate and most propext shapes are caught by earlier handlers. -/
  forcePrettyPrint : Expr → Bool := fun _ => false

/-- Unified policy for emitting an `exact` / `with_unfolding_all exact` /
    `decide` fallback.  Three call sites use this:

    - `mkExactFallbackTactics` (validation-failure fallback in
      `validateOrExact`): max-size check on, decide-first on, propext / Iff.intro
      force pp.all.
    - `decompExact` (last-resort fallback when no handler matched): max-size
      check off, decide-first off, only `eagerReduce` forces pp.all.

    A single function captures the term-syntax selection (delab vs pp.all) and
    the certificate-shape decide attempt so future changes (e.g. always
    trying `decide` first, or always pp.all-rendering propext) only need to
    edit one place. -/
def chooseExactStrategy (proof : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (cfg : ExactStrategyConfig)
    : TacticM (Array (TSyntax `tactic)) := do
  if cfg.enforceMaxSize then
    throwIfFallbackProofTooLarge proof
  -- Rename inaccessible hypotheses to accessible names BEFORE delab so
  -- the rendered source can refer to them.  Prepend a `rename_i` tactic
  -- to the result so re-elaboration ends up with matching names.
  -- See `renameInaccessibleHyps` docstring for the failure mode this
  -- addresses (`a✝` references in fallback exact term).
  -- NOTE 2026-05-07: `renameInaccessibleHyps` + `replaceInaccessibleRefs`
  -- are wired up in this file but NOT yet hooked into `chooseExactStrategy`.
  -- An attempt to prepend `rename_i ...` + post-process the delabbed
  -- term hung L216 at ≥120s validation (the rename_i + giant exact
  -- combination causes Lean's elaborator to explore a large search
  -- space, possibly looking for a typeclass instance whose old name has
  -- just been replaced).  The helpers are correct in isolation; revisit
  -- when we have a smaller scoped use case.
  let renamePrefix : Array (TSyntax `tactic) := #[]
  let needsPrettyPrint := containsEagerReduce proof || cfg.forcePrettyPrint proof
  let termStx ←
    if needsPrettyPrint then
      try ppExprToTermSyntaxWith proof true
      catch _ => delabRefinable proof
    else
      try delabRefinable proof
      catch _ => ppExprToTermSyntaxWith proof true
  -- Last-resort BEFORE the giant exact: try `grind only [<extracted>]`.
  -- The extracted lemmas come from the proof term (`extractGrindOnlyLemmas`)
  -- — these are the user-form lemmas grind picked up during proof search.
  -- A restricted `grind only [...]` is much more stable than bare grind
  -- (no automatic lemma instantiation), and dramatically cleaner than a
  -- 100KB raw exact term that may not even re-elaborate.
  --
  -- This is the explicit relax of the "no grind in output" policy: when
  -- nothing else closes, extracted-lemma `grind only` is the compromise.
  -- Order: specialized handlers fail → structural recursion fails → here.
  let proofTy ← instantiateMVars (← Meta.inferType proof)
  let lemmas := extractGrindOnlyLemmas proof
  if !lemmas.isEmpty then
    -- `grind only [a, b, c]` expects `grindParam`s, not bare idents.
    -- Each `grindParam` wraps a `grindLemma` which wraps the ident.
    -- See `Lean.Meta.Tactic.Grind.EMatchTheoremParam.toGrindParam`.
    let grindParams : Array (TSyntax ``Lean.Parser.Tactic.grindParam) ←
      lemmas.mapM fun n => do
        let lemmaStx ← `(Lean.Parser.Tactic.grindLemma| $(mkIdent n):ident)
        return ⟨Syntax.node SourceInfo.none ``Lean.Parser.Tactic.grindParam #[lemmaStx]⟩
    let grindTac ← `(tactic| grind only [$grindParams,*])
    if ← subproofTacticsCloseGoal #[grindTac] proofTy lctx localInsts then
      return renamePrefix.push grindTac
  if containsEagerReduce proof then
    if cfg.tryDecideFirst then
      if isBoolEqTrue proofTy then
        let decideTac ← `(tactic| decide)
        if ← subproofTacticsCloseGoal #[decideTac] proofTy lctx localInsts then
          return #[decideTac]
    let tac ← `(tactic| with_unfolding_all exact $termStx)
    return renamePrefix.push tac
  else
    let tac ← `(tactic| exact $termStx)
    return renamePrefix.push tac

/-- Validation-failure fallback.  Wraps `chooseExactStrategy` with the config
    used by `validateOrExact` — see `ExactStrategyConfig` for the rationale. -/
private def mkExactFallbackTactics (proof : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) : TacticM (Array (TSyntax `tactic)) :=
  chooseExactStrategy proof lctx localInsts {
    enforceMaxSize := true
    tryDecideFirst := true
    forcePrettyPrint := fun e =>
      containsConstName e ``propext || containsConstName e ``Iff.intro
  }

/-- Validate a candidate tactic block against the full proof goal and fall back
    to an exact proof term if validation fails.  On a `build` failure (either a
    thrown exception or a candidate that doesn't close the goal), the
    used-name state is rolled back to its pre-`build` snapshot — names
    introduced *only* in the failed branch shouldn't constrain subsequent
    handlers' name choices. -/
def validateOrExact (proof : Expr) (lctx : LocalContext) (localInsts : LocalInstances)
    (build : DecompM (Array (TSyntax `tactic)))
    : DecompM (Array (TSyntax `tactic)) := do
  let proofTy ← instantiateMVars (← Meta.inferType proof)
  let savedUsed ← getUsed
  try
    let candidateTacs ← build
    if ← subproofTacticsCloseGoal candidateTacs proofTy lctx localInsts then
      return candidateTacs
    else
      set savedUsed
      mkExactFallbackTactics proof lctx localInsts
  catch _ =>
    set savedUsed
    mkExactFallbackTactics proof lctx localInsts

def decompileOrExact (proof : Expr) (lctx : LocalContext) (localInsts : LocalInstances)
    (decompileExpr : DecompileCallback) : DecompM (Array (TSyntax `tactic)) :=
  validateOrExact proof lctx localInsts <| decompileExpr proof lctx localInsts

/-- Emit a tactic that may create multiple goals, then recursively decompile one
    proof term per generated goal into focused sub-blocks. This is the common
    shape used by theorem-style decompiler passes. -/
def emitTacticWithSubgoals (headTac : TSyntax `tactic) (subgoalProofs : Array Expr)
    (lctx : LocalContext) (localInsts : LocalInstances)
  (decompileExpr : DecompileCallback) : DecompM (Array (TSyntax `tactic)) := do
  let mut allTacs : Array (TSyntax `tactic) := #[headTac]
  for proof in subgoalProofs do
    let chosenTacs ← decompileOrExact proof lctx localInsts decompileExpr
    let blockTac ← mkFocusedBlock chosenTacs
    allTacs := allTacs.push blockTac
  return allTacs

def binderBaseName (idx : Nat) (name : Name) : String :=
  let raw := name.eraseMacroScopes.toString
  let lastSegment := (raw.splitOn ".").reverse.headD raw
  let cleaned := lastSegment.replace "'" ""
  if cleaned = "" || cleaned = "_" then s!"x{idx + 1}" else cleaned

def mkUniqueName (base : String) (used : List String) : String :=
  if !(used.contains base) then base
  else
    let rec loop (suffix remaining : Nat) : String :=
      let candidate := s!"{base}_{suffix}"
      match remaining with
      | 0 => candidate
      | Nat.succ remaining' =>
          if used.contains candidate then
            loop (suffix + 1) remaining'
          else
            candidate
    loop 1 (used.length + 1)

/-- Choose a fresh name based on `userName` (or a positional fallback
    `x{idx+1}` when the user name is empty/`_`) that doesn't collide with any
    name already in the used-names state, and add it to the state.

    `idx` is the per-binder position used to construct the fallback name.
    For binders introduced as part of an `assignIntroNames` batch, pass the
    local position counter (so two consecutive `_` binders get base names
    `x1` and `x2`).  For singleton binders introduced outside a batch
    (`tryDecompByContradiction`, `tryDecompLet`, etc.) pass
    `(← getUsed).length` — preserves the snapshot test naming output. -/
def chooseIntroName (idx : Nat) (userName : Name) : DecompM String := do
  let used ← getUsed
  let base := binderBaseName idx userName
  let introName := mkUniqueName base used
  addUsed introName
  return introName

def assignIntroNames (xs : Array Expr) : DecompM (List String × LocalContext) := do
  let mut names : List String := []
  let mut lctx ← getLCtx
  let mut idx : Nat := 0
  for x in xs do
    let some fvarId := x.fvarId?
      | throwError "Unexpected non-fvar binder in proof term"
    let decl ← fvarId.getDecl
    let introName ← chooseIntroName idx decl.userName
    names := introName :: names
    let newName := Name.mkSimple introName
    lctx := lctx.setUserName fvarId newName
    idx := idx + 1
  return (names.reverse, lctx)

/-- Convert intro names to identifier syntax -/
def namesToIdents (names : List String) : Array Ident :=
  names.toArray.map (fun n => mkIdent (Name.mkSimple n))

/-- Check if an expression contains tactic-generated automation internals such
  as grind certificates or linear-arithmetic scaffolding. Walks at most 5000
  nodes. -/
def containsAutomationInternals (e : Expr) : Bool := Id.run do
  let mut stack : List Expr := [e]
  let mut count := 0
  while !stack.isEmpty && count < 5000 do
    let cur := stack.head!
    stack := stack.tail!
    count := count + 1
    match cur with
    | .const n _ =>
      let s := n.toString
      if s.startsWith "Int.Linear." || s.startsWith "Lean.Grind." || s.startsWith "Lean.RArray." then
        return true
    | .app f a => stack := f :: a :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .forallE _ t b _ => stack := t :: b :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | .mdata _ e => stack := e :: stack
    | _ => pure ()
  return false

/-- Check if a constant name is "structural" — i.e., part of the equality /
    congruence / boolean-decidability machinery that grind uses to chain
    proofs, not a meaningful library fact.  Used by `extractGrindFacts` to
    decide which subterms are interesting "user-form" hypotheses worth
    surfacing as a `have`.

    The namespace checks (`Eq`, `Classical`) use `Name.isPrefixOf` against
    `Name` literals.  The `congr*` / `*_congr*` / `eq_true*` / `eq_false*`
    checks remain string-prefixed because those are top-level names with no
    common namespace parent — there's no `Name` literal that captures
    "anything starting with `congr` in the root namespace", and enumerating
    every `congr…` lemma in mathlib is not maintainable.  Misclassification
    is non-critical: it just shifts whether a fact is named in a `have` or
    threaded raw, neither of which breaks correctness. -/
private def isStructuralConst (n : Name) : Bool :=
  Name.isPrefixOf `Eq n || Name.isPrefixOf `Classical n ||
  let s := n.toString
  s.startsWith "congr" || s.startsWith "implies_congr" ||
  s.startsWith "forall_congr" || s.startsWith "eq_true" || s.startsWith "eq_false" ||
  n == ``True.intro || n == ``False.rec || n == ``False.elim ||
  n == ``eagerReduce || n == ``id || n == ``funext || n == ``propext ||
  n == ``Iff.intro ||
  n == ``And.intro ||
  n == ``Or.inl || n == ``Or.inr || n == ``Not ||
  n == ``Bool.true || n == ``Bool.false ||
  n == ``rfl

/-- Check if a constant name is grind-internal — namespaces emitted by grind's
    polynomial normalizers and indexers, never user-facing facts.

    Single-backtick `Name` literals (raw, unchecked) — these are *namespace*
    names and don't correspond to any defined constant, so the double-backtick
    form would fail elaboration. -/
private def isGrindConst (n : Name) : Bool :=
  Name.isPrefixOf `Int.Linear n ||
  Name.isPrefixOf `Lean.Grind n ||
  Name.isPrefixOf `Lean.RArray n

/-- Extract "interesting" subexpressions from a grind proof term.
  These are applications of library lemmas (not structural, not grind-internal)
  whose types are propositions. Callers can turn them into named `have` facts
  before continuing structural decompilation. -/
def extractGrindFacts (e : Expr) : MetaM (Array Expr) := do
  let mut result : Array Expr := #[]
  let mut stack : List Expr := [e]
  let mut seen : Std.HashSet UInt64 := {}
  let mut count := 0
  while !stack.isEmpty && count < 10000 do
    let cur := stack.head!
    stack := stack.tail!
    count := count + 1
    -- Deduplicate by pointer hash
    let h := cur.hash
    if seen.contains h then continue
    seen := seen.insert h
    match cur with
    | .app .. =>
      -- Peel to head constant
      let fn := cur.getAppFn
      let args := cur.getAppArgs
      match fn with
      | .const n _ =>
        if isGrindConst n then
          -- Don't collect grind applications, but DO recurse into their args
          -- because library facts may be passed as arguments to grind lemmas
          for a in args do stack := a :: stack
        else if isStructuralConst n then
          -- Recurse into args of structural constants
          for a in args do stack := a :: stack
        else
          -- Library/user lemma application — check if it's a Prop
          let ty ← try Meta.inferType cur catch _ => continue
          let sort ← try Meta.inferType ty catch _ => continue
          if sort.isProp then
            -- ty is a Prop — this is an interesting fact
            result := result.push cur
          -- Also recurse into args in case there are nested interesting facts
          for a in args do stack := a :: stack
      | .fvar .. =>
        -- fvar application — check if it's a Prop
        let ty ← try Meta.inferType cur catch _ => continue
        let sort ← try Meta.inferType ty catch _ => continue
        if sort.isProp then
          result := result.push cur
        for a in args do stack := a :: stack
      | _ =>
        for a in args do stack := a :: stack
        stack := fn :: stack
    | .lam _ t b _ => stack := t :: b :: stack
    | .mdata _ e => stack := e :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | _ => pure ()
  return result


end LeanDecomp
