import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import LeanDecomp.Helpers
import LeanDecomp.CasesOn
import LeanDecomp.EqDecomp
import LeanDecomp.Specialized
import LeanDecomp.Simplify

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

private def theoremHeadToExplicitTermSyntax (headName : Name) : MetaM Term := do
  let env ← getEnv
  let headStr := s!"@{headName}"
  match Parser.runParserCategory env `term headStr with
  | .ok stx => pure ⟨stx⟩
  | .error err =>
    throwError "failed to parse theorem head:\n{err}\n\n{headStr}"

private def theoremAppToNotationTermSyntax (headName : Name) (args : List Expr)
    (holeMask : Array Bool := #[]) : MetaM Term := do
  let headTerm ← theoremHeadToExplicitTermSyntax headName
  let mut argTerms : Array Term := #[]
  for h : i in [:args.length] do
    let arg := args[i]
    let useHole := holeMask.getD i false
    let argTerm ← if useHole || (← Meta.isProof arg) then
        `(term| ?_)
      else
        let argType ← instantiateMVars (← Meta.inferType arg)
        if argType.isSort then
          try ppExprToTermSyntaxWith arg false
          catch _ => delabToRefinableSyntax arg
        else
          delabToRefinableSyntax arg
    argTerms := argTerms.push argTerm
  pure <| Syntax.mkApp headTerm argTerms

private def refineTacProducesGoals (term : Term) (expectedType : Expr)
  (expectedGoals : Nat) (lctx : LocalContext) (localInsts : LocalInstances) : TacticM Bool :=
  silentTry false do
    withLCtx lctx localInsts do
      let goal ← Meta.mkFreshExprMVar (some expectedType) .syntheticOpaque
      let tac ← `(tactic| refine $term)
      let goals ← Tactic.run goal.mvarId! do
        evalTactic tac
      let newMsgs ← Core.getMessageLog
      pure (!newMsgs.hasErrors && goals.length == expectedGoals)

private def refineTacMatchesProofArgs (term : Term) (expectedType : Expr)
  (proofArgs : Array Expr) (lctx : LocalContext) (localInsts : LocalInstances) : TacticM Bool :=
  silentTry false do
    withLCtx lctx localInsts do
      let goal ← Meta.mkFreshExprMVar (some expectedType) .syntheticOpaque
      let tac ← `(tactic| refine $term)
      let goals := (← Tactic.run goal.mvarId! do
        evalTactic tac
        ).toArray
      let newMsgs ← Core.getMessageLog
      if newMsgs.hasErrors || goals.size != proofArgs.size then
        pure false
      else
        let mut ok := true
        for i in [:proofArgs.size] do
          let goalId := goals[i]!
          let proofArg := proofArgs[i]!
          let proofTy ← instantiateMVars (← Meta.inferType proofArg)
          let sameType ← goalId.withContext do
            let goalTy ← instantiateMVars (← goalId.getType)
            Meta.isDefEq goalTy proofTy
          if !sameType then
            ok := false
        pure ok

/-- Flatten nested arrays of tactics -/
private def flattenTactics (tacss : List (Array (TSyntax `tactic))) : Array (TSyntax `tactic) :=
  tacss.foldl (· ++ ·) #[]

private partial def containsCastLike (e : Expr) : Bool :=
  Expr.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some n =>
        n == ``NatCast.natCast || n == ``IntCast.intCast || n == ``OfNat.ofNat ||
          n == ``Nat.cast || n == ``Int.ofNat
    | none => false) e |>.isSome

private def hasProblematicEvidence (e : Expr) : Bool :=
  containsAutomationInternals e || containsConstName e ``eagerReduce ||
    containsConstName e ``of_decide_eq_true || containsConstName e ``propext ||
    containsConstName e ``Iff.intro || containsCastLike e

private partial def containsArithRelevantConst (e : Expr) : Bool :=
  Expr.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some n =>
        n == ``Int || n == ``Nat || n == ``LE.le || n == ``LT.lt ||
          n == ``GE.ge || n == ``GT.gt || n == ``Dvd.dvd ||
          n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul ||
          n == ``OfNat.ofNat || n == ``Nat.succ || n == ``Nat.sub || n == ``Int.sub ||
          n == ``Int.add || n == ``Int.mul || n == ``Nat.add || n == ``Nat.mul
    | none => false) e |>.isSome

private partial def containsArithmeticAutomationConst (e : Expr) : Bool :=
  Expr.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some n =>
        let s := toString n
        s.startsWith "Int.Linear." ||
          s.startsWith "Nat.Linear." ||
          s.startsWith "Lean.Grind.Order." ||
          s.startsWith "Lean.Grind.CommRing."
    | none => false) e |>.isSome

private def isArithmeticLikeGoal (expr : Expr) : MetaM Bool := do
  let ty ← instantiateMVars (← Meta.inferType expr)
  pure <|
    containsArithRelevantConst ty ||
      containsArithRelevantConst expr ||
      containsArithmeticAutomationConst expr

private def tryValidatedTerminalTactic (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (tac : TSyntax `tactic)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  let expectedType ← instantiateMVars (← Meta.inferType expr)
  if ← LeanDecomp.candidateTacticsCloseGoal #[tac] expectedType lctx localInsts then
    return some (#[tac], used)
  return none

private def tryDecompExactLocalHyp (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let some fvarId := expr.fvarId? | return none
    let decl ← fvarId.getDecl
    let tac ← `(tactic| exact $(mkIdent decl.userName):ident)
    return some (#[tac], used)

private def tryDecompArithmeticTerminalPasses (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    if !(← isArithmeticLikeGoal expr) then
      return none
    let liaTac ← `(tactic| lia)
    if let some result ← tryValidatedTerminalTactic expr lctx localInsts used liaTac then
        return some result
    let orderTac ← `(tactic| grind_order)
    if let some result ← tryValidatedTerminalTactic expr lctx localInsts used orderTac then
      return some result
    let linarithTac ← `(tactic| grind_linarith)
    tryValidatedTerminalTactic expr lctx localInsts used linarithTac

/-- Return `true` when the head of the application looks like a theorem-level
    proof constructor rather than data construction. This is intentionally broad:
    the handler is placed late in the pipeline, so more specific patterns still
    win, and we fall back to `exact` if the application has no proof arguments. -/
private def isTheoremAppHead? (e : Expr) : Option Name :=
  match e.getAppFn.constName? with
  | some name => some name
  | none => none

private def isConstructorName (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.ctorInfo _) => true
  | _ => false

/-- Treat explicit proof functions like `∀ x, P x → Q x` as proof-like so theorem
    applications can recurse into them instead of embedding large lambda terms raw. -/
private def isProofLikeBinderType (binderType : Expr) : MetaM Bool := do
  let binderType ← instantiateMVars binderType
  let binderType ← Meta.whnf binderType
  if ← Meta.isProp binderType then
    return true
  Meta.forallTelescopeReducing binderType fun _ body =>
    Meta.isProp body

/-- Try a list of computations in order, returning the first `some` result. -/
private def firstSomeM [Monad m] (xs : List (m (Option α))) : m (Option α) := do
  for x in xs do
    if let some res ← x then
      return some res
  return none

private partial def tryDecompProblematicProofApp (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some _ := fn.fvarId? | return none
    if args.isEmpty then
      return none

    let mut app := fn
    let mut remainingType ← Meta.inferType fn
    let mut proofArgs : Array Expr := #[]
    let mut sawProblematicProofArg := false
    let mut hasNonProofArg := false

    for arg in args do
      remainingType ← Meta.whnf remainingType
      let .forallE _ binderType body _ := remainingType
        | return none
      if ← Meta.isProp binderType then
        let hole ← Meta.mkFreshExprSyntheticOpaqueMVar binderType
        app := mkApp app hole
        proofArgs := proofArgs.push arg
        if hasProblematicEvidence arg then
          sawProblematicProofArg := true
      else
        app := mkApp app arg
        hasNonProofArg := true
      remainingType := body.instantiate1 arg

    if proofArgs.isEmpty || !sawProblematicProofArg then
      return none

    let headTerm ← delabToRefinableSyntax fn
    let headTac ← if hasNonProofArg then
        let refineTerm ← delabToRefinableSyntax app
        `(tactic| refine $refineTerm)
      else
        `(tactic| apply $headTerm)
    let result ← LeanDecomp.emitTacticWithSubgoals headTac proofArgs lctx localInsts used decompileExpr
    return some result

private partial def tryDecompIffIntro (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some constName := Expr.constName? fn | return none
    if constName != ``Iff.intro || args.length < 4 then
      return none
    let fwd := args[2]!
    let bwd := args[3]!
    let constructorTac ← `(tactic| constructor)
    let result ← LeanDecomp.emitTacticWithSubgoals constructorTac #[fwd, bwd] lctx localInsts used decompileExpr
    return some result

private partial def tryDecompIffMpMpr (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some constName := Expr.constName? fn | return none
    if constName != ``Iff.mp && constName != ``Iff.mpr then
      return none
    if args.length < 4 then
      return none
    let iffProof := args[2]!
    let premiseProof := args[3]!
    let headIdent : Ident := ⟨mkIdent constName |>.raw.setInfo .none⟩
    let refineTac ← `(tactic| refine $headIdent:ident ?_ ?_)
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[iffProof, premiseProof] lctx localInsts used decompileExpr
    return some result

/-- Handle `And.intro a b <pfA> <pfB>` by emitting `refine ⟨?_, ?_⟩` with the
    two component proofs as recursive subgoals. Without this, the theorem-app
    fallback bails on constructor heads and the whole `And.intro` collapses
    into a single `exact` term. When the components are large, splitting them
    lets each side be closed by a cheaper handler such as `lia`.

    Skip when both components are local hypotheses: for trivial cases like
    `And.intro a b ha hb` the natural decomp is `exact ⟨ha, hb⟩`, which the
    theorem-app fallback handles directly. Splitting those is just churn. -/
private partial def tryDecompAndIntro (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some constName := Expr.constName? fn | return none
    if constName != ``And.intro then return none
    -- @And.intro takes {a b : Prop} (left : a) (right : b), so exactly 4 args.
    if args.length != 4 then return none
    let leftProof := args[2]!
    let rightProof := args[3]!
    if leftProof.isFVar && rightProof.isFVar then return none
    let refineTac ← `(tactic| refine ⟨?_, ?_⟩)
    let result ← LeanDecomp.emitTacticWithSubgoals refineTac #[leftProof, rightProof] lctx localInsts used decompileExpr
    return some result

private partial def tryDecompAndProj (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some constName := Expr.constName? fn | return none
    if constName != ``And.left && constName != ``And.right then
      return none
    -- @And.left/right takes {a b : Prop} (h : a ∧ b), so exactly 3 args.
    -- Let the applied case (extra args) fall through to the theorem-app fallback
    -- so both the And proof and the extra proof args get recursive subgoals.
    if args.length != 3 then
      return none
    let andProof := args[2]!
    let headIdent : Ident := ⟨mkIdent constName |>.raw.setInfo .none⟩
    let applyTac ← `(tactic| apply $headIdent:ident)
    let result ← LeanDecomp.emitTacticWithSubgoals applyTac #[andProof] lctx localInsts used decompileExpr
    return some result

private partial def tryDecompPropext (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String) (decompileExpr : DecompileCallback)
    : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
  withLCtx lctx localInsts do
    let (fn, args) := peelArgs expr
    let some constName := Expr.constName? fn | return none
    if constName != ``propext then
      return none
    let some iffProof := args.getLast? | return none
    let propextIdent : Ident := ⟨mkIdent ``propext |>.raw.setInfo .none⟩
    let applyTac ← `(tactic| apply $propextIdent:ident)
    let result ← LeanDecomp.emitTacticWithSubgoals applyTac #[iffProof] lctx localInsts used decompileExpr
    return some result

mutual

  /-- Convert a proof term expression into tactic syntax.

  **Decompiler invariant**.  The `lctx` and `localInsts` parameters define the
  local context in which `expr` is well-typed; this same context is the one in
  which any candidate tactics produced for `expr` are validated by
  `validateOrExact`.  For every recursive call into `decompileExpr`, callers
  must supply a `(lctx, localInsts)` that matches the proof state the *real*
  run of the surrounding tactics would produce — otherwise validation false-
  negatives sneak in (the canonical example is `tryDecompCasesOn`'s per-branch
  recursion, which uses `MVarId.cases` to obtain the substituted lctx for
  exactly this reason).

  Recursion sites that already maintain the invariant naturally:
  - `tryDecompIntro`: synthesizes a renamed lctx for the lambda binders, which
    matches what real `intro` produces.
  - `tryDecompLet` / `tryDecompBetaRedex`: extends lctx with a let-decl, which
    matches what real `let` produces.
  - `tryDecompByContradiction`: synthesizes a binder via `Meta.forallTelescope`,
    matching what real `intro` does after `apply Classical.byContradiction`.
  - `emitTacticWithSubgoals`: passes the outer lctx through, valid for refines
    that don't change the lctx (apply, refine `?_`, And.intro, etc.).
  - `tryDecompCasesOn`: uses `MVarId.cases` to produce the real substituted
    lctx for non-generalized motives.

  Documented limitations:
  - Generalized cases motives (`cases h : disc with`) currently fall back to
    a synthesized lctx.  Validation false-negatives are still possible there;
    `decompileOrExact` will silently degrade to `exact` when they bite. -/
  partial def decompileExpr (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Array (TSyntax `tactic) × List String) := do
    withLCtx lctx localInsts do
      Meta.lambdaTelescope expr fun xs body => do
        if xs.size > 0 then
          -- Use the current local context from inside lambdaTelescope
          let telescopeLctx ← getLCtx
          let telescopeInsts ← getLocalInstances
          tryDecompIntro xs body telescopeLctx telescopeInsts used
        else
          -- Pure beta reduction for lambda-headed applications.
          -- lambdaTelescope's whnfD also does delta reduction (unfolding casesOn to rec),
          -- so we reduce only beta-redexes here to preserve structure.
          let mut body := body
          while body.isApp && body.getAppFn.isLambda do
            body := body.headBeta
          let specialized? ← firstSomeM [
            tryDecompExactLocalHyp body lctx localInsts used,
            tryDecompProblematicProofApp body lctx localInsts used decompileExpr,
            tryDecompByContradiction body lctx localInsts used,
            tryDecompCasesOn body lctx localInsts used decompileExpr assignIntroNames,
            trySpecializedDecompHandlers body lctx localInsts used decompileExpr,
            tryDecompPropext body lctx localInsts used decompileExpr,
            tryDecompIffIntro body lctx localInsts used decompileExpr,
            tryDecompIffMpMpr body lctx localInsts used decompileExpr,
            tryDecompAndIntro body lctx localInsts used decompileExpr,
            tryDecompAndProj body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompCongr body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompCongrArg body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqSymm body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqTrans body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqRecPropTransport body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqMpForallCongr body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqMpImpliesCongr body lctx localInsts used decompileExpr,
            LeanDecomp.tryDecompEqMp body lctx localInsts used decompileExpr,
            tryDecompFalseRec body lctx localInsts used,
            tryDecompFalseType body lctx localInsts used,
            tryDecompLet body lctx localInsts used,
            tryDecompBetaRedex body lctx localInsts used,
            tryDecompEagerReduce body lctx localInsts used,
            tryDecompEqRefl body lctx localInsts used,
            tryDecompDecide body lctx localInsts used,
            tryDecompArithmeticTerminalPasses body lctx localInsts used,
            tryDecompTheoremAppFallback body lctx localInsts used
          ]
          match specialized? with
          | some res => pure res
          | none => decompExact body used

  private partial def tryDecompIntro (xs : Array Expr) (body : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Array (TSyntax `tactic) × List String) := do
    withLCtx lctx localInsts do
      let (introNames, newLctx, used') ← assignIntroNames xs used
      let newLocalInsts ← getLocalInstances
      let (bodyTactics, used'') ← decompileExpr body newLctx newLocalInsts used'
      let introTac ← if introNames.isEmpty then
          pure #[]
        else
          let idents := namesToIdents introNames
          let tac ← `(tactic| intro $[$idents]*)
          pure #[tac]
      return (introTac ++ bodyTactics, used'')

  private partial def tryDecompByContradiction (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
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
          let (binderName, used') := chooseIntroName used.length decl.userName used
          let renamedBinderLctx := lctxWithBinder.setUserName fvarId (Name.mkSimple binderName)
          let binderLocalInsts ← getLocalInstances
          let applied := Expr.app handler binder
          let binderIdent := mkIdent (Name.mkSimple binderName)
          -- Use mkIdent with no info to avoid hygiene marks (✝) in pretty-printed output
          let byContradictionIdent : Ident := ⟨mkIdent ``Classical.byContradiction |>.raw.setInfo .none⟩
          let applyTac ← `(tactic| apply $byContradictionIdent:ident)
          let introTac ← `(tactic| intro $binderIdent:ident)
          -- Prefer structural decompilation of the contradiction body before
          -- trying arithmetic terminals like `lia`. This keeps contradiction-
          -- shaped proofs stable and avoids collapsing non-arithmetic branches
          -- into `lia` when the recursive handlers already know how to emit a
          -- more faithful script.
          try
            let (bodyTactics, used'') ← decompileExpr applied renamedBinderLctx binderLocalInsts used'
            let candidate := #[applyTac, introTac] ++ bodyTactics
            let exprTy ← instantiateMVars (← Meta.inferType expr)
            if ← LeanDecomp.candidateTacticsCloseGoal candidate exprTy lctx localInsts then
              return some (candidate, used'')
          catch _ =>
            pure ()
          if let some (branchTactics, used'') ←
              tryDecompArithmeticTerminalPasses applied renamedBinderLctx binderLocalInsts used' then
            return some (#[applyTac, introTac] ++ branchTactics, used'')
          let result ← LeanDecomp.validateOrExact expr lctx localInsts used do
            let (bodyTactics, used'') ← decompileExpr applied renamedBinderLctx binderLocalInsts used'
            return (#[applyTac, introTac] ++ bodyTactics, used'')
          return some result
        else
          return none

  /-- Handle beta redex: `(fun x => body) arg`.
      For fvar arguments, emit a let binding for readability.
      For non-fvar arguments, beta-reduce and recurse. -/
  private partial def tryDecompBetaRedex (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let .app fn arg := expr | return none
      let .lam binderName binderType body _binderInfo := fn | return none
      if let some argFvarId := arg.fvarId? then
        let argDecl ← argFvarId.getDecl
        let argName := argDecl.userName
        let letBinderName := binderBaseName used.length binderName
        let letBinderId := FVarId.mk (← mkFreshId)
        let newLctx := lctx.mkLetDecl letBinderId (Name.mkSimple letBinderName) binderType arg
        let newLocalInsts ← getLocalInstances
        let used' := letBinderName :: used
        let newBody := body.instantiate1 (Expr.fvar letBinderId)
        let (bodyTactics, used'') ← decompileExpr newBody newLctx newLocalInsts used'
        let letBinderIdent := mkIdent (Name.mkSimple letBinderName)
        let argIdent := mkIdent argName
        let letTac ← `(tactic| let $letBinderIdent := $argIdent)
        return some (#[letTac] ++ bodyTactics, used'')
      else
        let reduced := body.instantiate1 arg
        let (tactics, used') ← decompileExpr reduced lctx localInsts used
        return some (tactics, used')

  /-- Handle let-expressions by introducing tactic-level `let` bindings, then
      recursively decompiling the body in the extended local context. This keeps
      low-level proof terms readable and exposes theorem applications hidden at
      the end of let-heavy generated terms. -/
  private partial def tryDecompLet (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let .letE binderName _binderType value body _ := expr | return none
      let (letName, used') := chooseIntroName used.length binderName used
      let letFVarId := FVarId.mk (← mkFreshId)
      let letDeclName := Name.mkSimple letName
      let newLctx := lctx.mkLetDecl letFVarId letDeclName (← Meta.inferType value) value
      let newBody := body.instantiate1 (Expr.fvar letFVarId)
      let valueStx ← delabToRefinableSyntax value
      let letTac ← `(tactic| let $(mkIdent letDeclName):ident := $valueStx)
      let (bodyTactics, used'') ← withLCtx newLctx localInsts do
        let newLocalInsts ← getLocalInstances
        decompileExpr newBody newLctx newLocalInsts used'
      return some (#[letTac] ++ bodyTactics, used'')

  /-- Handle `False.rec`, `False.elim`, and `False.casesOn` terms. -/
  private partial def tryDecompFalseRec (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, args) := peelArgs expr
      let some constName := Expr.constName? fn
        | return none
      if constName != ``False.rec && constName != ``False.elim && constName != ``False.casesOn then
        return none

      let falseTy := mkConst ``False
      let rec findFalseArg (xs : List Expr) : MetaM (Option Expr) := do
        match xs with
        | [] => return none
        | x :: xs' =>
            let xTy ← Meta.inferType x
            if (← Meta.isDefEq xTy falseTy) then
              return some x
            else
              findFalseArg xs'

      let some falseArg ← findFalseArg args
        | return none

      -- Try to simplify: detect `Eq.mp (eq_true h ... eq_false h') True.intro`
      -- and replace with `exact absurd h h'`. This works at tactic level because
      -- casesOn branches unify the types that differ at the Expr level.
      if let some (h, h') := extractContradiction falseArg then
        let hStx ← delabToRefinableSyntax h
        let h'Stx ← delabToRefinableSyntax h'
        let absurdId := mkIdent ``absurd
        let tac ← `(tactic| exact $absurdId $hStx $h'Stx)
        return some (#[tac], used)

      -- Best case: contradiction hypothesis is already a local variable.
      if let some falseFVarId := falseArg.fvarId? then
        let decl ← falseFVarId.getDecl
        let hFalseTarget : TSyntax `Lean.Parser.Tactic.elimTarget ←
          `(Lean.Parser.Tactic.elimTarget| $(mkIdent decl.userName):ident)
        let casesTac ← `(tactic| cases $hFalseTarget)
        return some (#[casesTac], used)

      -- `contradiction` only meaningfully closes a `False` goal; for any other
      -- goal type (typically when `False.elim` is being used polymorphically
      -- to derive a non-`False` conclusion), it cannot close and emitting it
      -- forces the caller to fall back to a giant `exact`. Return none in
      -- that case so dispatch falls through to the theorem-app fallback,
      -- which decomposes False.rec/elim structurally.
      let exprTy ← Meta.inferType expr
      unless exprTy.isConstOf ``False do return none
      let contradictionTac ← `(tactic| contradiction)
      return some (#[contradictionTac], used)

  /-- Handle `of_decide_eq_true` — emit `decide`.
      `decide` elaborates to `of_decide_eq_true <proof>`, so we recognize
      this pattern and replace the entire term with the `decide` tactic. -/
  private partial def tryDecompDecide (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, _) := peelArgs expr
      let some constName := fn.constName? | return none
      if constName != ``of_decide_eq_true then return none
      let tac ← `(tactic| decide)
      return some (#[tac], used)

  /-- `eagerReduce` is a proof-producing reduction wrapper used in low-level
      Grind certificates. At tactic level, `decide` is a much smaller proof of
      the resulting reducible proposition. -/
  private partial def tryDecompEagerReduce (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, _) := peelArgs expr
      let some constName := fn.constName? | return none
      if constName != ``eagerReduce then return none
      let tac ← `(tactic| decide)
      return some (#[tac], used)

  /-- `Eq.refl` proof terms are better rendered as `rfl`. -/
  private partial def tryDecompEqRefl (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, _) := peelArgs expr
      let some constName := fn.constName? | return none
      if constName != ``Eq.refl then return none
      let tac ← `(tactic| rfl)
      return some (#[tac], used)

  /-- Late fallback for theorem applications: refine with holes for proof
      arguments, then solve each generated subgoal recursively. This keeps the
      theorem-level structure available to the decompiler instead of collapsing
      everything into a single `exact` term. Terms with problematic evidence are
      the main motivation, but the shape is generic and not grind-specific. -/
  private partial def tryDecompTheoremAppFallback (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let (fn, args) := peelArgs expr
      if args.isEmpty then
        return none
      let headName? := isTheoremAppHead? fn
      if let some headName := headName? then
        if isConstructorName (← getEnv) headName then
          return none

      let mut app := fn
      let mut remainingType ← Meta.inferType fn
      let mut proofArgs : Array Expr := #[]
      let mut proofLikeMask : Array Bool := #[]
      let mut sawProofArg := false
      let problematic := hasProblematicEvidence expr

      for arg in args do
        remainingType ← Meta.whnf remainingType
        let .forallE _ binderType body _ := remainingType
          | return none
        if ← isProofLikeBinderType binderType then
          let hole ← Meta.mkFreshExprSyntheticOpaqueMVar binderType
          app := mkApp app hole
          proofArgs := proofArgs.push arg
          proofLikeMask := proofLikeMask.push true
          sawProofArg := true
        else
          app := mkApp app arg
          proofLikeMask := proofLikeMask.push false
        remainingType := body.instantiate1 arg

      if !sawProofArg then
        return none

      -- Keep the fallback cheap for ordinary theorem applications: if nothing in
      -- the term looks suspicious, only use this path when there are multiple
      -- proof arguments, where preserving subgoal structure is usually helpful.
      if !problematic && proofArgs.size < 2 then
        return none

      let exprTy ← Meta.inferType expr
      let delabTerm ← delabToRefinableSyntax app
      if ← refineTacMatchesProofArgs delabTerm exprTy proofArgs lctx localInsts then
        let refineTac ← `(tactic| refine $delabTerm)
        let result ← LeanDecomp.emitTacticWithSubgoals refineTac proofArgs lctx localInsts used decompileExpr
        return some result

      if let some headName := headName? then
        let notationTerm ← theoremAppToNotationTermSyntax headName args proofLikeMask
        if ← refineTacMatchesProofArgs notationTerm exprTy proofArgs lctx localInsts then
          let refineTac ← `(tactic| refine $notationTerm)
          let result ← LeanDecomp.emitTacticWithSubgoals refineTac proofArgs lctx localInsts used decompileExpr
          return some result

      let compactTerm ←
        try ppExprToTermSyntaxWith app false
        catch _ => delabToRefinableSyntax app
      let usePpAll := !(← refineTacProducesGoals compactTerm exprTy proofArgs.size lctx localInsts)
      let refineTerm ← if usePpAll then
          try ppExprToTermSyntaxWith app true
          catch _ => pure compactTerm
        else
          pure compactTerm
      let refineTac ← `(tactic| refine $refineTerm)
      let result ← LeanDecomp.emitTacticWithSubgoals refineTac proofArgs lctx localInsts used decompileExpr
      return some result

  /-- The final exact fallback. When the term carries grind's `eagerReduce`
      gadgets, wrap the `exact` in `with_unfolding_all` so the elaborator runs
      with the same all-transparency setting grind used to build the term. -/
  private partial def decompExact (body : Expr) (used : List String) :
      TacticM (Array (TSyntax `tactic) × List String) := do
    -- Only use pp.all for `eagerReduce` gadgets, where the explicit polynomial
    -- coefficients matter for elaboration. `propext` / `Iff.intro` containing
    -- bodies elaborate fine with regular delab, and pp.all makes them
    -- dramatically slower to re-check (they fully expand instances).
    let usePrettyPrintedTerm := containsEagerReduce body
    let termStx ← if usePrettyPrintedTerm then
        try ppExprToTermSyntaxWith body true
        catch _ => delabToRefinableSyntax body
      else
        try delabToRefinableSyntax body
        catch _ => ppExprToTermSyntaxWith body true
    if containsEagerReduce body then
      let tac ← `(tactic| with_unfolding_all exact $termStx)
      return (#[tac], used)
    else
      let tac ← `(tactic| exact $termStx)
      return (#[tac], used)

  /-- Handle any expression whose type is `False` — emit `contradiction`.
      Only fires when the local context contains an obvious contradiction
      (a `False` hypothesis, or `h : P` and `h' : ¬P`). This avoids emitting
      `contradiction` for complex proof terms where it can't close the goal. -/
  private partial def tryDecompFalseType (expr : Expr) (lctx : LocalContext)
      (localInsts : LocalInstances) (used : List String) : TacticM (Option (Array (TSyntax `tactic) × List String)) := do
    withLCtx lctx localInsts do
      let exprTy ← Meta.inferType expr
      if !exprTy.isConstOf ``False then return none
      -- Check if the local context has an obvious contradiction
      let mut hasFalse := false
      let mut posHyps : Array Expr := #[]  -- hypotheses of type P
      let mut negHyps : Array Expr := #[]  -- hypotheses of type ¬P (inner P)
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty := decl.type
        if ty.isConstOf ``False then
          hasFalse := true
          break
        let (fn, args) := peelArgs ty
        if fn.isConstOf ``Not && args.length >= 1 then
          negHyps := negHyps.push args[0]!
        else if ty.isForall && !ty.isArrow then
          -- skip universals
          pure ()
        else if let .forallE _ dom body _ := ty then
          -- P → False is ¬P
          if body.isConstOf ``False then
            negHyps := negHyps.push dom
          else
            posHyps := posHyps.push ty
        else if !ty.isSort then
          posHyps := posHyps.push ty
      if hasFalse then
        let contradictionTac ← `(tactic| contradiction)
        return some (#[contradictionTac], used)
      -- Check for P/¬P pair
      for neg in negHyps do
        for pos in posHyps do
          if (← Meta.isDefEq pos neg) then
            let contradictionTac ← `(tactic| contradiction)
            return some (#[contradictionTac], used)
      return none

end

end LeanDecomp
