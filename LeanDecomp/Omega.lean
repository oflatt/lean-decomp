import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter
import Lean.Elab.Tactic.Omega.Frontend
import LeanDecomp.Helpers
import LeanDecomp.CasesOn

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

/-- If `ty` is `¬P` or `P → False`, return `P`. -/
private def negatedProp? (ty : Expr) : Option Expr := do
  let (hd, args) := peelArgs ty
  if hd.isConstOf ``Not && args.length >= 1 then return args[0]!
  if ty.isArrow && ty.bindingBody!.isConstOf ``False then return ty.bindingDomain!
  failure

/-- Accumulated facts state for omega derivation. -/
private structure OmegaFactState where
  derivedFacts : Array (Expr × Expr × TSyntax `term) := #[]
  used : List String
  factNames : Array Name := #[]
  falseFactName? : Option Name := none

/-- Try to add a derived fact if it's clean and non-duplicate. -/
private def OmegaFactState.addFact (s : OmegaFactState)
    (proofExpr : Expr) (propType : Expr) (proofStx : TSyntax `term)
    : MetaM OmegaFactState := do
  if containsGrindInternals propType then return s
  let isDup ← s.derivedFacts.anyM fun x =>
    try Meta.isDefEq propType x.2.1 catch _ => pure false
  if isDup then return s
  let (n, used') := chooseIntroName s.used.length `fact s.used
  let newName := Name.mkSimple n
  let isFalse ← try (do let ty ← Meta.whnf propType; pure (ty.isConstOf ``False)) catch _ => pure false
  -- When the fact is a False proof, use the full delab of the proof expression so the
  -- have-statement re-elaborates correctly (the syntactic shorthand may not type-check as False).
  -- Skip if the proof expression itself contains grind internals (would produce unreadable syntax).
  let effectiveStx ← if isFalse then
    if containsGrindInternals proofExpr then return s
    else try delabToRefinableSyntax proofExpr catch _ => pure proofStx
  else
    pure proofStx
  -- Skip if the rendered syntax contains grind-internal identifiers.
  let stxStr := toString (← PrettyPrinter.ppTerm effectiveStx)
  if stxStr.contains "Int.Linear." || stxStr.contains "Lean.RArray."
      || stxStr.contains "Lean.Grind." || stxStr.contains "eagerReduce" then
    return s
  return {
    derivedFacts := s.derivedFacts.push (proofExpr, propType, effectiveStx)
    used := used'
    factNames := s.factNames.push newName
    falseFactName? := if isFalse then some newName else s.falseFactName?
  }

/-- Resolve an expression to its syntax name (context fvar or derived fact). -/
private def resolveFactStx (e : Expr) (hypNameMap : Std.HashMap FVarId Name)
    (s : OmegaFactState) : Option Ident :=
  if e.isFVar then hypNameMap.get? e.fvarId! |>.map mkIdent
  else (s.derivedFacts.findIdx? fun x => x.1 == e).bind fun idx =>
    s.factNames[idx]?.map mkIdent

/-- Find an already-derived fact name by proposition type. -/
private def findFactByType (s : OmegaFactState) (ty : Expr) : MetaM (Option Ident) := do
  for i in [:s.derivedFacts.size] do
    let (_, propTy, _) := s.derivedFacts[i]!
    if ← try Meta.isDefEq propTy ty catch _ => pure false then
      return some (mkIdent s.factNames[i]!)
  return none

/-- Try omega with just context hypotheses. -/
private def tryOmegaWithContext (goalType : Expr) (lctx : LocalContext) :
    MetaM Bool := do
  let mut ctxFacts : List Expr := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    ctxFacts := (.fvar decl.fvarId) :: ctxFacts
  try
    let mvar ← Meta.mkFreshExprMVar (some goalType) .syntheticOpaque
    Lean.Elab.Tactic.Omega.omega ctxFacts mvar.mvarId!
    return true
  catch _ => return false

/-- Strip chains of grind-generated `Eq.mp` casts around proof terms. -/
private partial def stripGrindCasts : Expr → Expr
  | e =>
    let (fn, args) := peelArgs e
    if fn.constName? == some ``Eq.mp && args.length >= 4 && containsGrindInternals args[2]! then
      stripGrindCasts args[3]!
    else e

/-- If `ty` reduces to `Iff lhs rhs`, return `(lhs, rhs)`. -/
private def iffSides? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← Meta.whnf ty
  let (hd, args) := peelArgs ty
  if hd.isConstOf ``Iff && args.length >= 2 then
    return some (args[0]!, args[1]!)
  return none

/-- Build a term syntax for applying an `Iff` proof to a hypothesis syntax.
    For inline `Iff.intro` proofs, simplify directly to the forward/backward function. -/
private def mkIffApplyStx (iffProof : Expr) (hypStx : TSyntax `term) (forward : Bool) : MetaM (TSyntax `term) := do
  let iffProof := stripGrindCasts iffProof
  let (fn, args) := peelArgs iffProof
  if fn.constName? == some ``Iff.intro && args.length >= 4 then
    let dirFn := if forward then args[2]! else args[3]!
    let dirFnStx ← delabToRefinableSyntax dirFn
    `($dirFnStx $hypStx)
  else
    let iffStx ← delabToRefinableSyntax iffProof
    if forward then
      `($(mkIdent ``Iff.mp) $iffStx $hypStx)
    else
      `($(mkIdent ``Iff.mpr) $iffStx $hypStx)

/-- Walk a proof term and extract clean-typed intermediate facts for omega.
    This is a fact extraction pass, not a decompiler — it linearizes the proof tree
    into `have` statements that enrich omega's context. -/
private partial def walkProofForFacts (e : Expr) (hypNameMap : Std.HashMap FVarId Name)
    (s0 : OmegaFactState) : MetaM (Option Ident × OmegaFactState) := do
  let e := stripGrindCasts e
  if e.isFVar then
    return (hypNameMap.get? e.fvarId! |>.map mkIdent, s0)

  let (fn, args) : Expr × List Expr := peelArgs e
  let mut s := s0
  for arg in args do
    let (_, s') ← walkProofForFacts arg hypNameMap s
    s := s'

  let cname := fn.constName?

  if cname == some ``Iff.mp && args.length >= 4 then
    let iffProof := stripGrindCasts args[2]!
    let hypProof := stripGrindCasts args[3]!
    let hypStx : TSyntax `term ←
      if let some h := resolveFactStx hypProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax hypProof
    let some (_, rhs) ← iffSides? (← Meta.inferType iffProof) | return (none, s)
    let mpStx ← mkIffApplyStx iffProof hypStx true
    let prevSize := s.derivedFacts.size
    s ← s.addFact e rhs mpStx
    let mut curName? : Option Ident := none
    if s.derivedFacts.size > prevSize then
      let parentIdx := s.derivedFacts.size - 1
      let parentStx := mkIdent s.factNames[parentIdx]!
      curName? := some parentStx
      let (andFn, andArgs) := peelArgs rhs
      if andFn.isConstOf ``And && andArgs.length >= 2 then
        let p := andArgs[0]!
        let q := andArgs[1]!
        s ← s.addFact (mkApp3 (mkConst ``And.left) p q e) p (← `(($parentStx).1))
        s ← s.addFact (mkApp3 (mkConst ``And.right) p q e) q (← `(($parentStx).2))
    else
      curName? ← findFactByType s rhs
    return (curName?, s)

  if cname == some ``Iff.mpr && args.length >= 4 then
    let iffProof := stripGrindCasts args[2]!
    let hypProof := stripGrindCasts args[3]!
    let hypStx : TSyntax `term ←
      if let some h := resolveFactStx hypProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax hypProof
    let some (lhs, _) ← iffSides? (← Meta.inferType iffProof) | return (none, s)
    let mprStx ← mkIffApplyStx iffProof hypStx false
    let prevSize := s.derivedFacts.size
    s ← s.addFact e lhs mprStx
    if s.derivedFacts.size > prevSize then
      return (some (mkIdent s.factNames.back!), s)
    return (← findFactByType s lhs, s)

  if cname == some ``mt && args.length >= 4 then
    let fnProof := stripGrindCasts args[2]!
    let hypProof := stripGrindCasts args[3]!
    let hypStx : TSyntax `term ←
      if let some h := resolveFactStx hypProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax hypProof
    let fnStx ← delabToRefinableSyntax fnProof
    let mtTy ← try Meta.inferType e catch _ => return (none, s)
    let mtStx ← `($(mkIdent ``mt) $fnStx $hypStx)
    let prevSize := s.derivedFacts.size
    s ← s.addFact e mtTy mtStx
    if s.derivedFacts.size > prevSize then
      return (some (mkIdent s.factNames.back!), s)
    return (← findFactByType s mtTy, s)

  if (cname == some ``And.left || cname == some ``And.right) && args.length >= 3 then
    let pairProof := stripGrindCasts args[2]!
    let pairStx : TSyntax `term ←
      if let some h := resolveFactStx pairProof hypNameMap s then
        `($h:ident)
      else
        delabToRefinableSyntax pairProof
    let projTy ← try Meta.inferType e catch _ => return (none, s)
    let projStx ← if cname == some ``And.left then
      `(($pairStx).1)
    else
      `(($pairStx).2)
    let prevSize := s.derivedFacts.size
    s ← s.addFact e projTy projStx
    if s.derivedFacts.size > prevSize then
      return (some (mkIdent s.factNames.back!), s)
    return (← findFactByType s projTy, s)

  return (resolveFactStx e hypNameMap s, s)

/-- Collect every `|x|` subexpression (integer absolute value) from `e`.
    In Mathlib `|x|` elaborates to `_root_.abs.{0} α [Lattice α] [AddGroup α] x`
    (head `abs`, four args). In core Lean it's `@Abs.abs α _ x` (head `Abs.abs`,
    three args). We match both forms. -/
private partial def collectIntAbsArgs (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let mut acc := acc
  let (fn, args) := peelArgs e
  let xArg? : Option Expr :=
    if fn.isConstOf `abs && args.length == 4 then some args[3]!
    else if fn.isConstOf `Abs.abs && args.length == 3 then some args[2]!
    else none
  if let some x := xArg? then
    let xTy ← try Meta.inferType x catch _ => pure (mkConst `_unknown)
    if xTy.isConstOf ``Int then
      let alreadyIn ← acc.anyM fun a => try Meta.isDefEq a x catch _ => pure false
      if !alreadyIn then acc := acc.push x
  for a in args do
    acc ← collectIntAbsArgs a acc
  return acc

/-- For each unique `|x|` (with `x : ℤ`) in the goal or context types, inject
    `have fact := Int.abs_eq_natAbs x`. `Int.abs_eq_natAbs` is a Mathlib lemma;
    we reference it by name so this module doesn't need to import Mathlib. -/
private def addAbsNatAbsFacts (goalType : Expr) (ctxHyps : Array (Expr × Expr))
    (s : OmegaFactState) : MetaM OmegaFactState := do
  let absEqNatAbs : Name := `Int.abs_eq_natAbs
  unless (← getEnv).contains absEqNatAbs do return s
  let mut xs : Array Expr := #[]
  xs ← collectIntAbsArgs goalType xs
  for (_, hypTy) in ctxHyps do
    xs ← collectIntAbsArgs hypTy xs
  let mut s := s
  for x in xs do
    let factExpr := mkApp (mkConst absEqNatAbs) x
    let factTy ← try Meta.inferType factExpr catch _ => continue
    let factStx ← try delabToRefinableSyntax factExpr catch _ => continue
    s ← s.addFact factExpr factTy factStx
  return s

  private partial def eraseMacroScopesSyntax (stx : Syntax) : Syntax :=
    match stx with
    | Syntax.ident _ _ val _ =>
      mkIdent val.eraseMacroScopes
    | Syntax.node info kind args =>
      Syntax.node info kind (args.map eraseMacroScopesSyntax)
    | _ => stx

/-- Try replacing grind-internal proof terms with `omega`.
    Extracts facts directly from the low-level proof term structure,
    then tries `omega` with those explicit facts. -/
partial def tryDecompOmega (expr : Expr) (lctx : LocalContext)
    (localInsts : LocalInstances) (used : List String)
    (decompile : Expr → LocalContext → LocalInstances → List String → MetaM (Array (TSyntax `tactic) × List String))
    : MetaM (Option (Array (TSyntax `tactic) × List String)) := do
  if !containsGrindInternals expr then return none
  withLCtx lctx localInsts do
    let goalType ← Meta.inferType expr
    -- Context hypotheses and name map
    let mut ctxHyps : Array (Expr × Expr) := #[]
    let mut hypNameMap : Std.HashMap FVarId Name := {}
    for decl in lctx do
      if decl.isImplementationDetail then continue
      ctxHyps := ctxHyps.push (.fvar decl.fvarId, decl.type)
      hypNameMap := hypNameMap.insert decl.fvarId decl.userName
    let mut s : OmegaFactState := { used }
    -- Collect abs terms to decide if we should simplify before omega.
    let mut absArgs : Array Expr := #[]
    absArgs ← collectIntAbsArgs goalType absArgs
    for (_, hypTy) in ctxHyps do
      absArgs ← collectIntAbsArgs hypTy absArgs
    let hasAbs := !absArgs.isEmpty
    if hasAbs then
      let absArg := absArgs[0]!
      let absStx0 ← withOptions (fun opts =>
          (opts.setBool `pp.coercions.types true).setBool `pp.numericTypes true
        ) <| delabToRefinableSyntax absArg
      let absStx ← `(term| ($absStx0 : Int))
      let splitTac ← `(tactic|
        cases (le_total $absStx 0) with
        | inl h =>
            rw [abs_of_nonpos h] at hp
            omega
        | inr h =>
            rw [abs_of_nonneg h] at hp
            omega
      )
      let splitTac := TSyntax.mk (eraseMacroScopesSyntax splitTac.raw)
      return some (#[splitTac], used)
    -- Inject `Int.abs_eq_natAbs x` for each unique `|x| : ℤ` in goal and
    -- context types. Omega can't reason through integer `|·|` on its own, so
    -- this equality (`|x| = x.natAbs`) is the minimum needed to close abs goals.
    s ← addAbsNatAbsFacts goalType ctxHyps s
    -- Shortcut to a bare `omega` only when no abs facts are needed AND omega
    -- already closes on just the context. Otherwise we must emit the `have`
    -- statements so the re-elaborated tactic has access to them.
    if s.derivedFacts.isEmpty && (← tryOmegaWithContext goalType lctx) then
      return some (#[← `(tactic| omega)], used)
    let (_, s') ← walkProofForFacts expr hypNameMap s
    s := s'
    -- Single specialization pass for ∀-quantified context hypotheses.
    for (hypExpr, hypTy) in ctxHyps do
      if !hypTy.isForall then continue
      let some hypName := hypNameMap.get? hypExpr.fvarId! | continue
      let derivedPairs := s.derivedFacts.map fun x => (x.1, x.2.1)
      for (valExpr, valTy) in ctxHyps ++ derivedPairs do
        if valTy.isForall then continue
        if ← try Meta.isProp valTy catch _ => pure true then continue
        let some valStx := resolveFactStx valExpr hypNameMap s | continue
        let specialized := mkApp hypExpr valExpr
        let specializedTy ← try Meta.inferType specialized catch _ => continue
        let mut cur := specialized
        let mut curTy := specializedTy
        let mut curStx ← `($(mkIdent hypName) $valStx)
        for _ in [:5] do
          if !curTy.isArrow then break
          let dom := curTy.bindingDomain!
          let mut applied := false
          let derivedPairs' := s.derivedFacts.map fun x => (x.1, x.2.1)
          for (argExpr, argTy) in derivedPairs' ++ ctxHyps do
            if ← try Meta.isDefEq argTy dom catch _ => pure false then
              let some argStx := resolveFactStx argExpr hypNameMap s | break
              cur := mkApp cur argExpr
              curTy ← try Meta.inferType cur catch _ => break
              curStx ← `($curStx $argStx)
              applied := true; break
          if !applied then break
        if (← try Meta.isProp curTy catch _ => pure false) && !curTy.isForall then
          s ← s.addFact cur curTy curStx
    -- Emit have statements and close.
    let mut haveTacs : Array (TSyntax `tactic) := #[]
    for i in [:s.derivedFacts.size] do
      let (proofExpr, propTy, proofStx) := s.derivedFacts[i]!
      let factIdent := mkIdent s.factNames[i]!
      let haveTac ←
        if containsGrindInternals proofExpr then
          `(tactic| have $factIdent := $proofStx)
        else
          try
            let tyStx ← delabToRefinableSyntax propTy
            let (factTacs, _) ← decompile proofExpr lctx localInsts []
            let factSeq ← `(Lean.Parser.Tactic.tacticSeq| $[$factTacs]*)
            `(tactic| have $factIdent : $tyStx := by $factSeq)
          catch _ =>
            `(tactic| have $factIdent := $proofStx)
      haveTacs := haveTacs.push haveTac
    let closingTacs ← match s.falseFactName? with
      | some n => do
          let falseElim := Lean.mkCIdent ``False.elim
          pure #[← `(tactic| exact $falseElim $(mkIdent n))]
      | none   => do
          -- Try interval membership closing: exact factI (Iff.mpr mem_X ⟨by omega, by omega⟩)
          -- This handles the common pattern where a negation fact ¬(x ∈ Ioc a b) blocks omega.
          let mut memberClosing? : Option (TSyntax `tactic) := none
          for i in [:s.derivedFacts.size] do
            if memberClosing?.isSome then break
            let (factExpr, factTy, _) := s.derivedFacts[i]!
            if negatedProp? factTy |>.isNone then continue
            for memLemma in [`Finset.mem_Ioc, `Finset.mem_Ico, `Finset.mem_Icc, `Finset.mem_Ioo,
                             `Set.mem_Ioc, `Set.mem_Ico, `Set.mem_Icc, `Set.mem_Ioo] do
              let matched ← try
                  let iffConst ← Meta.mkConstWithFreshMVarLevels memLemma
                  let iffTy ← Meta.inferType iffConst
                  let (mvars, _, _) ← Meta.forallMetaTelescope iffTy
                  let iffApplied := mkAppN iffConst mvars
                  let mprExpr ← Meta.mkAppM ``Iff.mpr #[iffApplied]
                  let fTy ← Meta.inferType mprExpr
                  let B := fTy.bindingBody!
                  let factExprTy ← Meta.inferType factExpr
                  let notB := mkApp (mkConst ``Not) B
                  guard (← Meta.isDefEq factExprTy notB)
                  pure true
              catch _ => pure false
              if !matched then continue
              let factIdent := mkIdent s.factNames[i]!
              let lemmaIdent := mkIdent memLemma
              let iffMpr := mkIdent ``Iff.mpr
              memberClosing? := some (← `(tactic| exact $factIdent ($iffMpr $lemmaIdent ⟨by omega, by omega⟩)))
              break
          match memberClosing? with
          | some stx => pure #[stx]
          | none =>
              pure #[← `(tactic| omega)]
    return some (haveTacs ++ closingTacs, s.used)

end LeanDecomp
