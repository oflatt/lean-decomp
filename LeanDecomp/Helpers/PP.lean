import Lean
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter

/-! # PrettyPrinter / delab wrappers

Helpers for emitting decompiled-source from Expr / Syntax.  All wrappers
lift PrettyPrinter truncation options so emitted source survives
re-elaboration — the default truncation markers (`⋯`) cannot be parsed
back as Lean source.

See README "Done: pre-flight `⋯` detection" and "Done: route all delab
through `delabRefinable` + lift `pp.maxSteps`" for the rationale.
-/

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter Tactic
open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax)

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

/-- Render an Expr as Term syntax via `Meta.ppExpr` + `Parser.runParserCategory`.
    `usePpAll` enables `pp.all` (fully-qualified names + explicit args).  `pp.maxSteps`
    is lifted to 1M because `pp.all` does not override it — large proofs hit the
    default 5000-step truncation and emit `⋯` even with `pp.all := true`. -/
def ppExprToTermSyntaxWith (e : Expr) (usePpAll : Bool) : MetaM Term :=
  withOptions (fun o =>
      let o := pp.coercions.types.set o true
      let o := pp.numericTypes.set o true
      let o := pp.maxSteps.set o 1000000
      if usePpAll then
        pp.all.set o true
      else
        o
    ) do
      ppExprToTermSyntax e

/-- Three PrettyPrinter options control terminal-source truncation; we
    lift all three for any rendering of generated source so emitted
    suggestions survive re-elaboration:
    - `pp.deepTerms := true` — disables depth-based subterm elision.
    - `pp.proofs := true` — disables Prop-typed-subterm elision.
    - `pp.maxSteps := 1000000` — disables the visited-counter elision. -/
def liftPPTruncationOptions (o : Lean.Options) : Lean.Options :=
  let o := pp.deepTerms.set o true
  let o := pp.proofs.set o true
  pp.maxSteps.set o 1000000

/-- `delabToRefinableSyntax` wrapper that disables PrettyPrinter
    truncation (all three paths — see `liftPPTruncationOptions`).  Use
    this everywhere we delab a proof term destined for emitted source. -/
def delabRefinable (e : Expr) : MetaM Term :=
  withOptions liftPPTruncationOptions (delabToRefinableSyntax e)

/-- `PrettyPrinter.ppTactic` wrapper that lifts the same truncation
    options as `delabRefinable`.  Use this everywhere we format a
    generated tactic seq for emission as a suggestion or for re-elab
    validation. -/
def ppTacticFull (stx : TSyntax `Lean.Parser.Tactic.tacticSeq) : CoreM Format :=
  withOptions liftPPTruncationOptions (PrettyPrinter.ppTactic ⟨stx⟩)

end LeanDecomp
