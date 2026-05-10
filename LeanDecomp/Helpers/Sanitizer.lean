import Lean

/-! # Inaccessible-name sanitizer

Replaces references to inaccessible (`name✝`) typeclass-instance fvars
in delab output with `inferInstance`.  Without this, decompiled scripts
that mention anonymous `[TypeClass]` binders fail cross-file
re-elaboration because `name✝` isn't a parseable identifier.

See README "Done: cross-file `inst✝` → `inferInstance` substitution"
for the full design rationale.
-/

namespace LeanDecomp
open Lean Elab Meta

/-- True iff `n` is the Name of an inaccessible binder — one Lean's
    pretty printer renders with the `✝` marker.  Two stored
    representations both qualify:
    1. **Macro scopes attached** (the common case): a hygienic name like
       `Lean.Name.num "inst" 12345` from `Macro.addMacroScope`.
       `Name.hasMacroScopes` detects these.
    2. **Literal `✝` in a component string**: rare, but happens when a
       name was constructed via the printer's renaming pass and re-fed
       into the elaborator.  Caught by the component-string check. -/
def isInaccessibleName (n : Name) : Bool :=
  n.hasMacroScopes ||
    n.components.any fun comp => comp.toString.contains '✝'

/-- Walk `stx` and replace identifier references that resolve to
    inaccessibly-named typeclass-instance fvars in `lctx` with
    `inferInstance`.  Cross-file re-elaboration of decompiled scripts
    fails on `refine @foo R inst✝ ...` and `exact inst✝¹` — the `✝`
    marks the ident as inaccessible.  Typeclass inference can re-fill
    these positions, so `inferInstance` works.

    Three-condition narrow trigger so we don't over-fire on hygienic
    but accessible binders:
    1. ident has macro scopes OR a literal `✝` component;
    2. the name resolves to an FVar in `lctx`;
    3. that FVar's type is a typeclass instance (`Meta.isClass?`).

    Uses `inferInstance` (not bare `_`) because `_` in tactic `exact`
    position becomes an unfilled term mvar (raises "internal exception
    #5" under `exact _`).  Also uses `mkIdent` (not quotation) so the
    substitute doesn't carry macro scopes that would re-sanitize as
    `inferInstance✝`. -/
def sanitizeInaccessibleIdents (lctx : LocalContext) (stx : Syntax) : MetaM Syntax := do
  let inferInst : Syntax := mkIdent ``inferInstance
  let isInaccessibleClassRef (name : Name) : MetaM Bool := do
    if !name.hasMacroScopes && !name.isInaccessibleUserName then return false
    let some decl := lctx.findFromUserName? name | return false
    return (← Meta.isClass? decl.type).isSome
  -- Walk down chained projections (`inst✝.foo.bar`) to find the
  -- receiver ident at the bottom.  Returns the bottom ident's name iff
  -- the chain is purely `.proj` nodes terminating in an ident.
  let rec projRoot : Syntax → Option Name
    | .node _ ``Lean.Parser.Term.proj #[receiver, _, _] => projRoot receiver
    | .ident _ _ name _ => some name
    | _ => none
  Meta.withLCtx lctx #[] do
    stx.replaceM fun s => do
      match s with
      -- Whole-projection replacement: `inst✝.toLE` → `inferInstance`.
      -- `inferInstance.toLE` would fail with "type class instance
      -- expected ?m" because Lean can't infer the type to synthesize
      -- for the bare `inferInstance` before descending into `.toLE`.
      -- Replacing the whole projection works because the projection's
      -- RESULT type is also a class.
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

end LeanDecomp
