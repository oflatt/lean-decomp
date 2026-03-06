import Lean
import Lean.PrettyPrinter

namespace LeanDecomp
open Lean Elab Meta PrettyPrinter

/-- Type alias for the decompileExpr callback to avoid repetition -/
abbrev DecompileCallback := Expr → LocalContext → LocalInstances → List String →
    MetaM (Array (TSyntax `tactic) × List String)

/-- Type alias for the assignIntroNames callback -/
abbrev AssignIntroNamesCallback := Array Expr → List String →
    MetaM (List String × LocalContext × List String)

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

def chooseIntroName (idx : Nat) (userName : Name) (used : List String) : (String × List String) :=
  let base := binderBaseName idx userName
  let introName := mkUniqueName base used
  (introName, introName :: used)

def assignIntroNames (xs : Array Expr) (used0 : List String) : MetaM (List String × LocalContext × List String) := do
  let mut used : List String := used0
  let mut idx := 0
  let mut names : List String := []
  let mut lctx ← getLCtx
  for x in xs do
    let some fvarId := x.fvarId?
      | throwError "Unexpected non-fvar binder in proof term"
    let decl ← fvarId.getDecl
    let (introName, used') := chooseIntroName idx decl.userName used
    used := used'
    names := introName :: names
    let newName := Name.mkSimple introName
    lctx := lctx.setUserName fvarId newName
    idx := idx + 1
  return (names.reverse, lctx, used)

/-- Convert intro names to identifier syntax -/
def namesToIdents (names : List String) : Array Ident :=
  names.toArray.map (fun n => mkIdent (Name.mkSimple n))

end LeanDecomp
