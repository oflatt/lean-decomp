import LeanDecomp.ProofTermMacro
import Lean.Elab.GuardMsgs

namespace LeanDecomp.SimpleTest


inductive Stmt : Type where
  | skip : Stmt
  | other : Stmt

deriving instance BEq for LeanDecomp.SimpleTest.Stmt

-- Test: decompile on a `cases h : s` proof with generalized equations.
-- The casesOn handler strips the Eq.ndrec transport wrappers, allowing
-- the branch bodies to re-elaborate correctly under `cases h : s with`.
/--
info: Try this:
  [apply] cases h : s with
      | skip => decide
      | other => decide
-/
#guard_msgs in
example (s: Stmt) : (s == Stmt.skip) || (s == Stmt.other) := by
  decompile
    cases h: s with
    | skip =>
      exact of_decide_eq_true (id (Eq.refl true))
    | other =>
      exact of_decide_eq_true (id (Eq.refl true))


-- Direct proof term for reference (this works fine)
example (s: Stmt) : (s == Stmt.skip) || (s == Stmt.other) := by
  let motive := fun t => s = t → (s == Stmt.skip || s == Stmt.other) = true
  exact
    Stmt.casesOn (motive := motive) s
      (fun h => (Eq.symm h ▸ of_decide_eq_true (id (Eq.refl true))))
      (fun h => Eq.symm h ▸ of_decide_eq_true (id (Eq.refl true))) (Eq.refl s)



end LeanDecomp.SimpleTest
