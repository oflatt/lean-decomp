import LeanDecomp.ProofTermMacro
import Lean.Elab.GuardMsgs

namespace LeanDecomp.BigStepTest


inductive Stmt : Type where
  | skip : Stmt
  | other : Stmt

deriving instance BEq for LeanDecomp.BigStepTest.Stmt


example (s: Stmt) : (s == Stmt.skip) || (s == Stmt.other) := by
  decompile
    cases h: s with
    | skip =>
      exact of_decide_eq_true (id (Eq.refl true))
    | other =>
      exact of_decide_eq_true (id (Eq.refl true))


example (s: Stmt) : (s == Stmt.skip) || (s == Stmt.other) := by
  let motive := fun t => s = t → (s == Stmt.skip || s == Stmt.other) = true
  exact
    Stmt.casesOn (motive := motive) s
      (fun h => (Eq.symm h ▸ of_decide_eq_true (id (Eq.refl true))))
      (fun h => Eq.symm h ▸ of_decide_eq_true (id (Eq.refl true))) (Eq.refl s)



end LeanDecomp.BigStepTest
