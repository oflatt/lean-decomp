import LeanDecomp.ProofTermMacro

namespace LeanDecomp

theorem sampleTheorem : 2 + 2 = 4 := by decide

showProofTerm sampleTheorem

theorem sampleGrind : ∀ n : Nat, 0 + n = n := by
  grind

theorem samplegrind : ∀ n : Nat, 0 + n = n := by
  grind

showProofTerm samplegrind

end LeanDecomp
