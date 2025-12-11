import LeanDecomp.ProofTermMacro

namespace LeanDecomp

theorem sampleTheorem : 2 + 2 = 4 := by decide

showProofTerm sampleTheorem

theorem samplegrind : ∀ n : Nat, 0 + n = n := by
  grind

showProofTerm samplegrind


#print samplegrind._proof_1_1

end LeanDecomp
