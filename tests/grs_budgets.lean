import PoissonDAG.Constructions.GRSCC.Reference

open PoissonDAG.GRSCC

/-- Unconditional properties of the fixed organizer implementation. -/
theorem Submission.certificate :
    scheme.WellFormed ∧ scheme.Correct ∧ scheme.size ≤ 756 ∧
    scheme.signCost ≤ 2^24 ∧ scheme.verifyCost ≤ 512 ∧
    scheme.failure ≤ (1 : Rat) / 2^128 :=
  ⟨scheme_wellFormed, scheme_correct, scheme_size_budget, scheme_signing_budget,
    scheme_verification_budget, scheme_failure_budget⟩
