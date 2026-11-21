import PoissonDAG.Constructions.GRSCC.Authentication
import PoissonDAG.Constructions.GRSCC.MaskedCounts
import PoissonDAG.Constructions.GRSCC.SmallEnvelope
import PoissonDAG.Constructions.GRSCC.SmallNumerical

namespace PoissonDAG.GRSCC

/-- Precisely the twenty local supply inequalities in the smaller Poisson
argument. Keeping this hypothesis visible prevents an incomplete arithmetic
certificate from being entered as a challenge record. -/
theorem construction756_of_local_bounds
    (countBounds : ∀ m v : Nat, 2 ≤ m → m ≤ 6 → 0 < v → v ≤ m →
      localCover m v ≤ ((Small.caps[m]?.getD [])[v-1]?.getD 0 : Rat) / 1000000) :
    V2.ConstructionCertificate scheme 756 := by
  have covering := Small.poisson_bound_of_bounds
    (Small.localCover_le_localUpper_of_cases countBounds) Small.numerical_bound
  exact ⟨⟨⟨scheme_wellFormed, scheme_correct, scheme_failure_budget,
    scheme_signing_budget, scheme_verification_budget, covering⟩,
    scheme_authenticated⟩, scheme_size_budget⟩

end PoissonDAG.GRSCC
