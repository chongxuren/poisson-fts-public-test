import PoissonDAG.Constructions.GRSCC.Circuit
import PoissonDAG.V2.Model

namespace PoissonDAG.GRSCC

/-- The two remaining obligations for a ranked 756-byte construction. -/
theorem certificate_of_covering_and_authentication
    (covering : PoissonLE scheme.coverCoefficient ((1 : Rat) / 2^128))
    (authentication : ∀ raw ∈ scheme.accepted,
      V2.Authenticated scheme.graph (scheme.frontier raw) (scheme.plan raw)) :
    V2.ConstructionCertificate scheme 756 :=
  ⟨⟨⟨scheme_wellFormed, scheme_correct, scheme_failure_budget, scheme_signing_budget,
      scheme_verification_budget, covering⟩, authentication⟩, scheme_size_budget⟩

end PoissonDAG.GRSCC
