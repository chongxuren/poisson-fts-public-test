import PoissonDAG.Constructions.GRSCC.Circuit
import PoissonDAG.V2.Model

-- This regression fixture has an eligibility hypothesis and must fail the live goal.
theorem Submission.certificate : PoissonDAG.V2.Eligible PoissonDAG.GRSCC.scheme →
    PoissonDAG.V2.ConstructionCertificate PoissonDAG.GRSCC.scheme 756 :=
  fun h => ⟨h, PoissonDAG.GRSCC.scheme_size_budget⟩
