import PoissonDAG.V2.Model

/- Only the integration test grants eligibility as a hypothesis. The real judge
requires an unconditional certificate, so this fixture cannot rank. -/
private def sample : PoissonDAG.Scheme :=
  ⟨[.source], ⟨1, [.constant true], [0, 0, 0]⟩, 1⟩

theorem Submission.certificate : PoissonDAG.V2.Eligible sample →
    PoissonDAG.V2.ConstructionCertificate sample 17 :=
  fun h => ⟨h, by decide⟩
