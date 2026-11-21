import PoissonDAG.Constructions.GRSCC.Certification
import PoissonDAG.Constructions.GRSCC.TwoSame

open PoissonDAG PoissonDAG.GRSCC

/-- The other nineteen local covering inequalities remain open. -/
theorem Submission.certificate
    (remaining : ∀ m v : Nat, 2 ≤ m → m ≤ 6 → 0 < v → v ≤ m →
      ¬ (m = 2 ∧ v = 2) →
      localCover m v ≤ ((Small.caps[m]?.getD [])[v-1]?.getD 0 : Rat) / 1000000) :
    V2.ConstructionCertificate scheme 756 := by
  apply construction756_of_local_bounds
  intro m v hm hM hv hV
  by_cases same : m = 2 ∧ v = 2
  · obtain ⟨rfl, rfl⟩ := same
    exact TwoSame.local_two_same
  · exact remaining m v hm hM hv hV same
