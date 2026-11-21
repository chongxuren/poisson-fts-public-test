import PoissonDAG.Constructions.PORS.BucketRefinedRow

namespace PoissonDAG.PORS.BucketRefined

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem resources :
    p.bytes = 1492 ∧ p.signCeiling = 15333760 ∧
    p.verifyCeiling = 106 ∧ p.graphNodes = 11010047 ∧
    89 * 2^p.r ≤ 2^p.ctr * p.acceptedWords := by decide +kernel

theorem finite_moment :
    weightedCut p.rawEnvelope 1 40 +
      ((1 : ℚ)^40 / factorial 40) / (1 - 1 / (40+1 : ℚ)) ≤
      ((1 : ℚ)/2^128) * exponentialCut 1 4 := by
  simp only [weightedCut, exponentialCut]
  decide +kernel

end PoissonDAG.PORS.BucketRefined
