import PoissonDAG.Constructions.PORS.SingleRefinedRow

namespace PoissonDAG.PORS.SingleRefined

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem resources :
    p.bytes = 1780 ∧ p.signCeiling = 16133231 ∧
    p.verifyCeiling = 121 ∧ p.graphNodes = 1474559 ∧
    89 * 2^p.r ≤ 2^p.ctr * p.acceptedWords := by decide +kernel

theorem finite_moment :
    weightedCut p.rawEnvelope 1 40 +
      ((1 : ℚ)^40 / factorial 40) / (1 - 1 / (40+1 : ℚ)) ≤
      ((1 : ℚ)/2^128) * exponentialCut 1 4 := by
  simp only [weightedCut, exponentialCut]
  decide +kernel

end PoissonDAG.PORS.SingleRefined
