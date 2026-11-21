import PoissonDAG.Constructions.PORS.ChainRefinedRow

namespace PoissonDAG.PORS.ChainRefined

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem resources :
    p.bytes = 1188 ∧ p.signCeiling = 9816603 ∧
    p.verifyCeiling = 219 ∧ p.graphNodes = 3440639 ∧
    89 * 2^p.r ≤ 2^p.ctr * p.acceptedWords := by decide +kernel

theorem finite_moment :
    weightedCut (p.simplexEnvelope coefs) 1 40 +
      ((1 : ℚ)^40 / factorial 40) / (1 - 1 / (40+1 : ℚ)) ≤
      ((1 : ℚ)/2^128) * exponentialCut 1 4 := by
  simp only [weightedCut, exponentialCut]
  decide +kernel

end PoissonDAG.PORS.ChainRefined
