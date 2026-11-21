import PoissonDAG.Probability.ExponentialCuts

/-! A rational finite-check bridge for the raw common-Poisson coefficients. -/
namespace PoissonDAG.PORS

theorem poissonLE_of_forty_terms {a : Nat → ℚ} {budget : ℚ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (hb : 0 ≤ budget)
    (hfinite : weightedCut a 1 40 +
      ((1 : ℚ)^40 / factorial 40) / (1 - 1 / (40 + 1 : ℚ)) ≤
      budget * exponentialCut 1 4) :
    PoissonLE a budget := by
  intro n m hm
  have htail := weightedCut_tail_le (c := a) ha0 ha1 (by norm_num : (0 : ℚ) ≤ 1)
    40 n (by norm_num)
  have hnorm := exponentialCut_le_expUpper 4 m hm
  calc
    partialSum a n = weightedCut a 1 n := by
      simp [partialSum_eq_sum, weightedCut, div_eq_mul_inv]
    _ ≤ _ := htail
    _ ≤ _ := hfinite
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hb

end PoissonDAG.PORS
