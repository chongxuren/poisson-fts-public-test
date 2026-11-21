import PoissonDAG.Probability.Counting

/-! # Consequences of the exact Poisson rational-cut definition

The lower-bound proof only needs the event with one historical disclosure. This
avoids replacing the unbounded law with any sampled or truncated distribution.
-/

namespace PoissonDAG

theorem expUpper_three_lt_three : expUpper 3 < (3 : ℚ) := by
  norm_num [expUpper, partialSum, List.range_succ, factorial]

theorem partialSum_two (a : Nat → ℚ) : partialSum a 2 = a 0 + a 1 := by
  simp [partialSum, List.range_succ, factorial]

theorem poisson_one_coefficient_lt {a : Nat → ℚ} {budget : ℚ}
    (hnonneg : 0 ≤ a 0) (hbudget : 0 < budget) (h : PoissonLE a budget) :
    a 1 < 3 * budget := by
  have hc := h 2 3 (by omega)
  rw [partialSum_two] at hc
  have he := expUpper_three_lt_three
  nlinarith

theorem eligible_one_history_upper {s : Scheme} (he : s.Eligible) :
    s.coverCoefficient 1 < 3 * ((1 : ℚ) / 2^128) := by
  exact poisson_one_coefficient_lt (coverCoefficient_nonneg s 0) (by positivity)
    he.2.2.2.2.2

end PoissonDAG
