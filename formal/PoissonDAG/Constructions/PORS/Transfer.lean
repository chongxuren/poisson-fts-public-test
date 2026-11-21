import PoissonDAG.Constructions.PORS.RowModel
import PoissonDAG.Probability.Counting

namespace PoissonDAG.PORS

/-- Converts a bound on the judge's history coefficients and the finite numeric
row check into the literal all-cuts statement. The mathematical coefficient
comparison remains an explicit obligation for the instantiated circuit. -/
theorem covering_of_envelope (s : Scheme) (bound : Nat → ℚ)
    (coeff : ∀ q, s.coverCoefficient q ≤ bound q)
    (unit : ∀ q, bound q ≤ 1)
    (finite : weightedCut bound 1 40 +
      ((1 : ℚ)^40 / factorial 40) / (1 - 1 / (40+1 : ℚ)) ≤
      ((1 : ℚ)/2^128) * exponentialCut 1 4) :
    PoissonLE s.coverCoefficient ((1 : ℚ)/2^128) := by
  apply poissonLE_of_forty_terms (coverCoefficient_nonneg s)
    (fun q => (coeff q).trans (unit q)) (by norm_num)
  apply le_trans _ finite
  apply add_le_add _ le_rfl
  unfold weightedCut
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (coeff i) (by positivity)

theorem rawEnvelope_le_one (p : Row) (size : p.acceptedWords ≤ 2^p.r) (q : Nat) :
    p.rawEnvelope q ≤ 1 := by
  unfold Row.rawEnvelope
  apply le_trans (min_le_left _ _)
  apply (div_le_one (by positivity)).2
  exact_mod_cast size

end PoissonDAG.PORS
