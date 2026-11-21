import PoissonDAG.Constructions.PORS.FiniteCut

namespace PoissonDAG.FORS

/-- One shared Poisson count q; thinning is applied once to the raw target. -/
def rawCoefficient (a k g q : Nat) : ℚ :=
  (1 - (1 - 1 / (2:ℚ)^a)^q)^k / (2:ℚ)^g

def momentEnvelope (a k g q : Nat) : ℚ :=
  ((q:ℚ) * (1 / (2:ℚ)^a))^k / (2:ℚ)^g

private theorem unit_inv (a : Nat) : 1 / (2:ℚ)^a ≤ 1 := by
  apply (div_le_one (by positivity)).2
  exact one_le_pow₀ (by norm_num)

private theorem hit_bounds {x : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (q : Nat) :
    0 ≤ 1-(1-x)^q ∧ 1-(1-x)^q ≤ 1 :=
  ⟨sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith)),
   sub_le_self _ (pow_nonneg (by linarith) _)⟩

private theorem union_bound {x : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (q : Nat) :
    1-(1-x)^q ≤ (q:ℚ)*x := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hy : (1-x)^q ≤ 1 := sub_nonneg.mp (hit_bounds hx hx1 q).1
    have hxy := mul_le_mul_of_nonneg_right hy hx
    rw [pow_succ, Nat.cast_succ]
    nlinarith

theorem coefficient_poisson_of_moment_check (a k g : Nat)
    (hfinite : weightedCut (momentEnvelope a k g) 1 40 +
      ((1:ℚ)^40 / factorial 40) / (1 - 1/(40+1:ℚ)) ≤
      ((1:ℚ)/2^128) * exponentialCut 1 4) :
    PoissonLE (rawCoefficient a k g) ((1:ℚ)/2^128) := by
  have hx : 0 ≤ 1 / (2:ℚ)^a := by positivity
  have hu := unit_inv a
  apply PORS.poissonLE_of_forty_terms
  · intro q
    exact div_nonneg (pow_nonneg (hit_bounds hx hu q).1 _) (by positivity)
  · intro q
    apply (div_le_one (by positivity : 0 < (2:ℚ)^g)).2
    exact (pow_le_one₀ (hit_bounds hx hu q).1 (hit_bounds hx hu q).2).trans
      (one_le_pow₀ (by norm_num))
  · positivity
  · apply le_trans _ hfinite
    apply add_le_add _ le_rfl
    unfold weightedCut
    apply Finset.sum_le_sum
    intro q _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (hit_bounds hx hu q).1 (union_bound hx hu q) _) (by positivity)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem ordinary_poisson : PoissonLE (rawCoefficient 18 8 0) ((1:ℚ)/2^128) := by
  apply coefficient_poisson_of_moment_check
  simp only [weightedCut, exponentialCut]
  decide +kernel

theorem equal_width_poisson : PoissonLE (rawCoefficient 18 7 18) ((1:ℚ)/2^128) := by
  apply coefficient_poisson_of_moment_check
  simp only [weightedCut, exponentialCut]
  decide +kernel

theorem variable_width_poisson : PoissonLE (rawCoefficient 17 7 19) ((1:ℚ)/2^128) := by
  apply coefficient_poisson_of_moment_check
  simp only [weightedCut, exponentialCut]
  decide +kernel

end PoissonDAG.FORS
