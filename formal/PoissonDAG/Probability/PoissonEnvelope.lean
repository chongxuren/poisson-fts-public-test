import PoissonDAG.Probability.Thinning

/-! # A finite, rational certificate for the unbounded Poisson law

`cutoff` bounds the computed coefficients; every later coefficient is covered
by the geometric tail. `normalizer` is a lower exponential polynomial, not a
replacement probability distribution. Raw target acceptance appears once.
-/

namespace PoissonDAG

theorem exponentialCut_nonneg {x : ℚ} (hx : 0 ≤ x) (n : Nat) :
    0 ≤ exponentialCut x n := by
  unfold exponentialCut
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))

theorem partialSum_le_scaled {a b : Nat → ℚ} {scale : ℚ}
    (hab : ∀ i, a i ≤ scale * b i) (n : Nat) :
    partialSum a n ≤ scale * partialSum b n := by
  rw [partialSum_eq_sum, partialSum_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa [mul_div_assoc] using
    div_le_div_of_nonneg_right (hab i) (Nat.cast_nonneg (factorial i))

def poissonTail (p : ℚ) (cutoff : Nat) : ℚ :=
  (p ^ cutoff / (factorial cutoff : ℚ)) / (1 - p / (cutoff + 1 : ℚ))

theorem poissonLE_of_thinning_envelope {a c : Nat → ℚ} {p scale budget : ℚ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hscale : 0 ≤ scale) (hbudget : 0 ≤ budget)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hcoeff : ∀ q, a q ≤ scale * binomialTransform p c q)
    (cutoff normalizer : Nat) (hratio : p / (cutoff + 1 : ℚ) < 1)
    (hbound : scale * (weightedCut c p cutoff + poissonTail p cutoff) ≤
      budget * exponentialCut p normalizer) : PoissonLE a budget := by
  intro n m hm
  have hE := exponentialCut_nonneg (sub_nonneg.mpr hp1) n
  have htail := weightedCut_tail_le hc0 hc1 hp0 cutoff n hratio
  have hproduct : exponentialCut (1 - p) n * exponentialCut p normalizer ≤ expUpper m := by
    calc
      _ ≤ exponentialCut ((1 - p) + p) (n + normalizer) :=
        exponentialCut_product_le (sub_nonneg.mpr hp1) hp0 n normalizer
      _ = exponentialCut 1 (n + normalizer) := by congr 1; ring
      _ ≤ expUpper m := exponentialCut_le_expUpper _ _ hm
  calc
    partialSum a n ≤ scale * partialSum (binomialTransform p c) n := partialSum_le_scaled hcoeff n
    _ ≤ scale * (weightedCut c p n * exponentialCut (1 - p) n) :=
      mul_le_mul_of_nonneg_left (binomial_partialSum_le hp0 hp1 hc0 n) hscale
    _ ≤ scale * ((weightedCut c p cutoff + poissonTail p cutoff) * exponentialCut (1 - p) n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htail hE) hscale
    _ = (scale * (weightedCut c p cutoff + poissonTail p cutoff)) * exponentialCut (1 - p) n := by ring
    _ ≤ (budget * exponentialCut p normalizer) * exponentialCut (1 - p) n :=
      mul_le_mul_of_nonneg_right hbound hE
    _ = budget * (exponentialCut (1 - p) n * exponentialCut p normalizer) := by ring
    _ ≤ budget * expUpper m := mul_le_mul_of_nonneg_left hproduct hbudget

end PoissonDAG
