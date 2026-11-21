import PoissonDAG.Probability.ExponentialCuts
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum

/-! # Finite binomial thinning under exact Poisson cuts -/

namespace PoissonDAG

open scoped BigOperators

theorem choose_factorial_ratio (n i : Nat) (hi : i ≤ n) :
    (n.choose i : ℚ) / (factorial n : ℚ) =
      1 / ((factorial i : ℚ) * (factorial (n - i) : ℚ)) := by
  have hf (k : Nat) : (factorial k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (factorial_pos k)
  apply (div_eq_div_iff (hf n) (mul_ne_zero (hf i) (hf (n - i)))).2
  have h : (n.choose i : ℚ) * (factorial i : ℚ) * (factorial (n - i) : ℚ) =
      (factorial n : ℚ) := by
    simp only [factorial_eq_nat_factorial]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  simpa [mul_assoc] using h

theorem exponential_add_term (a b : ℚ) (n : Nat) :
    (a + b) ^ n / (factorial n : ℚ) =
      ∑ i ∈ Finset.range (n + 1),
        (a ^ i / (factorial i : ℚ)) * (b ^ (n - i) / (factorial (n - i) : ℚ)) := by
  rw [add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hratio := choose_factorial_ratio n i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  calc
    _ = (a ^ i * b ^ (n - i)) * ((n.choose i : ℚ) / (factorial n : ℚ)) := by ring
    _ = _ := by rw [hratio]; ring

theorem exponentialCut_product_le {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n k : Nat) :
    exponentialCut a n * exponentialCut b k ≤ exponentialCut (a + b) (n + k) := by
  have hnonneg (i j : Nat) :
      0 ≤ (a ^ i / (factorial i : ℚ)) * (b ^ j / (factorial j : ℚ)) := by positivity
  have htriangle : exponentialCut (a + b) (n + k) =
      ∑ i ∈ Finset.range (n + k), ∑ j ∈ Finset.range (n + k - i),
        (a ^ i / (factorial i : ℚ)) * (b ^ j / (factorial j : ℚ)) := by
    unfold exponentialCut
    simp_rw [exponential_add_term]
    exact Finset.sum_range_diag_flip (n + k)
      (fun i j => (a ^ i / (factorial i : ℚ)) * (b ^ j / (factorial j : ℚ)))
  rw [htriangle, exponentialCut, exponentialCut, Finset.sum_mul_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + k - i),
        (a ^ i / (factorial i : ℚ)) * (b ^ j / (factorial j : ℚ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by
        have := Finset.mem_range.mp hi
        omega))
      intro j hj hnot
      exact hnonneg i j
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : n ≤ n + k))
      intro i hi hnot
      exact Finset.sum_nonneg (fun j _ => hnonneg i j)

def binomialTransform (p : ℚ) (c : Nat → ℚ) (q : Nat) : ℚ :=
  ∑ j ∈ Finset.range (q + 1),
    (q.choose j : ℚ) * p ^ j * (1 - p) ^ (q - j) * c j

theorem binomial_partialSum_le {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {c : Nat → ℚ} (hc : ∀ i, 0 ≤ c i) (n : Nat) :
    partialSum (binomialTransform p c) n ≤
      weightedCut c p n * exponentialCut (1 - p) n := by
  have hpbase : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hnonneg (i j : Nat) :
      0 ≤ (c i * (p ^ i / (factorial i : ℚ))) *
        ((1 - p) ^ j / (factorial j : ℚ)) := by
    exact mul_nonneg (mul_nonneg (hc i) (by positivity)) (by positivity)
  have hterm (q j : Nat) (hj : j < q + 1) :
      ((q.choose j : ℚ) * p ^ j * (1 - p) ^ (q - j) * c j) / (factorial q : ℚ) =
        (c j * (p ^ j / (factorial j : ℚ))) *
          ((1 - p) ^ (q - j) / (factorial (q - j) : ℚ)) := by
    have hratio := choose_factorial_ratio q j (by omega)
    calc
      _ = (c j * p ^ j * (1 - p) ^ (q - j)) *
          ((q.choose j : ℚ) / (factorial q : ℚ)) := by ring
      _ = _ := by rw [hratio]; ring
  have heq : partialSum (binomialTransform p c) n =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i),
        (c i * (p ^ i / (factorial i : ℚ))) *
          ((1 - p) ^ j / (factorial j : ℚ)) := by
    rw [partialSum_eq_sum]
    unfold binomialTransform
    simp_rw [Finset.sum_div]
    calc
      _ = ∑ q ∈ Finset.range n, ∑ j ∈ Finset.range (q + 1),
          (c j * (p ^ j / (factorial j : ℚ))) *
            ((1 - p) ^ (q - j) / (factorial (q - j) : ℚ)) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact Finset.sum_congr rfl (fun j hj => hterm q j (Finset.mem_range.mp hj))
      _ = _ := Finset.sum_range_diag_flip n (fun i j =>
        (c i * (p ^ i / (factorial i : ℚ))) * ((1 - p) ^ j / (factorial j : ℚ)))
  rw [heq, weightedCut, exponentialCut, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _))
  intro j hj hnot
  exact hnonneg i j

end PoissonDAG
