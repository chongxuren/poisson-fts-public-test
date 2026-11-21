import PoissonDAG.Probability.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-! # Rational exponential cuts and geometric tails

All statements quantify over arbitrary finite cuts. No tail is discarded and
no real infinite-sum default is used in the certificates.
-/

namespace PoissonDAG

open scoped BigOperators

theorem factorial_eq_nat_factorial (n : Nat) : factorial n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factorial, Nat.factorial_succ, ih, Nat.mul_comm]

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  rw [factorial_eq_nat_factorial]
  exact Nat.factorial_pos n

def exponentialCut (x : ℚ) (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ i / (factorial i : ℚ)

def weightedCut (c : Nat → ℚ) (x : ℚ) (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, c i * (x ^ i / (factorial i : ℚ))

def geometricCut (x : ℚ) (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ i

theorem geometricCut_identity (x : ℚ) (n : Nat) :
    geometricCut x n * (1 - x) = 1 - x ^ n := by
  induction n with
  | zero => simp [geometricCut]
  | succ n ih =>
      simp only [geometricCut, Finset.sum_range_succ, pow_succ] at *
      nlinarith

theorem geometricCut_le_inverse {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : Nat) :
    geometricCut x n ≤ 1 / (1 - x) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - x)).2
  have h := geometricCut_identity x n
  have hp := pow_nonneg hx0 n
  linarith

theorem factorial_offset_lower (m j : Nat) :
    factorial m * (m + 1) ^ j ≤ factorial (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        factorial m * (m + 1) ^ (j + 1) = (m + 1) *
            (factorial m * (m + 1) ^ j) := by ring
        _ ≤ (m + j + 1) * factorial (m + j) := Nat.mul_le_mul (by omega) ih
        _ = factorial (m + (j + 1)) := by
          rw [show m + (j + 1) = (m + j) + 1 by omega, factorial]

theorem exponential_term_offset_le {x : ℚ} (hx : 0 ≤ x) (m j : Nat) :
    x ^ (m + j) / (factorial (m + j) : ℚ) ≤
      (x ^ m / (factorial m : ℚ)) * (x / (m + 1 : ℚ)) ^ j := by
  have hfact : (factorial m : ℚ) * (m + 1 : ℚ) ^ j ≤ (factorial (m + j) : ℚ) := by
    exact_mod_cast factorial_offset_lower m j
  have hpos : (0 : ℚ) < (factorial m : ℚ) * (m + 1 : ℚ) ^ j := by
    have hf : (0 : ℚ) < factorial m := by exact_mod_cast factorial_pos m
    positivity
  calc
    _ ≤ x ^ (m + j) / ((factorial m : ℚ) * (m + 1 : ℚ) ^ j) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) hpos hfact
    _ = _ := by rw [pow_add, div_pow]; ring

theorem exponential_tail_le {x : ℚ} (hx : 0 ≤ x) (m n : Nat)
    (hratio : x / (m + 1 : ℚ) < 1) :
    (∑ j ∈ Finset.range n, x ^ (m + j) / (factorial (m + j) : ℚ)) ≤
      (x ^ m / (factorial m : ℚ)) / (1 - x / (m + 1 : ℚ)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        (x ^ m / (factorial m : ℚ)) * (x / (m + 1 : ℚ)) ^ j :=
      Finset.sum_le_sum (fun j _ => exponential_term_offset_le hx m j)
    _ = (x ^ m / (factorial m : ℚ)) * geometricCut (x / (m + 1 : ℚ)) n := by
      rw [geometricCut, Finset.mul_sum]
    _ ≤ (x ^ m / (factorial m : ℚ)) * (1 / (1 - x / (m + 1 : ℚ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact geometricCut_le_inverse (div_nonneg hx (by positivity)) hratio n
      · positivity
    _ = _ := by ring

theorem sum_map_range (f : Nat → ℚ) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem partialSum_eq_sum (a : Nat → ℚ) (n : Nat) :
    partialSum a n = ∑ i ∈ Finset.range n, a i / (factorial i : ℚ) := by
  unfold partialSum
  rw [← List.sum_eq_foldl, sum_map_range]

theorem weightedCut_mono {c : Nat → ℚ} {x : ℚ} (hc : ∀ i, 0 ≤ c i)
    (hx : 0 ≤ x) {m n : Nat} (hmn : m ≤ n) : weightedCut c x m ≤ weightedCut c x n := by
  unfold weightedCut
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro i hi hnot
  exact mul_nonneg (hc i) (div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))

theorem weightedCut_tail_le {c : Nat → ℚ} {x : ℚ}
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hx : 0 ≤ x) (m n : Nat)
    (hratio : x / (m + 1 : ℚ) < 1) :
    weightedCut c x n ≤ weightedCut c x m +
      (x ^ m / (factorial m : ℚ)) / (1 - x / (m + 1 : ℚ)) := by
  by_cases hnm : n ≤ m
  · exact (weightedCut_mono hc0 hx hnm).trans (le_add_of_nonneg_right (by positivity))
  · have hmn : m ≤ n := by omega
    calc
      weightedCut c x n = weightedCut c x m +
          ∑ j ∈ Finset.range (n - m), c (m + j) *
            (x ^ (m + j) / (factorial (m + j) : ℚ)) := by
        unfold weightedCut
        conv_lhs => rw [show n = m + (n - m) by omega, Finset.sum_range_add]
      _ ≤ weightedCut c x m +
          ∑ j ∈ Finset.range (n - m), x ^ (m + j) / (factorial (m + j) : ℚ) := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro j hj
        simpa using mul_le_mul_of_nonneg_right (hc1 (m + j))
          (div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))
      _ ≤ _ := add_le_add le_rfl (exponential_tail_le hx m (n - m) hratio)

theorem exponentialCut_le_expUpper (n m : Nat) (hm : 0 < m) :
    exponentialCut 1 n ≤ expUpper m := by
  have hratio : (1 : ℚ) / (m + 1 : ℚ) < 1 := by
    apply (div_lt_one (by positivity : (0 : ℚ) < m + 1)).2
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    linarith
  have h := weightedCut_tail_le (c := fun _ => (1 : ℚ))
    (by intro i; norm_num) (by intro i; norm_num) (by norm_num) m n hratio
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hfQ : (factorial m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (factorial_pos m)
  have hmp : (m : ℚ) + 1 ≠ 0 := by positivity
  have htail : ((1 : ℚ) ^ m / (factorial m : ℚ)) / (1 - 1 / (m + 1 : ℚ)) =
      (m + 1 : Nat) / ((m * factorial m : Nat) : ℚ) := by
    push_cast
    field_simp [hmQ, hfQ, hmp, Nat.ne_of_gt hm]
    ring
  rw [htail] at h
  simpa [weightedCut, exponentialCut, expUpper, partialSum_eq_sum] using h

end PoissonDAG
