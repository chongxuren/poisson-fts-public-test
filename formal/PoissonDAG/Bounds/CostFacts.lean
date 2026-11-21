import PoissonDAG.Probability.Counting
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Ring.Pow

/-! # Exact finite-counter costs

Every bound refers to the protected interpreter's unconditional cost, including
failure. No infinite-retry premise or pointwise verification limit is added.
-/

namespace PoissonDAG

theorem expectedTrials_mul_tau (s : Scheme) :
    s.expectedTrials * s.tau = 1 - s.failure := by
  unfold Scheme.expectedTrials Scheme.failure
  rw [← List.sum_eq_foldl]
  have h (n : Nat) :
      (((List.range n).map (fun j => (1 - s.tau)^j)).sum) * s.tau =
        1-(1-s.tau)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton, pow_succ]
      nlinarith
  exact h s.trials

theorem generation_le_signCost (s : Scheme) : (s.graph.length : ℚ) ≤ s.signCost := by
  unfold Scheme.signCost
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (expectedTrials_nonneg s))

theorem expectedTrials_le_signCost {s : Scheme} (hw : s.WellFormed) :
    s.expectedTrials ≤ s.signCost := by
  have hd : (1 : ℚ) ≤ s.digestCalls := by exact_mod_cast digestCalls_pos hw
  have ht := expectedTrials_nonneg s
  unfold Scheme.signCost
  nlinarith [show (0 : ℚ) ≤ (s.graph.length : ℚ) from Nat.cast_nonneg _]

theorem eligible_generation_bound {s : Scheme} (he : s.Eligible) :
    s.graph.length ≤ 2^24 := by
  have hs := he.2.2.2.1
  exact_mod_cast (generation_le_signCost s).trans hs

theorem eligible_acceptance_floor {s : Scheme} (he : s.Eligible) :
    (1 : ℚ) / 2^25 < s.tau := by
  have hw := he.1
  have ht := tau_pos hw
  have hs := he.2.2.2.1
  have hf := he.2.2.1
  have hcost := expectedTrials_le_signCost hw
  have hid := expectedTrials_mul_tau s
  have hprod : 1 - s.failure ≤ (2^24 : ℚ) * s.tau := by
    nlinarith
  norm_num at hf ⊢
  linarith

theorem counter_small_acceptance_floor {s : Scheme} (hw : s.WellFormed)
    (hc : s.counterBits ≤ 16) (hf : s.failure ≤ (1 : ℚ) / 2^128) :
    (1 : ℚ) / 2^10 < s.tau := by
  have ht := tau_pos hw
  by_contra hn
  have hsmall : s.tau ≤ (1 : ℚ)/1024 := by norm_num at hn ⊢; linarith
  have hR : s.trials ≤ 65536 := by
    unfold Scheme.trials
    exact (Nat.pow_le_pow_right (by omega : 0 < 2) hc)
  have hbase0 : (0 : ℚ) ≤ 1-s.tau := sub_nonneg.mpr (tau_le_one s)
  have hbase1 : 1-s.tau ≤ (1 : ℚ) := by linarith
  have hhalf : (1 : ℚ)/2 < (1-s.tau)^512 := by
    have bern := one_add_mul_sub_le_pow
      (by nlinarith [sq_nonneg ((1 : ℚ)-s.tau)] : (-1 : ℚ) ≤ (1-s.tau)^2) 256
    calc
      (1 : ℚ)/2 < 1-512*s.tau+256*s.tau^2 := by
        nlinarith [sq_pos_of_pos ht]
      _ = 1+256*((1-s.tau)^2-1) := by ring
      _ ≤ ((1-s.tau)^2)^256 := bern
      _ = (1-s.tau)^512 := by rw [← pow_mul]
  have he : ((1-s.tau)^512)^128 ≤ s.failure := by
    calc
      ((1-s.tau)^512)^128 = (1-s.tau)^65536 := by rw [← pow_mul]
      _ ≤ (1-s.tau)^s.trials := pow_le_pow_of_le_one hbase0 hbase1 hR
      _ = s.failure := rfl
  have endpoint : (1 : ℚ)/2^128 < ((1-s.tau)^512)^128 := by
    calc
      (1 : ℚ)/2^128 = ((1 : ℚ)/2)^128 := by norm_num
      _ < ((1-s.tau)^512)^128 := by gcongr
  exact (not_lt_of_ge (he.trans hf)) endpoint

end PoissonDAG
