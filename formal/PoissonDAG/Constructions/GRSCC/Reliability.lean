import PoissonDAG.Constructions.GRSCC.CostTrials

/-! Exact protected-model finite-trial cost inequalities. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

/-- Elementary finite geometric bound; it avoids evaluating huge powers. -/
theorem failure_times_linear_le_one (τ : ℚ) (hτ : 0 ≤ τ) (hτone : τ ≤ 1)
    (n : Nat) : (1 - τ) ^ n * (1 + (n : ℚ) * τ) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0 ≤ (1 - τ) ^ n := pow_nonneg (by linarith) _
      have hs : (1 - τ) * (1 + ((n + 1 : Nat) : ℚ) * τ) ≤
          1 + (n : ℚ) * τ := by
        simp only [Nat.cast_add, Nat.cast_one]
        have hn : 0 ≤ (n : ℚ) := Nat.cast_nonneg n
        nlinarith [sq_nonneg τ, mul_nonneg hn (sq_nonneg τ)]
      calc
        (1 - τ) ^ (n + 1) * (1 + ((n + 1 : Nat) : ℚ) * τ) =
            (1 - τ) ^ n * ((1 - τ) *
              (1 + ((n + 1 : Nat) : ℚ) * τ)) := by rw [pow_succ]; ring
        _ ≤ (1 - τ) ^ n * (1 + (n : ℚ) * τ) :=
          mul_le_mul_of_nonneg_left hs hp
        _ ≤ 1 := ih

theorem fixed_counter_reliability (τ : ℚ)
    (hτ : (1 : ℚ) / 2 ^ 23 ≤ τ) (hτone : τ ≤ 1) :
    (1 - τ) ^ (2 ^ 32 : Nat) ≤ (1 : ℚ) / 2 ^ 128 := by
  have hτzero : 0 ≤ τ := le_trans (by norm_num) hτ
  have hp : 0 ≤ (1 - τ) ^ (2 ^ 23 : Nat) :=
    pow_nonneg (by linarith) _
  have hlinear := failure_times_linear_le_one τ hτzero hτone (2 ^ 23)
  have hfactor : (1 : ℚ) ≤ (2 ^ 23 : Nat) * τ := by
    norm_num at hτ ⊢
    linarith only [hτ]
  generalize hX : (1 - τ) ^ (2 ^ 23 : Nat) = block at hp hlinear
  have hblock : block ≤ (1 : ℚ) / 2 := by
    have hgap := mul_nonneg hp (sub_nonneg.mpr hfactor)
    nlinarith only [hlinear, hgap]
  have hpower : block ^ (512 : Nat) ≤ ((1 : ℚ) / 2) ^ (512 : Nat) :=
    pow_le_pow_left₀ hp hblock _
  have hexponent : (2 ^ 32 : Nat) = (2 ^ 23 : Nat) * 512 := by norm_num
  calc
    (1 - τ) ^ (2 ^ 32 : Nat) = (1 - τ) ^ ((2 ^ 23 : Nat) * 512) :=
      congrArg (fun exponent : Nat => (1 - τ) ^ exponent) hexponent
    _ = ((1 - τ) ^ (2 ^ 23 : Nat)) ^ (512 : Nat) := pow_mul _ _ _
    _ = block ^ (512 : Nat) := congrArg (fun value : ℚ => value ^ (512 : Nat)) hX
    _ ≤ ((1 : ℚ) / 2) ^ (512 : Nat) := hpower
    _ ≤ ((1 : ℚ) / 2) ^ (128 : Nat) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by decide)
    _ = (1 : ℚ) / 2 ^ 128 := by rw [div_pow, one_pow]



end PoissonDAG.GRSCC
