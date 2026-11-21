import PoissonDAG.Constructions.GRSCC.Parameters

/-! Exact protected-model finite-trial cost inequalities. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

theorem geometric_identity (τ : ℚ) (n : Nat) :
    τ * ((List.range n).map (fun j => (1 - τ) ^ j)).sum =
      1 - (1 - τ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton, pow_succ]
      nlinarith

theorem expectedTrials_le_inverse (s : Scheme) (hτ : 0 < s.tau)
    (hτone : s.tau ≤ 1) : s.expectedTrials ≤ 1 / s.tau := by
  have h := geometric_identity s.tau s.trials
  have hp : 0 ≤ (1 - s.tau) ^ s.trials := pow_nonneg (by linarith) _
  rw [List.sum_eq_foldl] at h
  change s.tau * s.expectedTrials = 1 - (1 - s.tau) ^ s.trials at h
  apply (le_div_iff₀ hτ).2
  nlinarith


end PoissonDAG.GRSCC
