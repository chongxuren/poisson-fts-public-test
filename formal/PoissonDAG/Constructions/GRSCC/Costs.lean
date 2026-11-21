import PoissonDAG.Constructions.GRSCC.CostBasic
import PoissonDAG.Constructions.GRSCC.Reliability

/-! Exact protected-model finite-trial cost inequalities. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

theorem affine_inverse_bound (base rate tau trials budget : ℚ)
    (hrate : 0 ≤ rate) (htrials : trials ≤ 1 / tau)
    (hbudget : base + rate / tau ≤ budget) :
    base + rate * trials ≤ budget := by
  calc
    base + rate * trials ≤ base + rate * (1 / tau) :=
      add_le_add (le_refl base) (mul_le_mul_of_nonneg_left htrials hrate)
    _ = base + rate / tau := by rw [mul_one_div]
    _ ≤ budget := hbudget

theorem signing_budget_of_refinement (s : Scheme)
    (hgraph : s.graph.length = graphNodes)
    (hdigest : s.digestCalls = digestBlockCount)
    (htau : s.tau = acceptanceRatio) (hτone : s.tau ≤ 1) :
    s.signCost ≤ 2 ^ 24 := by
  have hτ : 0 < s.tau := by rw [htau]; exact acceptanceRatio_pos
  have htrials := expectedTrials_le_inverse s hτ hτone
  have htrials' : s.expectedTrials ≤ 1 / acceptanceRatio := by
    simpa only [htau] using htrials
  have h := affine_inverse_bound (graphNodes : ℚ) (digestBlockCount : ℚ)
    acceptanceRatio s.expectedTrials (2 ^ 24) (Nat.cast_nonneg _) htrials'
    fixed_trial_signing_budget.le
  change (s.graph.length : ℚ) + (s.digestCalls : ℚ) * s.expectedTrials ≤ 2 ^ 24
  rw [hgraph, hdigest]
  exact h

theorem failure_budget_of_refinement (s : Scheme)
    (hcounter : s.counterBits = counterWidth)
    (htau : s.tau = acceptanceRatio) (hτone : s.tau ≤ 1) :
    s.failure ≤ (1 : ℚ) / 2 ^ 128 := by
  have hτ : (1 : ℚ) / 2 ^ 23 ≤ s.tau := by
    rw [htau]
    exact acceptanceRatio_lower
  simpa only [Scheme.failure, Scheme.trials, hcounter, counterWidth] using
    fixed_counter_reliability s.tau hτ hτone

end PoissonDAG.GRSCC
