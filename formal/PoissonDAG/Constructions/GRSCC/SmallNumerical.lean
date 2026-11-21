import PoissonDAG.Constructions.GRSCC.SmallParameters
import PoissonDAG.Probability.PoissonEnvelope

/-! The small finite envelope is rational arithmetic only. Its use for the
literal scheme additionally requires the twenty local-count inequalities.
-/
namespace PoissonDAG.GRSCC.Small

set_option maxRecDepth 20000

/-- A cheap smoke test for the one-history scalar recurrence. -/
theorem upperChild_one : upperChild 1 = 1 / (2 * (32 * 15597 : Rat)^7) := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- The finite head and analytic tail fit the unchanged raw covering budget.
No histogram, external coefficient table, or real exponential is evaluated.
-/
theorem numerical_bound :
    acceptanceRatio *
      (weightedCut upperChild ((1 : Rat) / 16) 18 +
        poissonTail ((1 : Rat) / 16) 18) ≤
      ((1 : Rat) / 2^128) * exponentialCut ((1 : Rat) / 16) 8 := by
  simp only [weightedCut, upperChild, initialState,
    binomialMass, Nat.choose_eq_fast_choose]
  decide +kernel

end PoissonDAG.GRSCC.Small
