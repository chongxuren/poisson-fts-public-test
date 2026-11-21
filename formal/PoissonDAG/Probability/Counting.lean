import PoissonDAG.Model
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # Elementary finite probabilities of the protected interpreter -/

namespace PoissonDAG

theorem accepted_length_le (s : Scheme) : s.accepted.length ≤ 2 ^ s.encoder.inputs := by
  simpa [Scheme.accepted, Scheme.raws] using List.length_filter_le s.accept s.raws

theorem tau_nonneg (s : Scheme) : 0 ≤ s.tau := by
  unfold Scheme.tau
  positivity

theorem tau_le_one (s : Scheme) : s.tau ≤ 1 := by
  unfold Scheme.tau
  have hp : (0 : ℚ) < (2 ^ s.encoder.inputs : Nat) := by positivity
  apply (div_le_one hp).2
  exact_mod_cast accepted_length_le s

theorem tau_pos {s : Scheme} (hw : s.WellFormed) : 0 < s.tau := by
  unfold Scheme.tau
  exact div_pos (by exact_mod_cast hw.2.2.2.2.2) (by positivity)

theorem digestCalls_pos {s : Scheme} (hw : s.WellFormed) : 1 ≤ s.digestCalls := by
  unfold Scheme.digestCalls
  have hr := hw.2.1
  omega

theorem coverCoefficient_nonneg (s : Scheme) (q : Nat) : 0 ≤ s.coverCoefficient q := by
  unfold Scheme.coverCoefficient
  positivity

theorem expectedTrials_nonneg (s : Scheme) : 0 ≤ s.expectedTrials := by
  unfold Scheme.expectedTrials
  rw [← List.sum_eq_foldl]
  apply List.sum_nonneg
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact pow_nonneg (sub_nonneg.mpr (tau_le_one s)) _

theorem failure_nonneg (s : Scheme) : 0 ≤ s.failure := by
  exact pow_nonneg (sub_nonneg.mpr (tau_le_one s)) _

end PoissonDAG
