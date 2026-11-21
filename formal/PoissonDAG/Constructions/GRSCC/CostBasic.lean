import PoissonDAG.Constructions.GRSCC.Graph

/-! Exact protected-model finite-trial cost inequalities. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

theorem foldMax_le (xs : List Nat) (bound initial : Nat)
    (hi : initial ≤ bound) (hx : ∀ x ∈ xs, x ≤ bound) :
    xs.foldl max initial ≤ bound := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons x xs ih =>
      apply ih (max initial x)
      · exact max_le hi (hx x (by simp))
      · intro y hy
        exact hx y (by simp [hy])

theorem size_budget_of_refinement (s : Scheme)
    (hcounter : s.counterBits = counterWidth)
    (hfrontier : ∀ raw ∈ s.accepted,
      ∃ r : Route, s.frontier raw = r.frontier) :
    s.size ≤ 756 := by
  have hmax : ((s.accepted.map (fun raw => weight (s.frontier raw))).foldl max 0) ≤
      47 := by
    apply foldMax_le _ 47 0 (by decide)
    intro w hw
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hw
    obtain ⟨r, hr⟩ := hfrontier raw hraw
    rw [hr]
    exact frontier_weight_le r
  unfold Scheme.size
  rw [hcounter]
  norm_num [counterWidth]
  omega

theorem rational_sum_le_length_mul (xs : List ℚ) (bound : ℚ)
    (hx : ∀ x ∈ xs, x ≤ bound) : xs.sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxbound := hx x (by simp)
      have hrest := ih (fun y hy => hx y (by simp [hy]))
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

theorem verification_budget_of_refinement (s : Scheme)
    (hnonempty : 0 < s.accepted.length)
    (hfailure : 0 ≤ s.failure) (hfailureone : s.failure ≤ 1)
    (hverify : ∀ raw ∈ s.accepted, s.verifyCalls raw ≤ 441) :
    s.verifyCost ≤ 512 := by
  let costs := s.accepted.map (fun raw => (s.verifyCalls raw : ℚ))
  have ha : (0 : ℚ) < s.accepted.length := Nat.cast_pos.mpr hnonempty
  have hsum : costs.sum ≤ (s.accepted.length : ℚ) * 441 := by
    have h := rational_sum_le_length_mul costs 441 (by
      intro x hx
      obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hx
      exact Nat.cast_le.mpr (hverify raw hraw))
    simpa [costs] using h
  have hsumzero : 0 ≤ costs.sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.cast_nonneg _
  have havg : costs.sum / (s.accepted.length : ℚ) ≤ 441 := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have havgzero : 0 ≤ costs.sum / (s.accepted.length : ℚ) :=
    div_nonneg hsumzero ha.le
  have hmul := mul_le_mul (show 1 - s.failure ≤ (1 : ℚ) by linarith)
    havg havgzero (by norm_num : (0 : ℚ) ≤ 1)
  rw [List.sum_eq_foldl] at hmul
  change s.verifyCost ≤ 1 * 441 at hmul
  norm_num at hmul
  linarith


end PoissonDAG.GRSCC
