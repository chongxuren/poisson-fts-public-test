import PoissonDAG.Constructions.GRSCC.SmallParameters
import PoissonDAG.Constructions.GRSCC.CoveringBound
import PoissonDAG.Constructions.GRSCC.Markov
import PoissonDAG.Probability.PoissonEnvelope

set_option Elab.async false

/-! Positive domination of the shared-history recurrence, followed by the
generic rational Poisson envelope. Only the local upper bounds remain as a
premise; no independence between layers is introduced. -/
namespace PoissonDAG.GRSCC.Small

private theorem binomial_nonneg {p : Rat} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (m v : Nat) : 0 ≤ binomialMass m v p := by
  have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  unfold binomialMass
  split_ifs <;> positivity

theorem localUpper_nonneg (m v : Nat) : 0 ≤ localUpper m v := by
  unfold localUpper
  split_ifs <;> positivity

private theorem localCover_nonneg (m v : Nat) : 0 ≤ localCover m v := by
  unfold localCover
  split_ifs
  · exact le_rfl
  · exact div_nonneg (by exact_mod_cast localNumerator_nonnegative m v)
      (Nat.cast_nonneg _)

private theorem jointKernel_nonneg (q m n : Nat) : 0 ≤ jointKernel q m n := by
  rw [jointKernel, PoissonDAG.sum_map_range]
  apply Finset.sum_nonneg
  intro v hv
  dsimp only
  split_ifs
  · exact mul_nonneg
      (mul_nonneg (binomial_nonneg (by norm_num) (by norm_num) _ _)
        (localCover_nonneg _ _))
      (binomial_nonneg (by norm_num) (by norm_num) _ _)
  · exact le_rfl

theorem upperKernel_nonneg (q m n : Nat) : 0 ≤ upperKernel q m n := by
  rw [upperKernel, PoissonDAG.sum_map_range]
  apply Finset.sum_nonneg
  intro v hv
  dsimp only
  split_ifs
  · exact mul_nonneg
      (mul_nonneg (binomial_nonneg (by norm_num) (by norm_num) _ _)
        (localUpper_nonneg _ _))
      (binomial_nonneg (by norm_num) (by norm_num) _ _)
  · exact le_rfl

theorem jointKernel_le_upperKernel
    (hcap : ∀ m v, localCover m v ≤ localUpper m v) (q m n : Nat) :
    jointKernel q m n ≤ upperKernel q m n := by
  rw [jointKernel, upperKernel, PoissonDAG.sum_map_range, PoissonDAG.sum_map_range]
  apply Finset.sum_le_sum
  intro v hv
  dsimp only
  split_ifs
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcap _ _)
        (binomial_nonneg (by norm_num) (by norm_num) _ _))
      (binomial_nonneg (by norm_num) (by norm_num) _ _)
  · exact le_rfl

private theorem getD_map_range (q i : Nat) (f : Nat → Rat) :
    (((List.range q).map f)[i]?).getD 0 = if i < q then f i else 0 := by
  by_cases hi : i < q
  · rw [List.getElem?_map, List.getElem?_range hi]
    simp [hi]
  · have hn : ((List.range q).map f)[i]? = none :=
      List.getElem?_eq_none (by
        simpa only [List.length_map, List.length_range] using Nat.le_of_not_gt hi)
    simp [hn, hi]

private def advance (q : Nat) (K : Nat → Nat → Rat) (s : List Rat) : List Rat :=
  (List.range q).map (fun k => ((List.range q).map (fun j =>
    (s[j]?.getD 0) * K (j + 1) (k + 1))).sum)

private theorem advance_nonneg (q : Nat) (K : Nat → Nat → Rat)
    (hK : ∀ m n, 0 ≤ K m n) (s : List Rat)
    (hs : ∀ i : Nat, 0 ≤ s[i]?.getD 0) (i : Nat) :
    0 ≤ (advance q K s)[i]?.getD 0 := by
  unfold advance
  rw [getD_map_range]
  split_ifs
  · rw [PoissonDAG.sum_map_range]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hs j) (hK _ _))
  · exact le_rfl

private theorem advance_mono (q : Nat) (K U : Nat → Nat → Rat)
    (hK : ∀ m n, 0 ≤ K m n) (hKU : ∀ m n, K m n ≤ U m n)
    (s t : List Rat) (ht : ∀ i : Nat, 0 ≤ t[i]?.getD 0)
    (hst : ∀ i : Nat, s[i]?.getD 0 ≤ t[i]?.getD 0) (i : Nat) :
    (advance q K s)[i]?.getD 0 ≤ (advance q U t)[i]?.getD 0 := by
  unfold advance
  rw [getD_map_range, getD_map_range]
  split_ifs
  · rw [PoissonDAG.sum_map_range, PoissonDAG.sum_map_range]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul (hst j) (hKU _ _) (hK _ _) (ht j))
  · exact le_rfl

private theorem initial_nonneg (q i : Nat) : 0 ≤ (initialState q)[i]?.getD 0 := by
  unfold initialState
  rw [getD_map_range]
  split_ifs
  · exact binomial_nonneg (by norm_num) (by norm_num) _ _
  · exact le_rfl

private theorem advance_iterate_bounds (q : Nat) (K U : Nat → Nat → Rat)
    (hK : ∀ m n, 0 ≤ K m n) (hU : ∀ m n, 0 ≤ U m n)
    (hKU : ∀ m n, K m n ≤ U m n) (s : List Rat)
    (hs : ∀ i : Nat, 0 ≤ s[i]?.getD 0) (n : Nat) :
    (∀ i : Nat, 0 ≤ (((advance q U)^[n] s)[i]?).getD 0) ∧
    (∀ i : Nat, (((advance q K)^[n] s)[i]?).getD 0 ≤
      (((advance q U)^[n] s)[i]?).getD 0) := by
  induction n with
  | zero => exact ⟨hs, fun _ => le_rfl⟩
  | succ n ih =>
      constructor
      · intro i
        rw [Function.iterate_succ_apply']
        exact advance_nonneg q U hU (((advance q U)^[n] s)) ih.1 i
      · intro i
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact advance_mono q K U hK hKU
          (((advance q K)^[n] s)) (((advance q U)^[n] s)) ih.1 ih.2 i

private theorem kernelStep_eq_advance (q : Nat) :
    kernelStep q = advance q (jointKernel q) := rfl

private theorem upperStep_eq_advance (q : Nat) :
    upperStep q = advance q (upperKernel q) := rfl

private theorem iterate_bounds
    (hcap : ∀ m v, localCover m v ≤ localUpper m v) (q n : Nat) :
    (∀ i : Nat, 0 ≤ (((upperStep q)^[n] (initialState q))[i]?).getD 0) ∧
    (∀ i : Nat, (((kernelStep q)^[n] (initialState q))[i]?).getD 0 ≤
      (((upperStep q)^[n] (initialState q))[i]?).getD 0) := by
  simpa only [kernelStep_eq_advance, upperStep_eq_advance] using
    advance_iterate_bounds q (jointKernel q) (upperKernel q)
      (jointKernel_nonneg q) (upperKernel_nonneg q) (jointKernel_le_upperKernel hcap q)
      (initialState q) (initial_nonneg q) n

private theorem list_sum_nonneg (s : List Rat) :
    (∀ i : Nat, 0 ≤ s[i]?.getD 0) → 0 ≤ s.sum := by
  induction s with
  | nil => simp
  | cons a s ih =>
      intro h
      have ha : 0 ≤ a := by simpa using h 0
      have hs : ∀ i : Nat, 0 ≤ s[i]?.getD 0 := by
        intro i
        simpa using h (i + 1)
      simpa only [List.sum_cons] using add_nonneg ha (ih hs)

private theorem list_sum_mono (s t : List Rat) :
    (∀ i : Nat, s[i]?.getD 0 ≤ t[i]?.getD 0) → s.sum ≤ t.sum := by
  induction s generalizing t with
  | nil =>
      intro h
      apply list_sum_nonneg
      intro i
      simpa using h i
  | cons a s ih =>
      cases t with
      | nil =>
          intro h
          have ha : a ≤ 0 := by simpa using h 0
          have hs : s.sum ≤ 0 := by
            have ht := ih [] (fun i => by simpa using h (i + 1))
            simpa using ht
          simpa using add_nonpos ha hs
      | cons b t =>
          intro h
          have hab : a ≤ b := by simpa using h 0
          have hst : ∀ i : Nat, s[i]?.getD 0 ≤ t[i]?.getD 0 := by
            intro i
            simpa using h (i + 1)
          simpa only [List.sum_cons] using add_le_add hab (ih t hst)

private theorem upperIterate_nonneg (q n : Nat) :
    ∀ i : Nat, 0 ≤ (((upperStep q)^[n] (initialState q))[i]?).getD 0 := by
  have h := advance_iterate_bounds q (upperKernel q) (upperKernel q)
    (upperKernel_nonneg q) (upperKernel_nonneg q) (fun _ _ => le_rfl)
    (initialState q) (initial_nonneg q) n
  simpa only [upperStep_eq_advance] using h.1

theorem upperChild_nonneg (q : Nat) : 0 ≤ upperChild q := by
  change 0 ≤ (((upperStep q)^[7] (initialState q))).sum
  exact list_sum_nonneg _ (upperIterate_nonneg q 7)

theorem childCover_le_upperChild
    (hcap : ∀ m v, localCover m v ≤ localUpper m v) (q : Nat) :
    childCover q ≤ upperChild q := by
  change (((kernelStep q)^[7] (initialState q))).sum ≤
    (((upperStep q)^[7] (initialState q))).sum
  exact list_sum_mono _ _ (iterate_bounds hcap q 7).2

theorem boundedChild_nonneg (q : Nat) : 0 ≤ boundedChild q :=
  le_min (upperChild_nonneg q) (by norm_num)

theorem boundedChild_le_one (q : Nat) : boundedChild q ≤ 1 := min_le_right _ _

theorem boundedChild_le_upperChild (q : Nat) : boundedChild q ≤ upperChild q :=
  min_le_left _ _

theorem childCover_le_boundedChild
    (hcap : ∀ m v, localCover m v ≤ localUpper m v) (q : Nat) :
    childCover q ≤ boundedChild q :=
  le_min (childCover_le_upperChild hcap q) (childCover_le_one q)

private theorem bucketThinned_eq_transform (q : Nat) :
    bucketThinned q = binomialTransform ((1 : Rat) / 16) childCover q := by
  unfold bucketThinned binomialTransform
  rw [PoissonDAG.sum_map_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ q := by have := Finset.mem_range.mp hj; omega
  simp [binomialMass, hle]

private theorem transform_mono {a b : Nat → Rat} (hab : ∀ i, a i ≤ b i) (q : Nat) :
    binomialTransform ((1 : Rat) / 16) a q ≤ binomialTransform ((1 : Rat) / 16) b q := by
  unfold binomialTransform
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left (hab j)
  have : 0 ≤ (1 : Rat) - 1 / 16 := by norm_num
  positivity

/-- Local counting and finite rational arithmetic are separate obligations. -/
theorem poisson_bound_of_bounds
    (hcap : ∀ m v, localCover m v ≤ localUpper m v)
    (hnumeric : acceptanceRatio *
      (weightedCut upperChild ((1 : Rat) / 16) 18 + poissonTail ((1 : Rat) / 16) 18) ≤
      ((1 : Rat) / 2^128) * exponentialCut ((1 : Rat) / 16) 8) :
    PoissonLE scheme.coverCoefficient ((1 : Rat) / 2^128) := by
  apply poissonLE_of_thinning_envelope (c := boundedChild) (p := (1 : Rat) / 16)
    (scale := acceptanceRatio) (cutoff := 18) (normalizer := 8)
    (by norm_num) (by norm_num) acceptanceRatio_pos.le (by positivity)
    boundedChild_nonneg boundedChild_le_one
  · intro q
    calc
      scheme.coverCoefficient q ≤ acceptanceRatio * bucketThinned q :=
        scheme_coefficient_upper q
      _ = acceptanceRatio * binomialTransform ((1 : Rat) / 16) childCover q := by
        rw [bucketThinned_eq_transform]
      _ ≤ acceptanceRatio * binomialTransform ((1 : Rat) / 16) boundedChild q :=
        mul_le_mul_of_nonneg_left
          (transform_mono (childCover_le_boundedChild hcap) q) acceptanceRatio_pos.le
  · norm_num
  · have hcut : weightedCut boundedChild ((1 : Rat) / 16) 18 ≤
        weightedCut upperChild ((1 : Rat) / 16) 18 := by
      unfold weightedCut
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right (boundedChild_le_upperChild q)
      positivity
    have hsum :
        weightedCut boundedChild ((1 : Rat) / 16) 18 + poissonTail ((1 : Rat) / 16) 18 ≤
        weightedCut upperChild ((1 : Rat) / 16) 18 + poissonTail ((1 : Rat) / 16) 18 :=
      add_le_add hcut le_rfl
    exact (mul_le_mul_of_nonneg_left hsum acceptanceRatio_pos.le).trans hnumeric

end PoissonDAG.GRSCC.Small
