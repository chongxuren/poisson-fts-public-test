import PoissonDAG.Constructions.GRSCC.SmallParameters
import PoissonDAG.Probability.BoundedCompositions
import Mathlib.Data.Fintype.EquivFin

set_option maxHeartbeats 50000
set_option maxRecDepth 1000

/-!
# Small exact masked-coordinate counts

This module develops the reviewed bounded-composition route directly from
the original local supplier events. No dense prefix table, external grouping
map, or historical numerical coefficient is used.
-/

namespace PoissonDAG.GRSCC.Small

open PoissonDAG.BoundedCompositions

def maskedBound (target : Codeword) (mask : Nat) (j : CodePosition) : Nat :=
  if mask.testBit j.val = true then (target.depth j).val else 9

theorem maskedBound_le_nine (target : Codeword) (mask : Nat) (j : CodePosition) :
    maskedBound target mask j ≤ 9 := by
  unfold maskedBound
  split
  · have hj := (target.depth j).isLt
    omega
  · omega

theorem avoidance_mem_iff_maskedBound (target : Codeword) (mask : Nat)
    (rank : Fin codeCardinality) :
    rank ∈ avoidanceSet (sameSlotSupply target) (requirementsOfMask mask) ↔
      ∀ j : CodePosition, ((decodedCodeword rank).depth j).val < maskedBound target mask j := by
  rw [masked_avoidance_iff]
  constructor
  · intro h j
    by_cases hm : mask.testBit j.val = true
    · have hj := h j hm
      simp only [sameSlotSupply, decide_eq_false_iff_not] at hj
      simp only [maskedBound, if_pos hm]
      omega
    · simp only [maskedBound, if_neg hm]
      exact ((decodedCodeword rank).depth j).isLt
  · intro h j hm
    have hj := h j
    simp only [maskedBound, if_pos hm] at hj
    simp only [sameSlotSupply, decide_eq_false_iff_not]
    omega

noncomputable def avoidanceTupleEquiv (target : Codeword) (mask : Nat) :
    {rank : Fin codeCardinality //
      rank ∈ avoidanceSet (sameSlotSupply target) (requirementsOfMask mask)} ≃
      {x : NatTuple 6 16 // ∀ j, x.val j < maskedBound target mask j} :=
  Equiv.ofBijective
    (fun rank => ⟨⟨fun j => ((decodedCodeword rank.val).depth j).val,
      (decodedCodeword rank.val).sum_eq⟩,
      (avoidance_mem_iff_maskedBound target mask rank.val).mp rank.property⟩)
    (by
      constructor
      · intro left right heq
        apply Subtype.ext
        apply decodedCodeword_injective
        apply Codeword.eq_of_coordinatewise_le
        intro j
        have hj := congrArg (fun x => x.val.val j) heq
        exact hj.le
      · intro x
        let word : Codeword :=
          { depth := fun j => ⟨x.val.val j,
              lt_of_lt_of_le (x.property j) (maskedBound_le_nine target mask j)⟩
            sum_eq := x.val.property }
        obtain ⟨rank, hrank⟩ := decodedCodeword_surjective word
        have hallowed : rank ∈ avoidanceSet (sameSlotSupply target) (requirementsOfMask mask) := by
          apply (avoidance_mem_iff_maskedBound target mask rank).mpr
          intro j
          simpa only [hrank, word, Fin.val_mk] using x.property j
        refine ⟨⟨rank, hallowed⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        funext j
        change ((decodedCodeword rank).depth j).val = x.val.val j
        rw [hrank])

theorem avoidanceA_eq_boundedTupleCount6 (target : Codeword) (mask : Nat) :
    avoidanceA target mask = boundedTupleCount6 (maskedBound target mask) := by
  unfold avoidanceA boundedTupleCount6 boundedTupleCount
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (avoidanceTupleEquiv target mask)

theorem avoidanceA_bounded_compositions (target : Codeword) (mask : Nat) :
    (avoidanceA target mask : Int) =
      ∑ T ∈ (Finset.univ : Finset CodePosition).powerset,
        (-1 : Int) ^ T.card *
          (if boundSum (maskedBound target mask) T ≤ 16 then
            (16 - boundSum (maskedBound target mask) T + 5).choose 5 else 0) := by
  rw [avoidanceA_eq_boundedTupleCount6]
  exact boundedTupleCount6_eq _

abbrev FreePositions (S : Finset CodePosition) := {j : CodePosition // j ∉ S}

def assignmentSum (S : Finset CodePosition) (a : S → Fin 8) : Nat :=
  ∑ j : S, ((a j).val + 1)

abbrev FixedRank (S : Finset CodePosition) (a : S → Fin 8) :=
  {rank : Fin codeCardinality // ∀ j : S,
    ((decodedCodeword rank).depth j.val).val = (a j).val + 1}

theorem freePositions_card (S : Finset CodePosition) :
    Fintype.card (FreePositions S) = 6 - S.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

private noncomputable def freeIndex (S : Finset CodePosition) :
    FreePositions S ≃ Fin (Fintype.card (FreePositions S)) := Fintype.equivFin _

private theorem sum_mask_split (S : Finset CodePosition) (f : CodePosition → Nat) :
    (∑ j : S, f j.val) + (∑ j : FreePositions S, f j.val) = ∑ j : CodePosition, f j := by
  have hs : (∑ j : S, f j.val) = ∑ j ∈ S, f j := Finset.sum_coe_sort S f
  have hc : (∑ j : FreePositions S, f j.val) = ∑ j ∈ Sᶜ, f j :=
    (Finset.sum_subtype (p := fun j => j ∉ S) Sᶜ (by intro j; simp) f).symm
  rw [hs, hc]
  exact Finset.sum_add_sum_compl S f

private theorem fixedRank_total (S : Finset CodePosition) (a : S → Fin 8)
    (rank : FixedRank S a) :
    assignmentSum S a +
      (∑ j : FreePositions S, ((decodedCodeword rank.val).depth j.val).val) = 16 := by
  calc
    _ = (∑ j : S, ((decodedCodeword rank.val).depth j.val).val) +
        (∑ j : FreePositions S, ((decodedCodeword rank.val).depth j.val).val) := by
      apply congrArg (· + _)
      apply Finset.sum_congr rfl
      intro j _
      exact (rank.property j).symm
    _ = ∑ j : CodePosition, ((decodedCodeword rank.val).depth j).val :=
      sum_mask_split S (fun j => ((decodedCodeword rank.val).depth j).val)
    _ = 16 := (decodedCodeword rank.val).sum_eq

private noncomputable def freeProjection (S : Finset CodePosition) (a : S → Fin 8)
    (rank : FixedRank S a) :
    {x : NatTuple (Fintype.card (FreePositions S)) (16 - assignmentSum S a) //
      ∀ j, x.val j < 9} := by
  refine ⟨⟨fun i => ((decodedCodeword rank.val).depth ((freeIndex S).symm i).val).val,
    ?_⟩, fun i => ((decodedCodeword rank.val).depth ((freeIndex S).symm i).val).isLt⟩
  have hreindex : (∑ i : Fin (Fintype.card (FreePositions S)),
      ((decodedCodeword rank.val).depth ((freeIndex S).symm i).val).val) =
      ∑ j : FreePositions S, ((decodedCodeword rank.val).depth j.val).val := by
    symm
    apply Fintype.sum_equiv (freeIndex S)
    intro j
    simp only [Equiv.symm_apply_apply]
  rw [hreindex]
  have htotal := fixedRank_total S a rank
  omega

private noncomputable def maskedWord (S : Finset CodePosition) (a : S → Fin 8)
    (hsum : assignmentSum S a ≤ 16)
    (x : {x : NatTuple (Fintype.card (FreePositions S)) (16 - assignmentSum S a) //
      ∀ j, x.val j < 9}) : Codeword := by
  let depth : CodePosition → Fin 9 := fun j =>
    if hj : j ∈ S then ⟨(a ⟨j, hj⟩).val + 1, by have h := (a ⟨j, hj⟩).isLt; omega⟩
    else ⟨x.val.val (freeIndex S ⟨j, hj⟩), x.property _⟩
  refine ⟨depth, ?_⟩
  have hleft : (∑ j : S, (depth j.val).val) = assignmentSum S a := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [depth, dif_pos j.property, Fin.val_mk]
  have hright : (∑ j : FreePositions S, (depth j.val).val) =
      ∑ i : Fin (Fintype.card (FreePositions S)), x.val.val i := by
    calc
      _ = ∑ j : FreePositions S, x.val.val (freeIndex S j) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [depth, dif_neg j.property, Fin.val_mk]
      _ = _ := Fintype.sum_equiv (freeIndex S) _ _ (fun _ => rfl)
  calc
    (∑ j : CodePosition, (depth j).val) =
        (∑ j : S, (depth j.val).val) + (∑ j : FreePositions S, (depth j.val).val) :=
      (sum_mask_split S _).symm
    _ = assignmentSum S a + (16 - assignmentSum S a) := by rw [hleft, hright, x.val.property]
    _ = 16 := by omega

private noncomputable def fixedRankEquiv (S : Finset CodePosition) (a : S → Fin 8)
    (hsum : assignmentSum S a ≤ 16) : FixedRank S a ≃
    {x : NatTuple (Fintype.card (FreePositions S)) (16 - assignmentSum S a) //
      ∀ j, x.val j < 9} :=
  Equiv.ofBijective (freeProjection S a) (by
    constructor
    · intro left right heq
      apply Subtype.ext
      apply decodedCodeword_injective
      apply Codeword.ext
      intro j
      apply Fin.ext
      by_cases hj : j ∈ S
      · exact (left.property ⟨j, hj⟩).trans (right.property ⟨j, hj⟩).symm
      · have h := congrArg (fun x => x.val.val (freeIndex S ⟨j, hj⟩)) heq
        change ((decodedCodeword left.val).depth
          ((freeIndex S).symm (freeIndex S ⟨j, hj⟩)).val).val =
          ((decodedCodeword right.val).depth
            ((freeIndex S).symm (freeIndex S ⟨j, hj⟩)).val).val at h
        simpa only [Equiv.symm_apply_apply] using h
    · intro x
      obtain ⟨rank, hrank⟩ := decodedCodeword_surjective (maskedWord S a hsum x)
      have hfixed : ∀ j : S, ((decodedCodeword rank).depth j.val).val = (a j).val + 1 := by
        intro j
        rw [hrank]
        simp only [maskedWord, dif_pos j.property, Fin.val_mk]
      refine ⟨⟨rank, hfixed⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext i
      change ((decodedCodeword rank).depth ((freeIndex S).symm i).val).val = x.val.val i
      rw [hrank]
      simp only [maskedWord, dif_neg ((freeIndex S).symm i).property,
        Fin.val_mk, Subtype.coe_eta, Equiv.apply_symm_apply])

theorem fixedRank_card (S : Finset CodePosition) (a : S → Fin 8) :
    Fintype.card (FixedRank S a) =
      if assignmentSum S a ≤ 16 then
        boundedTupleCount (Fintype.card (FreePositions S)) (16 - assignmentSum S a) (fun _ => 9)
      else 0 := by
  classical
  split_ifs with hsum
  · unfold boundedTupleCount
    exact Fintype.card_congr (fixedRankEquiv S a hsum)
  · haveI : IsEmpty (FixedRank S a) := ⟨by
      intro rank
      have htotal := fixedRank_total S a rank
      omega⟩
    simp

abbrev PositiveRank (S : Finset CodePosition) :=
  {rank : Fin codeCardinality // ∀ j : S, 0 < ((decodedCodeword rank).depth j.val).val}

def positiveProjection (S : Finset CodePosition) (rank : PositiveRank S) : S → Fin 8 :=
  fun j => ⟨((decodedCodeword rank.val).depth j.val).val - 1, by
    have hp := rank.property j
    have hb := ((decodedCodeword rank.val).depth j.val).isLt
    omega⟩

private def positiveFiberEquiv (S : Finset CodePosition) (a : S → Fin 8) :
    {rank : PositiveRank S // positiveProjection S rank = a} ≃ FixedRank S a where
  toFun rank := ⟨rank.val.val, by
    intro j
    have heq := congrArg (fun f => (f j).val) rank.property
    have hpositive := rank.val.property j
    simp only [positiveProjection, Fin.val_mk] at heq
    omega⟩
  invFun rank :=
    ⟨⟨rank.val, by intro j; have h := rank.property j; omega⟩, by
      funext j
      apply Fin.ext
      change ((decodedCodeword rank.val).depth j.val).val - 1 = (a j).val
      have h := rank.property j
      omega⟩
  left_inv rank := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv rank := by apply Subtype.ext; rfl

theorem sum_positiveRanks (S : Finset CodePosition) (weight : (S → Fin 8) → Int) :
    (∑ rank : PositiveRank S, weight (positiveProjection S rank)) =
      ∑ a : S → Fin 8, (Fintype.card (FixedRank S a) : Int) * weight a := by
  classical
  rw [← Fintype.sum_fiberwise' (positiveProjection S) weight]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_congr (positiveFiberEquiv S a)]

theorem sum_rank_eq_masked (S : Finset CodePosition) (term : Fin codeCardinality → Int)
    (weight : (S → Fin 8) → Int)
    (hpositive : ∀ rank : PositiveRank S, term rank.val = weight (positiveProjection S rank))
    (hzero : ∀ rank : Fin codeCardinality,
      (¬∀ j : S, 0 < ((decodedCodeword rank).depth j.val).val) → term rank = 0) :
    (∑ rank : Fin codeCardinality, term rank) =
      ∑ a : S → Fin 8, (Fintype.card (FixedRank S a) : Int) * weight a := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun rank : Fin codeCardinality => ∀ j : S,
      0 < ((decodedCodeword rank).depth j.val).val) term
  have hnegative : (∑ rank : {rank : Fin codeCardinality //
      ¬∀ j : S, 0 < ((decodedCodeword rank).depth j.val).val}, term rank.val) = 0 := by
    apply Finset.sum_eq_zero
    intro rank _
    exact hzero rank.val rank.property
  rw [hnegative, add_zero] at hsplit
  calc
    _ = ∑ rank : PositiveRank S, term rank.val := hsplit.symm
    _ = ∑ rank : PositiveRank S, weight (positiveProjection S rank) :=
      Finset.sum_congr rfl (fun rank _ => hpositive rank)
    _ = _ := sum_positiveRanks S weight

def fastResidualCount (r t B : Nat) : Nat :=
  if B ≤ t then Nat.fast_choose (r + (t - B) - 1) (t - B) else 0

theorem fastResidualCount_eq (r t B : Nat) : fastResidualCount r t B = residualCount r t B := by
  simp only [fastResidualCount, residualCount, Nat.choose_eq_fast_choose]

def compositionFormula (b : CodePosition → Nat) : Int :=
  ∑ T ∈ (Finset.univ : Finset CodePosition).powerset,
    (-1 : Int) ^ T.card *
      (if boundSum b T ≤ 16 then (Nat.fast_choose (16 - boundSum b T + 5) 5 : Int) else 0)

theorem avoidanceA_eq_compositionFormula (target : Codeword) (mask : Nat) :
    (avoidanceA target mask : Int) = compositionFormula (maskedBound target mask) := by
  rw [avoidanceA_bounded_compositions]
  unfold compositionFormula
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : boundSum (maskedBound target mask) T ≤ 16
  · simp only [if_pos h, Nat.choose_eq_fast_choose]
  · simp only [if_neg h, Nat.cast_zero, mul_zero]

def assignmentBound (S : Finset CodePosition) (a : S → Fin 8) (j : CodePosition) : Nat :=
  if hj : j ∈ S then (a ⟨j, hj⟩).val + 1 else 9

def prefixBound (b : CodePosition → Nat) (depth : Depth) (j : CodePosition) : Nat :=
  if j.val < depth.val then b j else 9

def differentFormula (S : Finset CodePosition) (a : S → Fin 8) : Int :=
  ∑ depth : Depth, if depthPosition depth ∈ S then 0 else
    (2 : Int) ^ (4 - depth.val) * compositionFormula (prefixBound (assignmentBound S a) depth)

theorem maskedBound_of_fixed (target : Codeword) (mask : Nat)
    (a : requirementsOfMask mask → Fin 8)
    (hfixed : ∀ j : requirementsOfMask mask, (target.depth j.val).val = (a j).val + 1) :
    maskedBound target mask = assignmentBound (requirementsOfMask mask) a := by
  funext j
  by_cases hj : j ∈ requirementsOfMask mask
  · have hm : mask.testBit j.val = true := (Finset.mem_filter.mp hj).2
    simp only [maskedBound, if_pos hm, assignmentBound, dif_pos hj]
    exact hfixed ⟨j, hj⟩
  · have hm : mask.testBit j.val ≠ true := by
      intro hm
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
    simp only [maskedBound, if_neg hm, assignmentBound, dif_neg hj]

theorem maskedBound_prefix (target : Codeword) (mask : Nat) (hmask : mask < 64) (depth : Depth) :
    maskedBound target (mask % 2 ^ depth.val) = prefixBound (maskedBound target mask) depth := by
  funext j
  have hbits := mask_prefix_membership (⟨mask, hmask⟩ : Fin 64) depth j
  change (mask % 2 ^ depth.val).testBit j.val =
    (mask.testBit j.val && decide (j.val < depth.val)) at hbits
  unfold maskedBound prefixBound
  rw [hbits]
  cases hm : mask.testBit j.val <;> by_cases hj : j.val < depth.val <;> simp [hm, hj]

theorem avoidanceD_as_sum (target : Codeword) (mask : Nat) :
    avoidanceD target mask = ∑ depth : Depth,
      if mask.testBit depth.val then 0
      else 2 ^ (4 - depth.val) * avoidanceA target (mask % 2 ^ depth.val) := by
  unfold avoidanceD
  rw [← List.sum_toFinset _ (List.nodup_finRange 5), List.toFinset_finRange]

theorem avoidanceD_of_fixed (target : Codeword) (mask : Nat) (hmask : mask < 64)
    (a : requirementsOfMask mask → Fin 8)
    (hfixed : ∀ j : requirementsOfMask mask, (target.depth j.val).val = (a j).val + 1) :
    (avoidanceD target mask : Int) = differentFormula (requirementsOfMask mask) a := by
  rw [avoidanceD_as_sum, Nat.cast_sum]
  unfold differentFormula
  apply Finset.sum_congr rfl
  intro depth _
  have hmem : depthPosition depth ∈ requirementsOfMask mask ↔
      mask.testBit depth.val = true := by simp [requirementsOfMask, depthPosition]
  simp only [hmem]
  by_cases hm : mask.testBit depth.val = true
  · simp only [if_pos hm, Nat.cast_zero]
  · simp only [if_neg hm, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [avoidanceA_eq_compositionFormula, maskedBound_prefix target mask hmask,
      maskedBound_of_fixed target mask a hfixed]

theorem avoidanceA_zero_of_zero (target : Codeword) (mask : Nat) (j : CodePosition)
    (hm : mask.testBit j.val = true) (hzero : (target.depth j).val = 0) :
    avoidanceA target mask = 0 := by
  unfold avoidanceA
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rank hrank
  have h := (avoidance_mem_iff_maskedBound target mask rank).mp hrank j
  simp only [maskedBound, if_pos hm, hzero] at h
  omega

theorem fullMask_bit (j : CodePosition) : (63 : Nat).testBit j.val = true := by
  fin_cases j <;> decide

theorem avoidanceA_full (target : Codeword) : avoidanceA target 63 = 0 := by
  unfold avoidanceA
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rank hrank
  have hbound := (avoidance_mem_iff_maskedBound target 63 rank).mp hrank
  have hle : ∀ j : CodePosition,
      ((decodedCodeword rank).depth j).val ≤ (target.depth j).val := by
    intro j
    have h := hbound j
    simp only [maskedBound, fullMask_bit, if_true] at h
    omega
  have heq := Codeword.eq_of_coordinatewise_le _ _ hle
  have hzero := hbound (0 : CodePosition)
  simp only [maskedBound, fullMask_bit, if_true, heq] at hzero
  omega

theorem positiveProjection_fixed (S : Finset CodePosition) (rank : PositiveRank S) :
    ∀ j : S, ((decodedCodeword rank.val).depth j.val).val =
      (positiveProjection S rank j).val + 1 := by
  intro j
  have hp := rank.property j
  simp only [positiveProjection, Fin.val_mk]
  omega

def maskedMoment (m v mask : Nat)
    (a : requirementsOfMask mask → Fin 8) : Int :=
  subsetSign mask * compositionFormula (assignmentBound (requirementsOfMask mask) a) ^ v *
    differentFormula (requirementsOfMask mask) a ^ (m - v)

theorem localMoment_regrouped (m v : Nat) (hv : 0 < v) (mask : Nat) (hmask : mask < 64) :
    (∑ rank : Fin codeCardinality,
      subsetSign mask * (avoidanceA (decodedCodeword rank) mask : Int) ^ v *
        (avoidanceD (decodedCodeword rank) mask : Int) ^ (m - v)) =
      ∑ a : requirementsOfMask mask → Fin 8,
        (Fintype.card (FixedRank (requirementsOfMask mask) a) : Int) * maskedMoment m v mask a := by
  classical
  apply sum_rank_eq_masked (requirementsOfMask mask) _ (maskedMoment m v mask)
  · intro rank
    unfold maskedMoment
    have hf := positiveProjection_fixed (requirementsOfMask mask) rank
    rw [avoidanceA_eq_compositionFormula,
      maskedBound_of_fixed (decodedCodeword rank.val) mask _ hf,
      avoidanceD_of_fixed (decodedCodeword rank.val) mask hmask _ hf]
  · intro rank hnot
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    have hzero : ((decodedCodeword rank).depth j.val).val = 0 := by omega
    have hm : mask.testBit j.val.val = true := (Finset.mem_filter.mp j.property).2
    have ha := avoidanceA_zero_of_zero (decodedCodeword rank) mask j.val hm hzero
    simp only [ha, Nat.cast_zero, zero_pow (Nat.ne_of_gt hv), mul_zero, zero_mul]

noncomputable def groupedNumerator (m v : Nat) : Int :=
  ∑ mask : Fin 63, ∑ a : requirementsOfMask mask.val → Fin 8,
    if assignmentSum (requirementsOfMask mask.val) a ≤ 16 then
      (boundedTupleCount (Fintype.card (FreePositions (requirementsOfMask mask.val)))
        (16 - assignmentSum (requirementsOfMask mask.val) a) (fun _ => 9) : Int) *
          maskedMoment m v mask.val a
    else 0

theorem localNumerator_eq_grouped (m v : Nat) (hv : 0 < v) :
    localNumerator m v = groupedNumerator m v := by
  classical
  unfold localNumerator
  rw [Finset.sum_comm, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hfull : (∑ rank : Fin codeCardinality,
      subsetSign 63 * (avoidanceA (decodedCodeword rank) 63 : Int) ^ v *
        (avoidanceD (decodedCodeword rank) 63 : Int) ^ (m - v)) = 0 := by
    simp only [avoidanceA_full, Nat.cast_zero, zero_pow (Nat.ne_of_gt hv),
      mul_zero, zero_mul, Finset.sum_const_zero]
  rw [hfull, add_zero]
  unfold groupedNumerator
  apply Finset.sum_congr rfl
  intro mask _
  rw [localMoment_regrouped m v hv mask.val (Nat.lt_trans mask.isLt (by decide))]
  apply Finset.sum_congr rfl
  intro a _
  rw [fixedRank_card]
  split_ifs <;> simp only [Nat.cast_zero, zero_mul]

def completionFormula (r t : Nat) : Int :=
  (fastResidualCount r t 0 : Int) - (r : Int) * (fastResidualCount r t 9 : Int)

theorem boundedTupleCount_nine (r t : Nat) (ht : t ≤ 16) :
    (boundedTupleCount r t (fun _ => 9) : Int) =
      (residualCount r t 0 : Int) - (r : Int) * (residualCount r t 9 : Int) := by
  classical
  let f : Finset (Fin r) → Int := fun T =>
    (-1 : Int) ^ T.card * (residualCount r t (boundSum (fun _ => 9) T) : Int)
  let singles : Finset (Finset (Fin r)) := Finset.univ.image (fun j => ({j} : Finset (Fin r)))
  let allowed := insert (∅ : Finset (Fin r)) singles
  have hsub : allowed ⊆ (Finset.univ : Finset (Fin r)).powerset := by
    intro T _
    exact Finset.mem_powerset.mpr (Finset.subset_univ T)
  have hrest : ∀ T ∈ (Finset.univ : Finset (Fin r)).powerset, T ∉ allowed → f T = 0 := by
    intro T _ hnot
    have hzero : T.card ≠ 0 := by
      intro h
      have heq : T = ∅ := Finset.card_eq_zero.mp h
      apply hnot
      rw [heq]
      exact Finset.mem_insert_self _ _
    have hone : T.card ≠ 1 := by
      intro h
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h
      exact hnot (by simp [allowed, singles])
    have hcard : 2 ≤ T.card := by omega
    have hsum : boundSum (fun _ : Fin r => 9) T = 9 * T.card := by
      simp [boundSum, Nat.mul_comm]
    have hlarge : ¬boundSum (fun _ : Fin r => 9) T ≤ t := by rw [hsum]; omega
    simp only [f, residualCount, if_neg hlarge, Nat.cast_zero, mul_zero]
  have hempty : (∅ : Finset (Fin r)) ∉ singles := by simp [singles]
  have hfempty : f ∅ = (residualCount r t 0 : Int) := by simp [f, boundSum]
  have hfsingle (j : Fin r) : f {j} = -(residualCount r t 9 : Int) := by simp [f, boundSum]
  have hsingles : (∑ T ∈ singles, f T) = -(r : Int) * (residualCount r t 9 : Int) := by
    unfold singles
    rw [Finset.sum_image (fun _ _ _ _ h => Finset.singleton_injective h)]
    simp only [hfsingle, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [boundedTupleCount_eq]
  change (∑ T ∈ (Finset.univ : Finset (Fin r)).powerset, f T) = _
  rw [← Finset.sum_subset hsub hrest]
  change (∑ T ∈ insert (∅ : Finset (Fin r)) singles, f T) = _
  rw [Finset.sum_insert hempty, hfempty, hsingles]
  ring

theorem completionFormula_eq_count (r t : Nat) (ht : t ≤ 16) :
    completionFormula r t = (boundedTupleCount r t (fun _ => 9) : Int) := by
  rw [boundedTupleCount_nine r t ht]
  simp only [completionFormula, fastResidualCount_eq]

/-- Guards precede the costly moment: impossible assignments and zero-completion
states do not evaluate either bounded-composition moment factor. -/
def guardedNumerator (m v : Nat) : Int :=
  ∑ mask : Fin 63, ∑ a : requirementsOfMask mask.val → Fin 8,
    if assignmentSum (requirementsOfMask mask.val) a ≤ 16 then
      let completions := completionFormula
        (Fintype.card (FreePositions (requirementsOfMask mask.val)))
        (16 - assignmentSum (requirementsOfMask mask.val) a)
      if completions = 0 then 0 else completions * maskedMoment m v mask.val a
    else 0

theorem groupedNumerator_eq_guarded (m v : Nat) : groupedNumerator m v = guardedNumerator m v := by
  classical
  unfold groupedNumerator guardedNumerator
  apply Finset.sum_congr rfl
  intro mask _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hsum : assignmentSum (requirementsOfMask mask.val) a ≤ 16
  · simp only [if_pos hsum]
    rw [← completionFormula_eq_count _ _ (Nat.sub_le _ _)]
    split_ifs with hzero
    · simp only [hzero, zero_mul]
    · rfl
  · simp only [if_neg hsum]

theorem localNumerator_eq_guarded (m v : Nat) (hv : 0 < v) :
    localNumerator m v = guardedNumerator m v :=
  (localNumerator_eq_grouped m v hv).trans (groupedNumerator_eq_guarded m v)

def localCapCheck (m v cap : Nat) : Bool :=
  decide (guardedNumerator m v * 1000000 ≤
    (cap : Int) * (15597 ^ (m + 1) * 31 ^ (m - v) : Nat))

theorem localSuccessNumerator_one (targetSlot : Slot) (rank : Fin codeCardinality) :
    localSuccessNumerator targetSlot (decodedCodeword rank) 1 0 = 1 := by
  let single : LocalTuple (Fin codeCardinality) (DifferentHistory targetSlot) 1 0 :=
    ((fun _ => rank), fun i => Fin.elim0 i)
  have hset : localCoveredSet 1 0 (sameSlotSupply (decodedCodeword rank))
      (differentSlotSupply targetSlot (decodedCodeword rank)) = {single} := by
    ext sample
    rw [localCoveredSet_mem]
    simp only [Finset.mem_singleton]
    constructor
    · intro hcovered
      have hdepth : ∀ requirement : CodePosition,
          ((decodedCodeword rank).depth requirement).val ≤
            ((decodedCodeword (sample.1 0)).depth requirement).val := by
        intro requirement
        rcases hcovered requirement with ⟨i, hi⟩ | ⟨i, _⟩
        · have hi0 : i = 0 := Subsingleton.elim _ _
          simpa only [hi0, sameSlotSupply, decide_eq_true_eq] using hi
        · exact Fin.elim0 i
      have hword := Codeword.eq_of_coordinatewise_le _ _ hdepth
      have hrank : sample.1 0 = rank := decodedCodeword_injective hword.symm
      apply Prod.ext
      · funext i
        change sample.1 i = rank
        have hi0 : i = 0 := Subsingleton.elim _ _
        simpa only [hi0] using hrank
      · funext i
        exact Fin.elim0 i
    · rintro rfl requirement
      left
      refine ⟨0, ?_⟩
      change decide (((decodedCodeword rank).depth requirement).val ≤
        ((decodedCodeword rank).depth requirement).val) = true
      exact decide_eq_true (Nat.le_refl _)
  unfold localSuccessNumerator
  rw [hset, Finset.card_singleton]

theorem localConditionalCount_one (targetSlot : Slot) :
    localConditionalCount targetSlot 1 1 = codeCardinality := by
  simp [localConditionalCount, localSuccessNumerator_one]

theorem localCover_one_one : localCover 1 1 = (1 : Rat) / 15597 := by
  rw [localCover_event_count (0 : Slot) 1 1 (by decide) (by decide),
    localConditionalCount_one, codeCardinality_eq]
  norm_num

theorem localCover_le_cap (m v cap : Nat) (hv : 0 < v) (hvalid : v ≤ m)
    (hnum : groupedNumerator m v * 1000000 ≤
      (cap : Int) * (15597 ^ (m + 1) * 31 ^ (m - v) : Nat)) :
    localCover m v ≤ (cap : Rat) / 1000000 := by
  have hzero : ¬(v = 0 ∨ m < v) := by omega
  have hden : (0 : Rat) < (15597 ^ (m + 1) * 31 ^ (m - v) : Nat) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by decide : 0 < (15597 : Nat)))
      (Nat.pow_pos (by decide : 0 < (31 : Nat)))
  rw [localCover, if_neg hzero, localNumerator_eq_grouped m v hv]
  apply (div_le_div_iff₀ hden (by norm_num : (0 : Rat) < 1000000)).mpr
  exact_mod_cast hnum

theorem localCapCheck_sound (m v cap : Nat) (hv : 0 < v) (hvalid : v ≤ m)
    (hcheck : localCapCheck m v cap = true) : localCover m v ≤ (cap : Rat) / 1000000 := by
  apply localCover_le_cap m v cap hv hvalid
  rw [groupedNumerator_eq_guarded]
  exact of_decide_eq_true hcheck

theorem localCover_le_localUpper_of_cases
    (hcases : ∀ m v : Nat, 2 ≤ m → m ≤ 6 → 0 < v → v ≤ m →
      localCover m v ≤ ((caps[m]?.getD [])[v - 1]?.getD 0 : Rat) / 1000000) :
    ∀ m v, localCover m v ≤ localUpper m v := by
  intro m v
  by_cases hzero : v = 0 ∨ m < v
  · simp only [localCover, localUpper, if_pos hzero, le_refl]
  · have hv : 0 < v := by omega
    have hvalid : v ≤ m := by omega
    by_cases hm : m = 1
    · have heq : v = 1 := by omega
      subst m
      subst v
      simpa [localUpper] using localCover_one_one.le
    · by_cases hsmall : m ≤ 6
      · simpa only [localUpper, if_neg hzero, if_neg hm, if_pos hsmall] using
          hcases m v (by omega) hsmall hv hvalid
      · simpa only [localUpper, if_neg hzero, if_neg hm, if_neg hsmall] using
          localCover_le_one m v

end PoissonDAG.GRSCC.Small
