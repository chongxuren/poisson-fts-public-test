import PoissonDAG.Constructions.GRSCC.Graph
import Mathlib.Data.Nat.Bitwise

/-!
# Finite local slot/profile law

The exact XOR bijection reduces every target slot to zero. Small closed scalar
checks classify first divergence, while a generic disjoint-indicator argument
handles arbitrary Boolean profiles without enumerating functions. Isolating
these proofs allows their compiled result to be reused by later count proofs.
-/

namespace PoissonDAG.GRSCC

/-- First divergence of two five-bit leaf paths, numbered from the root. -/
def divergesAt (target history : Slot) (depth : Depth) : Bool :=
  decide (history.val / 2 ^ (5 - depth.val) = target.val / 2 ^ (5 - depth.val) ∧
    history.val / 2 ^ (4 - depth.val) ≠ target.val / 2 ^ (4 - depth.val))

def guardPosition : CodePosition := ⟨5, by decide⟩
def depthPosition (depth : Depth) : CodePosition := ⟨depth.val, by have h := depth.isLt; omega⟩

def coordinateSupply (target history : Slot) (profile : CodePosition → Bool)
    (requirement : CodePosition) : Bool :=
  if hd : requirement.val < 5 then
    let depth : Depth := ⟨requirement.val, hd⟩
    divergesAt target history depth ||
      (decide (history.val / 2 ^ (4 - depth.val) = target.val / 2 ^ (4 - depth.val)) &&
        profile requirement)
  else decide (target = history) && profile requirement

def differentProfileAvoidance (target : Slot) (mask : Fin 64)
    (profile : CodePosition → Bool) : Nat :=
  (Finset.univ.filter (fun history : Slot => history ≠ target ∧
    ∀ requirement : CodePosition, mask.val.testBit requirement.val = true →
      coordinateSupply target history profile requirement = false)).card

set_option maxRecDepth 100000 in
theorem slotXor_bound : ∀ left right : Slot, (left.val ^^^ right.val) < 32 := by
  decide +kernel

def slotXor (left right : Slot) : Slot :=
  ⟨left.val ^^^ right.val, slotXor_bound left right⟩

theorem slotXor_cancel (left right : Slot) : slotXor left (slotXor left right) = right := by
  apply Fin.ext
  simp [slotXor, Nat.xor_xor_cancel_left]

set_option maxRecDepth 100000 in
theorem slotXor_nonzero : ∀ left right : Slot,
    slotXor left right ≠ 0 ↔ right ≠ left := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem coordinateSupply_xor_bit : ∀ (target history : Slot)
    (requirement : CodePosition) (bit : Bool),
    coordinateSupply target history (fun _ => bit) requirement =
      coordinateSupply 0 (slotXor target history) (fun _ => bit) requirement := by
  decide +kernel

theorem coordinateSupply_xor (target history : Slot) (profile : CodePosition → Bool)
    (requirement : CodePosition) :
    coordinateSupply target history profile requirement =
      coordinateSupply 0 (slotXor target history) profile requirement := by
  have h := coordinateSupply_xor_bit target history requirement (profile requirement)
  simpa only [coordinateSupply] using h

def differentProfileAvoidanceEquiv (target : Slot) (mask : Fin 64)
    (profile : CodePosition → Bool) :
    {history : Slot // history ≠ target ∧ ∀ requirement : CodePosition,
      mask.val.testBit requirement.val = true →
        coordinateSupply target history profile requirement = false} ≃
    {history : Slot // history ≠ 0 ∧ ∀ requirement : CodePosition,
      mask.val.testBit requirement.val = true →
        coordinateSupply 0 history profile requirement = false} where
  toFun history := ⟨slotXor target history.val, by
    refine ⟨(slotXor_nonzero target history.val).mpr history.property.1, ?_⟩
    intro requirement hmask
    rw [← coordinateSupply_xor]
    exact history.property.2 requirement hmask⟩
  invFun history := ⟨slotXor target history.val, by
    refine ⟨?_, ?_⟩
    · apply (slotXor_nonzero target (slotXor target history.val)).mp
      rw [slotXor_cancel]
      exact history.property.1
    · intro requirement hmask
      rw [coordinateSupply_xor, slotXor_cancel]
      exact history.property.2 requirement hmask⟩
  left_inv history := by apply Subtype.ext; exact slotXor_cancel target history.val
  right_inv history := by apply Subtype.ext; exact slotXor_cancel target history.val

theorem differentProfileAvoidance_target_zero (target : Slot) (mask : Fin 64)
    (profile : CodePosition → Bool) :
    differentProfileAvoidance target mask profile = differentProfileAvoidance 0 mask profile := by
  have h := Fintype.card_congr (differentProfileAvoidanceEquiv target mask profile)
  simpa only [differentProfileAvoidance, Fintype.card_subtype] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem divergence_class_count : ∀ (target : Slot) (depth : Depth),
    ((List.finRange 32).filter (fun history => divergesAt target history depth)).length =
      2 ^ (4 - depth.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem divergence_partition : ∀ (target history : Slot), target ≠ history →
    ∃! depth : Depth, divergesAt target history depth = true := by
  unfold ExistsUnique
  decide +kernel

set_option maxHeartbeats 10000000 in
theorem mask_prefix_membership : ∀ (mask : Fin 64) (depth : Depth) (requirement : CodePosition),
    (mask.val % 2 ^ depth.val).testBit requirement.val =
      (mask.val.testBit requirement.val && decide (requirement.val < depth.val)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem coordinateSupply_at_zero_divergence_bit : ∀ (history : Slot) (depth : Depth)
    (requirement : CodePosition) (bit : Bool),
    divergesAt 0 history depth = true →
      coordinateSupply 0 history (fun _ => bit) requirement =
        if requirement.val < depth.val then bit else decide (requirement.val = depth.val) := by
  decide +kernel

theorem coordinateSupply_at_zero_divergence (history : Slot) (depth : Depth)
    (profile : CodePosition → Bool) (requirement : CodePosition)
    (hdiv : divergesAt 0 history depth = true) :
    coordinateSupply 0 history profile requirement =
      if requirement.val < depth.val then profile requirement
      else decide (requirement.val = depth.val) := by
  have h := coordinateSupply_at_zero_divergence_bit history depth requirement
    (profile requirement) hdiv
  simpa only [coordinateSupply] using h

def profileDepthAllowed (mask : Fin 64) (profile : CodePosition → Bool) (depth : Depth) : Prop :=
  mask.val.testBit depth.val = false ∧ ∀ requirement : CodePosition,
    (mask.val % 2 ^ depth.val).testBit requirement.val = true → profile requirement = false

instance profileDepthAllowed_decidable (mask : Fin 64) (profile : CodePosition → Bool)
    (depth : Depth) : Decidable (profileDepthAllowed mask profile depth) := by
  unfold profileDepthAllowed
  infer_instance

theorem profile_avoidance_at_zero_divergence (history : Slot) (depth : Depth)
    (mask : Fin 64) (profile : CodePosition → Bool)
    (hdiv : divergesAt 0 history depth = true) :
    (∀ requirement : CodePosition, mask.val.testBit requirement.val = true →
      coordinateSupply 0 history profile requirement = false) ↔
      profileDepthAllowed mask profile depth := by
  have hlaw := coordinateSupply_at_zero_divergence history depth profile
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · cases hmask : mask.val.testBit depth.val with
      | false => rfl
      | true =>
        have hc := h (depthPosition depth) (by simpa [depthPosition] using hmask)
        rw [hlaw _ hdiv] at hc
        simp [depthPosition] at hc
    · intro requirement hprefix
      rw [mask_prefix_membership] at hprefix
      obtain ⟨hmask, hlt⟩ := Bool.and_eq_true_iff.mp hprefix
      have hlt' : requirement.val < depth.val := of_decide_eq_true hlt
      have hc := h requirement hmask
      rw [hlaw _ hdiv, if_pos hlt'] at hc
      exact hc
  · intro h requirement hmask
    rw [hlaw _ hdiv]
    by_cases hlt : requirement.val < depth.val
    · rw [if_pos hlt]
      apply h.2 requirement
      rw [mask_prefix_membership]
      exact Bool.and_eq_true_iff.mpr ⟨hmask, decide_eq_true hlt⟩
    · rw [if_neg hlt]
      have hne : requirement.val ≠ depth.val := by
        intro heq
        rw [heq, h.1] at hmask
        contradiction
      simp [hne]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem divergence_class_card : ∀ (target : Slot) (depth : Depth),
    (Finset.univ.filter (fun history => divergesAt target history depth = true)).card =
      2 ^ (4 - depth.val) := by
  decide +kernel

theorem profile_indicator_sum (history : Slot) (mask : Fin 64)
    (profile : CodePosition → Bool) :
    (∑ depth : Depth, if divergesAt 0 history depth = true ∧
      profileDepthAllowed mask profile depth then (1 : Nat) else 0) =
      if history ≠ 0 ∧ (∀ requirement : CodePosition,
        mask.val.testBit requirement.val = true →
          coordinateSupply 0 history profile requirement = false) then 1 else 0 := by
  by_cases hz : history = 0
  · subst history
    simp [divergesAt]
  · obtain ⟨depth, hdepth, hunique⟩ := divergence_partition (0 : Slot) history (Ne.symm hz)
    rw [Finset.sum_eq_single depth]
    · simp [hz, hdepth, profile_avoidance_at_zero_divergence history depth mask profile hdepth]
    · intro other _ hne
      have hnot : ¬divergesAt 0 history other = true := by
        intro ho
        exact hne (hunique other ho)
      simp [hnot]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ depth))

theorem different_profile_avoidance_count_zero (mask : Fin 64)
    (profile : CodePosition → Bool) :
    differentProfileAvoidance 0 mask profile =
      ((List.finRange 5).map (fun depth =>
        if mask.val.testBit depth.val then 0
        else if (∀ requirement : CodePosition,
            (mask.val % 2 ^ depth.val).testBit requirement.val = true →
              profile requirement = false) then 2 ^ (4 - depth.val) else 0)).sum := by
  classical
  calc
    _ = ∑ history : Slot, if history ≠ 0 ∧ (∀ requirement : CodePosition,
        mask.val.testBit requirement.val = true →
          coordinateSupply 0 history profile requirement = false) then 1 else 0 := by
      rw [Finset.sum_boole]
      rfl
    _ = ∑ history : Slot, ∑ depth : Depth,
        if divergesAt 0 history depth = true ∧ profileDepthAllowed mask profile depth
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro history _
      exact (profile_indicator_sum history mask profile).symm
    _ = ∑ depth : Depth, if profileDepthAllowed mask profile depth
        then 2 ^ (4 - depth.val) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro depth _
      by_cases ha : profileDepthAllowed mask profile depth
      · simp only [ha, and_true, if_true]
        rw [Finset.sum_boole, divergence_class_card]
        push_cast
        rfl
      · simp [ha]
    _ = _ := by
      rw [← List.sum_toFinset _ (List.nodup_finRange 5), List.toFinset_finRange]
      apply Finset.sum_congr rfl
      intro depth _
      cases hmask : mask.val.testBit depth.val <;> simp [profileDepthAllowed, hmask]

theorem different_profile_avoidance_count (target : Slot) (mask : Fin 64)
    (profile : CodePosition → Bool) :
    differentProfileAvoidance target mask profile =
      ((List.finRange 5).map (fun depth =>
        if mask.val.testBit depth.val then 0
        else if (∀ requirement : CodePosition,
            (mask.val % 2 ^ depth.val).testBit requirement.val = true →
              profile requirement = false) then 2 ^ (4 - depth.val) else 0)).sum := by
  rw [differentProfileAvoidance_target_zero]
  exact different_profile_avoidance_count_zero mask profile

end PoissonDAG.GRSCC
