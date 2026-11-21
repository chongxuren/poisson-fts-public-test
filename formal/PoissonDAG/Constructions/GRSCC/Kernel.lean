import PoissonDAG.Constructions.GRSCC.Codebook
import PoissonDAG.Constructions.GRSCC.SupplyProfile
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.Order.Field.Basic

set_option maxHeartbeats 50000

/-!
# Literal finite avoidance counts and the joint layer recurrence

The codebook is generated from six coordinates in `[0,8]` of ordinary sum 16.
Neither a supplied probability function nor historical numeric coefficients
are inputs to these definitions. The recurrence preserves the common history
count and the dependence between current and next target-owner counts.

These are finite definitions of the source equations, not a theorem identifying
them with `Scheme.coverCoefficient`. In particular, no security conclusion is
exported until the pooled-closure/counting bridge is proved.
-/
namespace PoissonDAG.GRSCC

def localCodebook : List (List Nat) := codebook 6 16

/-- Explicit finite bijection behind the iid avoidance powers. No probability
axiom is needed: every coordinate independently ranges over the same allowed
finite set. -/
def restrictedTupleEquiv (α : Type) (n : Nat) (allowed : α → Prop) :
    {f : Fin n → α // ∀ i, allowed (f i)} ≃ (Fin n → {x : α // allowed x}) where
  toFun f i := ⟨f.val i, f.property i⟩
  invFun g := ⟨fun i => (g i).val, fun i => (g i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem restrictedTuple_card (α : Type) [Fintype α] (n : Nat)
    (allowed : α → Prop) [DecidablePred allowed] :
    Fintype.card {f : Fin n → α // ∀ i, allowed (f i)} =
      Fintype.card {x : α // allowed x} ^ n := by
  rw [Fintype.card_congr (restrictedTupleEquiv α n allowed)]
  simp

theorem mem_finite_inf {I X : Type} [DecidableEq I] [Fintype X] [DecidableEq X]
    (requirements : Finset I) (sets : I → Finset X) (x : X) :
    x ∈ requirements.inf sets ↔ ∀ j ∈ requirements, x ∈ sets j := by
  induction requirements using Finset.induction_on with
  | empty => simp
  | @insert j requirements hj ih => simp [Finset.inf_insert, Finset.inf_eq_inter, ih]

abbrev LocalTuple (A B : Type) (v w : Nat) := (Fin v → A) × (Fin w → B)

def avoidanceSet {A : Type} [Fintype A] [DecidableEq A]
    (supply : A → CodePosition → Bool) (requirements : Finset CodePosition) : Finset A :=
  Finset.univ.filter (fun x => ∀ j ∈ requirements, supply x j = false)

def missingSet {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (v w : Nat) (supplyA : A → CodePosition → Bool) (supplyB : B → CodePosition → Bool)
    (requirement : CodePosition) : Finset (LocalTuple A B v w) :=
  Finset.univ.filter (fun h => (∀ i, supplyA (h.1 i) requirement = false) ∧
    (∀ i, supplyB (h.2 i) requirement = false))

def localCoveredSet {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (v w : Nat) (supplyA : A → CodePosition → Bool) (supplyB : B → CodePosition → Bool) :
    Finset (LocalTuple A B v w) :=
  Finset.univ.inf (fun requirement => (missingSet v w supplyA supplyB requirement)ᶜ)

theorem localCoveredSet_mem {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (v w : Nat)
    (supplyA : A → CodePosition → Bool) (supplyB : B → CodePosition → Bool)
    (sample : LocalTuple A B v w) :
    sample ∈ localCoveredSet v w supplyA supplyB ↔
      ∀ requirement : CodePosition,
        (∃ i, supplyA (sample.1 i) requirement = true) ∨
        (∃ i, supplyB (sample.2 i) requirement = true) := by
  simp [localCoveredSet, mem_finite_inf, missingSet, not_and_or, not_forall]
  constructor
  · intro h requirement
    by_cases ha : ∃ i, supplyA (sample.1 i) requirement = true
    · exact Or.inl ha
    · right
      apply h requirement
      intro i
      cases hc : supplyA (sample.1 i) requirement with
      | false => rfl
      | true => exact False.elim (ha ⟨i, hc⟩)
  · intro h requirement ha
    rcases h requirement with ⟨i, hi⟩ | hb
    · have hf := ha i
      rw [hf] at hi
      contradiction
    · exact hb

def missingIntersectionEquiv {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (v w : Nat)
    (supplyA : A → CodePosition → Bool) (supplyB : B → CodePosition → Bool)
    (requirements : Finset CodePosition) :
    {h : LocalTuple A B v w // h ∈ requirements.inf (missingSet v w supplyA supplyB)} ≃
      (Fin v → {x : A // x ∈ avoidanceSet supplyA requirements}) ×
      (Fin w → {x : B // x ∈ avoidanceSet supplyB requirements}) where
  toFun h := (fun i => ⟨h.val.1 i, by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro j hj
    have hm := (mem_finite_inf requirements _ h.val).mp h.property j hj
    exact (Finset.mem_filter.mp hm).2.1 i⟩,
    fun i => ⟨h.val.2 i, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      have hm := (mem_finite_inf requirements _ h.val).mp h.property j hj
      exact (Finset.mem_filter.mp hm).2.2 i⟩)
  invFun h := ⟨(fun i => (h.1 i).val, fun i => (h.2 i).val), by
    apply (mem_finite_inf requirements _ _).mpr
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    constructor
    · intro i
      exact (Finset.mem_filter.mp (h.1 i).property).2 j hj
    · intro i
      exact (Finset.mem_filter.mp (h.2 i).property).2 j hj⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem missingIntersection_card {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (v w : Nat)
    (supplyA : A → CodePosition → Bool) (supplyB : B → CodePosition → Bool)
    (requirements : Finset CodePosition) :
    (requirements.inf (missingSet v w supplyA supplyB)).card =
      (avoidanceSet supplyA requirements).card ^ v *
        (avoidanceSet supplyB requirements).card ^ w := by
  have h := Fintype.card_congr (missingIntersectionEquiv v w supplyA supplyB requirements)
  simpa using h

/-- Exact finite inclusion-exclusion and iid cardinality powers. This is the
local counting theorem; instantiation still needs the actual same-slot and
different-slot avoidance cardinalities `A_e(S)` and `D_e(S)`. -/
theorem local_inclusion_exclusion {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (v w : Nat)
    (supplyA : A → CodePosition → Bool) (supplyB : B → CodePosition → Bool) :
    ((localCoveredSet v w supplyA supplyB).card : Int) =
      ∑ requirements ∈ (Finset.univ : Finset CodePosition).powerset,
        (-1 : Int) ^ requirements.card *
          ((avoidanceSet supplyA requirements).card : Int) ^ v *
            ((avoidanceSet supplyB requirements).card : Int) ^ w := by
  unfold localCoveredSet
  rw [Finset.inclusion_exclusion_card_inf_compl]
  apply Finset.sum_congr rfl
  intro requirements _
  rw [missingIntersection_card]
  push_cast
  ring

/-- Ordinary constant-sum words form an antichain under coordinatewise
forward-chain coverage. In particular one same-slot history can cover all
six openings only when its depth word equals the target's depth word. -/
theorem Codeword.eq_of_coordinatewise_le (e f : Codeword)
    (h : ∀ j, (e.depth j).val ≤ (f.depth j).val) : e = f := by
  have hdepth : e.depth = f.depth := by
    funext j
    apply Fin.ext
    by_contra hne
    have hlt : (e.depth j).val < (f.depth j).val := by
      have hj := h j
      omega
    have hsum : (Finset.univ.sum (fun i => (e.depth i).val)) <
        Finset.univ.sum (fun i => (f.depth i).val) :=
      Finset.sum_lt_sum (fun i _ => h i) ⟨j, Finset.mem_univ j, hlt⟩
    rw [e.sum_eq, f.sum_eq] at hsum
    omega
  cases e
  cases f
  cases hdepth
  rfl

def coordinate (word : List Nat) (index : Nat) : Nat := word[index]?.getD 0

def requirementsOfMask (mask : Nat) : Finset CodePosition :=
  Finset.univ.filter (fun j => mask.testBit j.val)

def sameSlotSupply (target : Codeword) (history : Fin codeCardinality)
    (requirement : CodePosition) : Bool :=
  decide ((target.depth requirement).val ≤ ((decodedCodeword history).depth requirement).val)

abbrev LayerSample (q : Nat) :=
  Slot × (Fin codeCardinality × ((Fin q → Slot) × (Fin q → Fin codeCardinality)))

def localLayerEvent {q : Nat} (current : Finset (Fin q)) (sample : LayerSample q) : Prop :=
  ∀ requirement : CodePosition, ∃ i ∈ current,
    coordinateSupply sample.1 (sample.2.2.1 i)
      (sameSlotSupply (decodedCodeword sample.2.1) (sample.2.2.2 i)) requirement = true

instance localLayerEvent_decidable {q : Nat} (current : Finset (Fin q))
    (sample : LayerSample q) : Decidable (localLayerEvent current sample) := by
  unfold localLayerEvent
  infer_instance

def nextOwnerCount {q : Nat} (sample : LayerSample q) : Nat :=
  (Finset.univ.filter (fun i : Fin q => sample.2.2.1 i = sample.1)).card

/-- Entire finite conditional layer experiment: target slot/code and every
history slot/code are independently uniform. `current` records the actual
current-owner subset; its identity is retained until the count theorem. -/
def layerTransitionCoefficient {q : Nat} (current : Finset (Fin q)) (next : Nat) : Rat :=
  (((Finset.univ : Finset (LayerSample q)).filter (fun sample =>
      localLayerEvent current sample ∧ nextOwnerCount sample = next)).card : Rat) /
    (Fintype.card (LayerSample q) : Rat)

/-- Number of canonical same-slot codewords avoiding every masked requirement.
The canonical decoder is bijective by `decodedCodeword_injective/surjective`. -/
def avoidanceA (target : Codeword) (mask : Nat) : Nat :=
  (avoidanceSet (sameSlotSupply target) (requirementsOfMask mask)).card

abbrev DifferentHistory (target : Slot) := {history : Slot // history ≠ target} × Fin codeCardinality

def differentSlotSupply (targetSlot : Slot) (target : Codeword)
    (history : DifferentHistory targetSlot) (requirement : CodePosition) : Bool :=
  coordinateSupply targetSlot history.1.val (sameSlotSupply target history.2) requirement

theorem masked_avoidance_iff (target : Codeword) (mask : Nat) (history : Fin codeCardinality) :
    history ∈ avoidanceSet (sameSlotSupply target) (requirementsOfMask mask) ↔
      ∀ requirement : CodePosition, mask.testBit requirement.val = true →
        sameSlotSupply target history requirement = false := by
  simp [avoidanceSet, requirementsOfMask]

def differentAvoidanceEquiv (targetSlot : Slot) (target : Codeword) (mask : Fin 64) :
    {h : DifferentHistory targetSlot //
      h ∈ avoidanceSet (differentSlotSupply targetSlot target) (requirementsOfMask mask.val)} ≃
      Σ rank : Fin codeCardinality, {history : Slot // history ≠ targetSlot ∧
        ∀ requirement : CodePosition, mask.val.testBit requirement.val = true →
          coordinateSupply targetSlot history (sameSlotSupply target rank) requirement = false} where
  toFun h := ⟨h.val.2, h.val.1.val, h.val.1.property, by
    intro requirement hm
    have hi : requirement ∈ requirementsOfMask mask.val := by simp [requirementsOfMask, hm]
    exact (Finset.mem_filter.mp h.property).2 requirement hi⟩
  invFun h := ⟨(⟨h.2.val, h.2.property.1⟩, h.1), by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro requirement hi
    exact h.2.property.2 requirement (Finset.mem_filter.mp hi).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem different_avoidance_card_sum (targetSlot : Slot) (target : Codeword) (mask : Fin 64) :
    (avoidanceSet (differentSlotSupply targetSlot target) (requirementsOfMask mask.val)).card =
      ∑ rank : Fin codeCardinality,
        differentProfileAvoidance targetSlot mask (sameSlotSupply target rank) := by
  have h := Fintype.card_congr (differentAvoidanceEquiv targetSlot target mask)
  rw [Fintype.card_coe, Fintype.card_sigma] at h
  simpa only [Fintype.card_subtype, differentProfileAvoidance] using h

theorem profile_prefix_sum (target : Codeword) (cutMask : Nat) (coefficient : Nat) :
    (∑ rank : Fin codeCardinality,
      if (∀ requirement : CodePosition, cutMask.testBit requirement.val = true →
        sameSlotSupply target rank requirement = false) then coefficient else 0) =
      coefficient * avoidanceA target cutMask := by
  calc
    _ = coefficient * ∑ rank : Fin codeCardinality,
        if (∀ requirement : CodePosition, cutMask.testBit requirement.val = true →
          sameSlotSupply target rank requirement = false) then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rank _
      split <;> simp_all
    _ = coefficient * avoidanceA target cutMask := by
      rw [Finset.sum_boole]
      simp [avoidanceA, avoidanceSet, requirementsOfMask]

/-- Number of different-slot choices avoiding every masked requirement.
There are exactly `2^(4-j)` slots first diverging from the target at depth j. -/
def avoidanceD (target : Codeword) (mask : Nat) : Nat :=
  ((List.finRange 5).map (fun depth =>
    if mask.testBit depth.val then 0
    else 2 ^ (4 - depth.val) * avoidanceA target (mask % 2 ^ depth.val))).sum

theorem different_avoidance_card (targetSlot : Slot) (target : Codeword) (mask : Fin 64) :
    (avoidanceSet (differentSlotSupply targetSlot target) (requirementsOfMask mask.val)).card =
      avoidanceD target mask.val := by
  rw [different_avoidance_card_sum]
  simp_rw [different_profile_avoidance_count]
  unfold avoidanceD
  simp only [← List.sum_toFinset _ (List.nodup_finRange 5), List.toFinset_finRange]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro depth _
  by_cases hm : mask.val.testBit depth.val = true
  · simp [hm]
  · simp only [if_neg hm]
    exact profile_prefix_sum target (mask.val % 2 ^ depth.val) (2 ^ (4 - depth.val))

def subsetSign (mask : Nat) : Int :=
  if ((List.range 6).filter mask.testBit).length % 2 = 0 then 1 else -1

set_option maxHeartbeats 10000000 in
theorem mask_requirements_injective : Function.Injective
    (fun mask : Fin 64 => requirementsOfMask mask.val) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
theorem mask_requirements_surjective : Function.Surjective
    (fun mask : Fin 64 => requirementsOfMask mask.val) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
theorem mask_sign_card : ∀ mask : Fin 64,
    subsetSign mask.val = (-1 : Int) ^ (requirementsOfMask mask.val).card := by
  decide +kernel

def localSuccessNumerator (targetSlot : Slot) (target : Codeword) (same different : Nat) : Nat :=
  (localCoveredSet same different (sameSlotSupply target)
    (differentSlotSupply targetSlot target)).card

theorem localSuccessNumerator_no_same (targetSlot : Slot) (target : Codeword)
    (different : Nat) : localSuccessNumerator targetSlot target 0 different = 0 := by
  unfold localSuccessNumerator
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro sample hmem
  have hguard := (localCoveredSet_mem 0 different (sameSlotSupply target)
    (differentSlotSupply targetSlot target) sample).mp hmem guardPosition
  rcases hguard with ⟨i, _⟩ | ⟨i, htrue⟩
  · exact Fin.elim0 i
  · have hn : targetSlot ≠ (sample.2 i).1.val := Ne.symm (sample.2 i).1.property
    simp [differentSlotSupply, coordinateSupply, guardPosition, hn] at htrue

theorem localSuccessNumerator_inclusion_exclusion (targetSlot : Slot) (target : Codeword)
    (same different : Nat) :
    (localSuccessNumerator targetSlot target same different : Int) =
      ∑ mask : Fin 64, subsetSign mask.val * (avoidanceA target mask.val : Int) ^ same *
        (avoidanceD target mask.val : Int) ^ different := by
  have hie := local_inclusion_exclusion same different
    (sameSlotSupply target) (differentSlotSupply targetSlot target)
  simp only [Finset.powerset_univ] at hie
  unfold localSuccessNumerator
  rw [hie]
  symm
  apply Fintype.sum_bijective (fun mask : Fin 64 => requirementsOfMask mask.val)
    ⟨mask_requirements_injective, mask_requirements_surjective⟩
  intro mask
  rw [mask_sign_card, different_avoidance_card]
  rfl

/-- Signed inclusion-exclusion numerator, before any rational division. -/
def localNumerator (incoming sameSlot : Nat) : Int :=
  ∑ target : Fin codeCardinality, ∑ mask : Fin 64,
    subsetSign mask.val * (avoidanceA (decodedCodeword target) mask.val : Int) ^ sameSlot *
      (avoidanceD (decodedCodeword target) mask.val : Int) ^ (incoming - sameSlot)

/-- Signed finite arithmetic is an actual nonnegative event count. This
discharges the local inclusion-exclusion interpretation, independently of
any historical checkpoint or supplied probability. -/
theorem localNumerator_as_event_count (targetSlot : Slot) (incoming sameSlot : Nat) :
    localNumerator incoming sameSlot =
      ∑ target : Fin codeCardinality,
        (localSuccessNumerator targetSlot (decodedCodeword target)
          sameSlot (incoming - sameSlot) : Int) := by
  unfold localNumerator
  apply Finset.sum_congr rfl
  intro target _
  exact (localSuccessNumerator_inclusion_exclusion targetSlot (decodedCodeword target)
    sameSlot (incoming - sameSlot)).symm

theorem localNumerator_nonnegative (incoming sameSlot : Nat) : 0 ≤ localNumerator incoming sameSlot := by
  rw [localNumerator_as_event_count (targetSlot := (0 : Slot))]
  exact Finset.sum_nonneg (fun _ _ => by omega)

def localCover (incoming sameSlot : Nat) : Rat :=
  if sameSlot = 0 ∨ incoming < sameSlot then 0
  else (localNumerator incoming sameSlot : Rat) /
    ((15597 ^ (incoming + 1) * 31 ^ (incoming - sameSlot) : Nat) : Rat)

def localConditionalCount (targetSlot : Slot) (incoming sameSlot : Nat) : Nat :=
  ∑ target : Fin codeCardinality,
    localSuccessNumerator targetSlot (decodedCodeword target) sameSlot (incoming - sameSlot)

theorem localConditionalCount_slot_independent (left right : Slot) (incoming sameSlot : Nat) :
    localConditionalCount left incoming sameSlot = localConditionalCount right incoming sameSlot := by
  have h := (localNumerator_as_event_count left incoming sameSlot).symm.trans
    (localNumerator_as_event_count right incoming sameSlot)
  have hcast : (localConditionalCount left incoming sameSlot : Int) =
      (localConditionalCount right incoming sameSlot : Int) := by
    simpa only [localConditionalCount, Nat.cast_sum] using h
  exact_mod_cast hcast

theorem localConditionalCount_no_same (targetSlot : Slot) (incoming : Nat) :
    localConditionalCount targetSlot incoming 0 = 0 := by
  simp [localConditionalCount, localSuccessNumerator_no_same]

theorem different_slot_card : ∀ target : Slot,
    Fintype.card {history : Slot // history ≠ target} = 31 := by
  decide +kernel

theorem localSuccessNumerator_bound (targetSlot : Slot) (target : Codeword)
    (same different : Nat) :
    localSuccessNumerator targetSlot target same different ≤
      codeCardinality ^ same * (31 * codeCardinality) ^ different := by
  have h := Finset.card_le_card (Finset.subset_univ
    (localCoveredSet same different (sameSlotSupply target)
      (differentSlotSupply targetSlot target)))
  simpa [localSuccessNumerator, LocalTuple, DifferentHistory,
    different_slot_card, Fintype.card_prod, Fintype.card_fun] using h

theorem localConditionalCount_bound (targetSlot : Slot) (incoming sameSlot : Nat)
    (hvalid : sameSlot ≤ incoming) :
    localConditionalCount targetSlot incoming sameSlot ≤
      15597 ^ (incoming + 1) * 31 ^ (incoming - sameSlot) := by
  have hexp : sameSlot + (incoming - sameSlot) = incoming := by omega
  calc
    _ ≤ ∑ _target : Fin codeCardinality,
        codeCardinality ^ sameSlot * (31 * codeCardinality) ^ (incoming - sameSlot) := by
      exact Finset.sum_le_sum (fun target _ => localSuccessNumerator_bound targetSlot
        (decodedCodeword target) sameSlot (incoming - sameSlot))
    _ = codeCardinality *
        (codeCardinality ^ sameSlot * (31 * codeCardinality) ^ (incoming - sameSlot)) := by simp
    _ = codeCardinality ^ (sameSlot + (incoming - sameSlot) + 1) *
        31 ^ (incoming - sameSlot) := by
      simp only [Nat.mul_pow, pow_add, pow_one]
      ring
    _ = 15597 ^ (incoming + 1) * 31 ^ (incoming - sameSlot) := by
      rw [hexp, codeCardinality_eq]

theorem localCover_event_count (targetSlot : Slot) (incoming sameSlot : Nat)
    (hpositive : 0 < sameSlot) (hvalid : sameSlot ≤ incoming) :
    localCover incoming sameSlot =
      (localConditionalCount targetSlot incoming sameSlot : Rat) /
        ((15597 ^ (incoming + 1) * 31 ^ (incoming - sameSlot) : Nat) : Rat) := by
  have hzero : ¬(sameSlot = 0 ∨ incoming < sameSlot) := by omega
  have hn : localNumerator incoming sameSlot =
      (localConditionalCount targetSlot incoming sameSlot : Int) := by
    rw [localNumerator_as_event_count (targetSlot := targetSlot)]
    simp only [localConditionalCount, Nat.cast_sum]
  have hr : (localNumerator incoming sameSlot : Rat) =
      (localConditionalCount targetSlot incoming sameSlot : Rat) := by
    exact_mod_cast hn
  rw [localCover, if_neg hzero]
  exact congrArg (fun numerator : Rat => numerator /
    ((15597 ^ (incoming + 1) * 31 ^ (incoming - sameSlot) : Nat) : Rat)) hr

theorem localCover_le_one (incoming sameSlot : Nat) : localCover incoming sameSlot ≤ 1 := by
  by_cases hzero : sameSlot = 0 ∨ incoming < sameSlot
  · simp [localCover, hzero]
  · have hs : 0 < sameSlot := by omega
    have hv : sameSlot ≤ incoming := by omega
    rw [localCover_event_count (0 : Slot) incoming sameSlot hs hv]
    have hd : (0 : Rat) < ((15597 ^ (incoming + 1) * 31 ^ (incoming - sameSlot) : Nat) : Rat) := by
      exact_mod_cast Nat.mul_pos (Nat.pow_pos (by decide : 0 < (15597 : Nat)))
        (Nat.pow_pos (by decide : 0 < (31 : Nat)))
    apply (div_le_one hd).mpr
    exact_mod_cast localConditionalCount_bound (0 : Slot) incoming sameSlot hv

def binomialMass (trials successes : Nat) (p : Rat) : Rat :=
  if successes ≤ trials then
    (Nat.choose trials successes : Rat) * p ^ successes * (1 - p) ^ (trials - successes)
  else 0

/-- A substochastic *joint-event* kernel once the local counting theorem has
been established. It does not multiply marginal layer-cover probabilities. -/
def jointKernel (q current next : Nat) : Rat :=
  ((List.range current).map (fun v0 =>
    let v := v0 + 1
    if v ≤ next then
      binomialMass current v ((1 : Rat) / 32) * localCover current v *
        binomialMass (q - current) (next - v) ((1 : Rat) / 32)
    else 0)).sum

def initialState (q : Nat) : List Rat :=
  (List.range q).map (fun j => binomialMass q (j + 1) ((1 : Rat) / 2))

def kernelStep (q : Nat) (state : List Rat) : List Rat :=
  (List.range q).map (fun k => ((List.range q).map (fun j =>
    (state[j]?.getD 0) * jointKernel q (j + 1) (k + 1))).sum)

def childCover (q : Nat) : Rat :=
  ((kernelStep q)^[7] (initialState q)).sum

def bucketThinned (q : Nat) : Rat :=
  ((List.range (q + 1)).map (fun j =>
    binomialMass q j ((1 : Rat) / 16) * childCover j)).sum

theorem localCover_no_supplier (incoming : Nat) : localCover incoming 0 = 0 := by
  simp [localCover]

theorem initialState_zero : initialState 0 = [] := rfl

theorem kernelStep_zero (state : List Rat) : kernelStep 0 state = [] := rfl

theorem childCover_zero : childCover 0 = 0 := by
  simp [childCover, initialState, kernelStep, Function.iterate_succ_apply]

theorem bucketThinned_zero : bucketThinned 0 = 0 := by
  simp [bucketThinned, childCover_zero]

end PoissonDAG.GRSCC
