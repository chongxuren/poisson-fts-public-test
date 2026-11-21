import PoissonDAG.Constructions.GRSCC.Transition
import PoissonDAG.Probability.SamplePaths
import PoissonDAG.Probability.UniformMatching
import PoissonDAG.Constructions.GRSCC.CountRecurrence

/-! # The seven dependent GRS-CC layers

The state retains the actual set of histories at the current owner. Only the
proved row-count theorem permits projecting that set to its cardinality.
-/

namespace PoissonDAG.GRSCC

open scoped BigOperators

def nextOwners {q : Nat} (sample : LayerSample q) : OwnerState q :=
  Finset.univ.filter (fun i => sample.2.2.1 i = sample.1)

def layerEvent {q : Nat} (state : OwnerState q) (sample : LayerSample q) : Bool :=
  decide (localLayerEvent state sample)

def layerKernel (q : Nat) : OwnerState q → OwnerState q → ℚ :=
  FiniteKernels.sampleKernel layerEvent nextOwners

theorem layerKernel_project_row {q : Nat} (source : OwnerState q) (target : OwnerCount q) :
    (∑ state, if ownerIndex state = target then layerKernel q source state else 0) =
      countKernel q (ownerIndex source) target := by
  rw [layerKernel, FiniteKernels.sample_project_row_count]
  have hset : (Finset.univ : Finset (LayerSample q)).filter
        (fun sample => layerEvent source sample = true ∧ ownerIndex (nextOwners sample) = target) =
      (Finset.univ : Finset (LayerSample q)).filter
        (fun sample => localLayerEvent source sample ∧ nextOwnerCount sample = target.val) := by
    ext sample
    simp [layerEvent, ownerIndex, nextOwners, nextOwnerCount, Fin.ext_iff]
  rw [hset]
  exact layerTransitionCoefficient_eq_jointKernel source target.val

theorem layerKernel_project_iterate {q : Nat} (mass : OwnerState q → ℚ) (n : Nat) :
    FiniteKernels.project ownerIndex ((FiniteKernels.step (layerKernel q))^[n] mass) =
      (FiniteKernels.step (countKernel q))^[n] (FiniteKernels.project ownerIndex mass) :=
  FiniteKernels.project_iterate ownerIndex (layerKernel q) (countKernel q)
    layerKernel_project_row mass n

abbrev InitialOwnerSample (q : Nat) := Fin 2 × (Fin q → Fin 2)

def initialOwners {q : Nat} (sample : InitialOwnerSample q) : OwnerState q :=
  Finset.univ.filter (fun i => sample.2 i = sample.1)

def initialOwnerMass (q : Nat) : OwnerState q → ℚ :=
  FiniteKernels.initialMass initialOwners

theorem initialOwnerMass_eq_uniform (q : Nat) : initialOwnerMass q = UniformMatching.mass 2 q := rfl

theorem initialOwnerMass_count {q : Nat} (count : OwnerCount q) :
    FiniteKernels.project ownerIndex (initialOwnerMass q) count =
      binomialMass q count.val ((1 : ℚ) / 2) := by
  have hk : count.val ≤ q := by have := count.isLt; omega
  have heq : FiniteKernels.project ownerIndex (initialOwnerMass q) count =
      UniformMatching.byCount 2 q count.val := by
    rw [initialOwnerMass_eq_uniform]
    unfold FiniteKernels.project UniformMatching.byCount
    apply Finset.sum_congr rfl
    intro subset hsubset
    simp only [ownerIndex, Fin.ext_iff]
  rw [heq]
  simpa [binomialMass, hk] using UniformMatching.byCount_eq_probability
    (m := 2) (by decide) q count.val hk

/-- A literal uniform experiment over initial owners and seven independent
layer-coordinate samples; every layer checks its actual evolving owner set. -/
def sevenLayerProbability (q : Nat) : ℚ :=
  (∑ initial : InitialOwnerSample q,
      FiniteKernels.pathProbability layerEvent nextOwners 7 (initialOwners initial)) /
    (Fintype.card (InitialOwnerSample q) : ℚ)

theorem sevenLayerProbability_nonnegative (q : Nat) : 0 ≤ sevenLayerProbability q := by
  unfold sevenLayerProbability
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => FiniteKernels.pathProbability_nonneg _ _ _ _)
  · positivity

theorem sevenLayerProbability_le_one (q : Nat) : sevenLayerProbability q ≤ 1 := by
  let rank : Fin codeCardinality := ⟨0, by rw [codeCardinality_eq]; decide⟩
  letI : Nonempty (LayerSample q) := ⟨(0, rank, (fun _ => 0), (fun _ => rank))⟩
  letI : Nonempty (InitialOwnerSample q) := ⟨(0, fun _ => 0)⟩
  have hd : (0 : ℚ) < Fintype.card (InitialOwnerSample q) := by
    exact_mod_cast Fintype.card_pos
  unfold sevenLayerProbability
  apply (div_le_one hd).2
  calc
    _ ≤ ∑ _initial : InitialOwnerSample q, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro initial hinitial
      exact FiniteKernels.pathProbability_le_one _ _ _ _
    _ = _ := by simp

theorem sevenLayerProbability_eq_state_kernel (q : Nat) :
    sevenLayerProbability q =
      ∑ state, ((FiniteKernels.step (layerKernel q))^[7] (initialOwnerMass q)) state := by
  symm
  exact FiniteKernels.total_sample_iterate initialOwners layerEvent nextOwners 7

theorem sevenLayerProbability_eq_count_kernel (q : Nat) :
    sevenLayerProbability q =
      ∑ count, ((FiniteKernels.step (countKernel q))^[7]
        (FiniteKernels.project ownerIndex (initialOwnerMass q))) count := by
  rw [sevenLayerProbability_eq_state_kernel]
  exact FiniteKernels.projected_total_iterate ownerIndex (layerKernel q) (countKernel q)
    layerKernel_project_row (initialOwnerMass q) 7

theorem positiveState_initial (q : Nat) :
    positiveState (FiniteKernels.project ownerIndex (initialOwnerMass q)) = initialState q := by
  unfold positiveState initialState
  rw [map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext index
  exact initialOwnerMass_count index.succ

/-- The arithmetic recurrence is exactly the literal seven-layer experiment. -/
theorem sevenLayerProbability_eq_childCover (q : Nat) :
    sevenLayerProbability q = childCover q := by
  rw [sevenLayerProbability_eq_count_kernel, childCover,
    ← positiveState_initial, positiveState_iterate]
  symm
  apply positiveState_sum
  rw [show 7 = 6 + 1 from rfl, Function.iterate_succ_apply']
  exact countStep_at_zero _

theorem childCover_nonnegative (q : Nat) : 0 ≤ childCover q := by
  rw [← sevenLayerProbability_eq_childCover]
  exact sevenLayerProbability_nonnegative q

theorem childCover_le_one (q : Nat) : childCover q ≤ 1 := by
  rw [← sevenLayerProbability_eq_childCover]
  exact sevenLayerProbability_le_one q

end PoissonDAG.GRSCC
