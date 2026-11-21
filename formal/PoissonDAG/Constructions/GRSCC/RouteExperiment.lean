import PoissonDAG.Constructions.GRSCC.Markov
import PoissonDAG.Constructions.GRSCC.Law
import PoissonDAG.Probability.UniformAverage
import Mathlib.Data.Fin.Rev

/-! # Literal route coordinates and the seven-layer experiment

The coordinate permutation reverses the graph's topological layer numbering:
signing and the coverage experiment traverse layer6 first and layer0 last.
-/
namespace PoissonDAG.GRSCC

open scoped BigOperators

abbrev RankedChild := Fin 2 × (Layer → Slot × Fin codeCardinality)
abbrev ChildSample (q : Nat) := RankedChild × (Fin q → RankedChild)

instance : Nonempty RankedChild :=
  ⟨(0, fun _ => (0, ⟨0, by rw [codeCardinality_eq]; decide⟩))⟩

def rankedOwner (child : RankedChild) (layer : Layer) : Nat :=
  if h : layer.val = 6 then child.1.val
  else (child.2 ⟨layer.val + 1, by omega⟩).1.val

def rankedOwners {q : Nat} (sample : ChildSample q) (layer : Layer) : OwnerState q :=
  Finset.univ.filter (fun i => rankedOwner (sample.2 i) layer = rankedOwner sample.1 layer)

def rankedLayerSample {q : Nat} (sample : ChildSample q) (layer : Layer) : LayerSample q :=
  ((sample.1.2 layer).1, (sample.1.2 layer).2,
    (fun i => ((sample.2 i).2 layer).1), (fun i => ((sample.2 i).2 layer).2))

def rankedInitialSample {q : Nat} (sample : ChildSample q) : InitialOwnerSample q :=
  (sample.1.1, fun i => (sample.2 i).1)

def childSupplyEvent {q : Nat} (sample : ChildSample q) : Prop :=
  ∀ layer : Layer, localLayerEvent (rankedOwners sample layer) (rankedLayerSample sample layer)

instance childSupplyEvent_decidable {q : Nat} (sample : ChildSample q) :
    Decidable (childSupplyEvent sample) := by
  unfold childSupplyEvent
  infer_instance

/-- Swap rows and columns, and read layers in the actual traversal order. -/
def childCoordinates (q : Nat) :
    ChildSample q ≃ InitialOwnerSample q × (Layer → LayerSample q) where
  toFun sample := (rankedInitialSample sample,
    fun layer => rankedLayerSample sample layer.rev)
  invFun data :=
    ((data.1.1, fun layer => ((data.2 layer.rev).1, (data.2 layer.rev).2.1)),
      fun i => (data.1.2 i,
        fun layer => ((data.2 layer.rev).2.2.1 i, (data.2 layer.rev).2.2.2 i)))
  left_inv sample := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext layer
        simp [rankedLayerSample]
    · funext i
      apply Prod.ext
      · rfl
      · funext layer
        simp [rankedLayerSample]
  right_inv data := by
    apply Prod.ext
    · rfl
    · funext layer
      simp [rankedLayerSample]

theorem rankedOwners_initial {q : Nat} (sample : ChildSample q) :
    initialOwners (rankedInitialSample sample) = rankedOwners sample 6 := by
  ext i
  simp [initialOwners, rankedInitialSample, rankedOwners, rankedOwner, Fin.ext_iff]

theorem rankedOwners_next {q : Nat} (sample : ChildSample q) (layer : Fin 6) :
    nextOwners (rankedLayerSample sample layer.succ) =
      rankedOwners sample layer.castSucc := by
  ext i
  have h : layer.val < 6 := layer.isLt
  simp [nextOwners, rankedLayerSample, rankedOwners, rankedOwner, Fin.ext_iff,
    show layer.val ≠ 6 by omega]
  rfl

private theorem path_seven_iff {q : Nat} (sample : ChildSample q) :
    FiniteKernels.pathEvent layerEvent nextOwners
      (initialOwners (rankedInitialSample sample))
      (List.ofFn (fun layer : Layer => rankedLayerSample sample layer.rev)) = true ↔
        childSupplyEvent sample := by
  simp only [List.ofFn_succ, List.ofFn_zero, FiniteKernels.pathEvent,
    Bool.and_eq_true, and_true, layerEvent, decide_eq_true_eq]
  rw [rankedOwners_initial]
  have hnext : ∀ layer : Fin 6,
      nextOwners (rankedLayerSample sample layer.succ) =
        rankedOwners sample layer.castSucc := rankedOwners_next sample
  constructor
  · intro h layer
    fin_cases layer
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using (hnext 0 ▸ h.2.2.2.2.2.2)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using (hnext 1 ▸ h.2.2.2.2.2.1)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using (hnext 2 ▸ h.2.2.2.2.1)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using (hnext 3 ▸ h.2.2.2.1)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using (hnext 4 ▸ h.2.2.1)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using (hnext 5 ▸ h.2.1)
    · exact h.1
  · intro h
    refine ⟨h 6, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using ((hnext 5).symm ▸ h 5)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using ((hnext 4).symm ▸ h 4)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using ((hnext 3).symm ▸ h 3)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using ((hnext 2).symm ▸ h 2)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using ((hnext 1).symm ▸ h 1)
    · simpa only [Fin.rev, Fin.val_zero, Fin.val_succ] using ((hnext 0).symm ▸ h 0)

def childSupplyProbability (q : Nat) : ℚ :=
  FiniteKernels.average (fun sample : ChildSample q =>
    if childSupplyEvent sample then (1 : ℚ) else 0)

theorem childSupplyProbability_eq_sevenLayer (q : Nat) :
    childSupplyProbability q = sevenLayerProbability q := by
  unfold childSupplyProbability
  calc
    _ = FiniteKernels.average (fun data : InitialOwnerSample q × (Layer → LayerSample q) =>
        if FiniteKernels.pathEvent layerEvent nextOwners (initialOwners data.1)
          (List.ofFn data.2) then (1 : ℚ) else 0) := by
      apply FiniteKernels.average_equiv (childCoordinates q)
      intro sample
      change (if childSupplyEvent sample then (1 : ℚ) else 0) =
        (if FiniteKernels.pathEvent layerEvent nextOwners
          (initialOwners (rankedInitialSample sample))
          (List.ofFn (fun layer : Layer => rankedLayerSample sample layer.rev))
          then (1 : ℚ) else 0)
      simp only [path_seven_iff]
    _ = _ := by
      rw [FiniteKernels.average_prod]
      unfold FiniteKernels.average sevenLayerProbability FiniteKernels.pathProbability
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

theorem childSupplyProbability_eq_childCover (q : Nat) :
    childSupplyProbability q = childCover q := by
  rw [childSupplyProbability_eq_sevenLayer, sevenLayerProbability_eq_childCover]

noncomputable def rankedChildOfRoute (route : Route) : RankedChild :=
  (route.initialOwner, fun layer => (route.slot layer, codeEquiv.symm (route.code layer)))

theorem rankedChildOfRoute_owner (route : Route) (layer : Layer) :
    rankedOwner (rankedChildOfRoute route) layer = route.owner layer := rfl

theorem rankedChildOfRoute_code (route : Route) (layer : Layer) :
    decodedCodeword ((rankedChildOfRoute route).2 layer).2 = route.code layer :=
  codeEquiv.apply_symm_apply _

end PoissonDAG.GRSCC
