import PoissonDAG.Constructions.GRSCC.BucketExperiment

/-! Actual route supplier events and their counted finite experiment. -/
namespace PoissonDAG.GRSCC

open scoped BigOperators

def routeAllSupplied {q : Nat} (target : Route) (history : Fin q → Route) : Prop :=
  ∀ layer : Layer, ∀ requirement : CodePosition, ∃ i : Fin q,
    target.bucket = (history i).bucket ∧ target.owner layer = (history i).owner layer ∧
      coordinateSupply (target.slot layer) ((history i).slot layer)
        (fun position => decide (((target.code layer).depth position).val ≤
          (((history i).code layer).depth position).val)) requirement = true

instance routeAllSupplied_decidable {q : Nat} (target : Route) (history : Fin q → Route) :
    Decidable (routeAllSupplied target history) := by
  unfold routeAllSupplied
  infer_instance

theorem route_supplied_bucket_event {q : Nat} (target : Route) (history : Fin q → Route)
    (hsupply : routeAllSupplied target history) :
    bucketChildEvent (routeSampleEquiv q (target, history)) := by
  change childSupplyEvent (restrictChild
    (UniformMatching.matchingSet (target.bucket, fun i => (history i).bucket))
    (rankedChildOfRoute target, fun i => rankedChildOfRoute (history i)))
  let bucket := UniformMatching.matchingSet (target.bucket, fun i => (history i).bucket)
  intro layer requirement
  obtain ⟨i, hb, ho, hc⟩ := hsupply layer requirement
  let member : ↥bucket := ⟨i, by simp [bucket, UniformMatching.matchingSet, hb]⟩
  let j := bucket.equivFin member
  have hindex : (bucket.equivFin.symm j).val = i := by simp [j, member]
  refine ⟨j, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change rankedOwner (rankedChildOfRoute (history (bucket.equivFin.symm j).val)) layer =
      rankedOwner (rankedChildOfRoute target) layer
    rw [hindex, rankedChildOfRoute_owner, rankedChildOfRoute_owner]
    exact ho.symm
  · change coordinateSupply (target.slot layer) ((history (bucket.equivFin.symm j).val).slot layer)
      (sameSlotSupply (decodedCodeword ((rankedChildOfRoute target).2 layer).2)
        ((rankedChildOfRoute (history (bucket.equivFin.symm j).val)).2 layer).2) requirement = true
    rw [hindex]
    have hprofile :
        sameSlotSupply (decodedCodeword ((rankedChildOfRoute target).2 layer).2)
          ((rankedChildOfRoute (history i)).2 layer).2 =
        (fun position => decide (((target.code layer).depth position).val ≤
          (((history i).code layer).depth position).val)) := by
      funext position
      unfold sameSlotSupply
      rw [rankedChildOfRoute_code, rankedChildOfRoute_code]
    rw [hprofile]
    exact hc

noncomputable def routeTupleEvent {q : Nat} (sample : Fin (q + 1) → Route) : Prop :=
  bucketChildEvent (routeSampleEquiv q (sample 0, fun i => sample i.succ))

noncomputable instance routeTupleEvent_decidable {q : Nat} (sample : Fin (q + 1) → Route) :
    Decidable (routeTupleEvent sample) := inferInstanceAs
      (Decidable (bucketChildEvent (routeSampleEquiv q (sample 0, fun i => sample i.succ))))

theorem routeTupleEvent_average (q : Nat) :
    FiniteKernels.average (fun sample : Fin (q + 1) → Route =>
      if routeTupleEvent sample then (1 : ℚ) else 0) = bucketChildProbability q := by
  unfold bucketChildProbability
  apply FiniteKernels.average_equiv ((FiniteKernels.tupleSucc q).trans (routeSampleEquiv q))
  intro sample
  rfl

theorem route_cardinality : Fintype.card Route = encodingCardinality := by
  rw [Fintype.card_congr routeEquiv.symm, Fintype.card_fin]

end PoissonDAG.GRSCC
