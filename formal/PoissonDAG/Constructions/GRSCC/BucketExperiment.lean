import PoissonDAG.Constructions.GRSCC.RouteExperiment
import Mathlib.Data.Fintype.EquivFin

/-! # Conditioning on the actual common bucket

The matching set is sampled once for all seven layers. Histories outside it
are forgotten by a proved product-space identity. No independent resampling
of a bucket, owner set, or history count occurs in this calculation.
-/
namespace PoissonDAG.GRSCC

open scoped BigOperators

noncomputable def routeCoordinateEquiv : Route ≃ Bucket × RankedChild :=
  routePack.trans (Equiv.prodCongr (Equiv.refl Bucket)
    (Equiv.prodCongr (Equiv.refl (Fin 2))
      (Equiv.piCongrRight fun _ : Layer =>
        Equiv.prodCongr (Equiv.refl Slot) codeEquiv.symm)))

noncomputable def routeSampleEquiv (q : Nat) :
    (Route × (Fin q → Route)) ≃ UniformMatching.Sample 16 q × ChildSample q :=
  ((Equiv.prodCongr routeCoordinateEquiv
      ((Equiv.piCongrRight fun _ : Fin q => routeCoordinateEquiv).trans
        (Equiv.arrowProdEquivProdArrow (Fin q) (fun _ => Bucket) (fun _ => RankedChild)))).trans
    (Equiv.prodProdProdComm Bucket RankedChild (Fin q → Bucket) (Fin q → RankedChild)))

noncomputable def restrictChild {q : Nat} (bucket : Finset (Fin q))
    (sample : ChildSample q) : ChildSample bucket.card :=
  (sample.1, fun i => sample.2 (bucket.equivFin.symm i).val)

noncomputable def bucketChildEvent {q : Nat}
    (sample : UniformMatching.Sample 16 q × ChildSample q) : Prop :=
  childSupplyEvent (restrictChild (UniformMatching.matchingSet sample.1) sample.2)

noncomputable instance bucketChildEvent_decidable {q : Nat}
    (sample : UniformMatching.Sample 16 q × ChildSample q) :
    Decidable (bucketChildEvent sample) := inferInstanceAs
      (Decidable (childSupplyEvent (restrictChild (UniformMatching.matchingSet sample.1) sample.2)))

theorem restrictChild_average {q : Nat} (bucket : Finset (Fin q)) :
    FiniteKernels.average (fun sample : ChildSample q =>
      if childSupplyEvent (restrictChild bucket sample) then (1 : ℚ) else 0) =
        childSupplyProbability bucket.card := by
  exact FiniteKernels.average_pair_restrict_equiv
    (fun i : Fin q => i ∈ bucket) bucket.equivFin
    (fun sample : ChildSample bucket.card =>
      if childSupplyEvent sample then (1 : ℚ) else 0)

noncomputable def bucketChildProbability (q : Nat) : ℚ :=
  FiniteKernels.average (fun sample : UniformMatching.Sample 16 q × ChildSample q =>
    if bucketChildEvent sample then (1 : ℚ) else 0)

theorem bucketChildProbability_eq_thinned (q : Nat) :
    bucketChildProbability q = bucketThinned q := by
  unfold bucketChildProbability
  rw [FiniteKernels.average_prod]
  have hconditional (bucketSample : UniformMatching.Sample 16 q) :
      FiniteKernels.average (fun child : ChildSample q =>
        if bucketChildEvent (bucketSample, child) then (1 : ℚ) else 0) =
          childCover (UniformMatching.matchingSet bucketSample).card := by
    change FiniteKernels.average (fun child : ChildSample q =>
      if childSupplyEvent (restrictChild (UniformMatching.matchingSet bucketSample) child)
        then (1 : ℚ) else 0) = _
    rw [restrictChild_average, childSupplyProbability_eq_childCover]
  simp_rw [hconditional]
  have hcard := UniformMatching.average_cardinality (m := 16) (by decide) q
    (fun k => childCover k.val)
  change FiniteKernels.average (fun sample : UniformMatching.Sample 16 q =>
    childCover (UniformMatching.matchingSet sample).card) = _
  have hcard' :
      FiniteKernels.average (fun sample : UniformMatching.Sample 16 q =>
        childCover (UniformMatching.matchingSet sample).card) =
      ∑ k : Fin (q + 1),
        ((q.choose k.val : ℚ) * ((1 : ℚ) / 16) ^ k.val *
          (1 - (1 : ℚ) / 16) ^ (q - k.val)) * childCover k.val := by
    simpa only [UniformMatching.cardinalityIndex, Nat.cast_ofNat] using hcard
  rw [hcard']
  unfold bucketThinned
  rw [map_range_eq_ofFn, Fin.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k hk
  have hle : k.val ≤ q := by have := k.isLt; omega
  simp [binomialMass, hle]

end PoissonDAG.GRSCC
