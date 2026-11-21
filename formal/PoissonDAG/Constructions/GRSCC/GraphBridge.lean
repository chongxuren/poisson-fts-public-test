import PoissonDAG.Constructions.GRSCC.SchemeRoute
import PoissonDAG.Constructions.GRSCC.RouteSupply
import PoissonDAG.Probability.SchemeExperiment

/-! Finite-experiment dominance rule for the actual protected raw coefficient.
The geometric supplier premise is explicit here and discharged in CoveringBound.
Raw target acceptance is extracted exactly once. -/
namespace PoissonDAG.GRSCC

open scoped BigOperators

private theorem indicator_le_of_imp (a : Bool) (b : Prop) [Decidable b]
    (h : a = true → b) :
    (if a then (1 : ℚ) else 0) ≤ (if b then (1 : ℚ) else 0) := by
  cases a <;> by_cases hb : b <;> simp_all

theorem coefficient_upper_of_suppliers (encoder : Circuit) (href : CircuitRefines encoder)
    (q : Nat)
    (hcover : ∀ sample : Fin (q + 1) → Fin (schemeOfCircuit encoder).accepted.length,
      (schemeOfCircuit encoder).covered
        (indexHistory (schemeOfCircuit encoder).accepted (fun i => sample i.succ))
        (schemeOfCircuit encoder).accepted[sample 0] = true →
      routeAllSupplied (acceptedIndexRoute encoder href (sample 0))
        (fun i => acceptedIndexRoute encoder href (sample i.succ))) :
    (schemeOfCircuit encoder).coverCoefficient q ≤ acceptanceRatio * bucketThinned q := by
  let s := schemeOfCircuit encoder
  have hw := scheme_wellFormed_of_refinement encoder href
  have hbound : s.acceptedCoverProbability q ≤ bucketChildProbability q := by
    rw [Scheme.acceptedCoverProbability_eq_tuple]
    calc
      _ ≤ FiniteKernels.average (fun sample : Fin (q + 1) → Fin s.accepted.length =>
          if routeTupleEvent (fun i => acceptedIndexRoute encoder href (sample i))
            then (1 : ℚ) else 0) := by
        apply FiniteKernels.average_mono
        intro sample
        apply indicator_le_of_imp
        intro hc
        exact route_supplied_bucket_event _ _ (hcover sample hc)
      _ = FiniteKernels.average (fun sample : Fin (q + 1) → Route =>
          if routeTupleEvent sample then (1 : ℚ) else 0) := by
        unfold FiniteKernels.average
        simp only [Fintype.card_fun, Fintype.card_fin, route_cardinality, Nat.cast_pow]
        simpa only [s] using acceptedTuple_uniform encoder href (q + 1)
          (fun sample => if routeTupleEvent sample then (1 : ℚ) else 0)
      _ = _ := routeTupleEvent_average q
  rw [Scheme.coverCoefficient_eq_acceptedProbability _ hw.2.2.2.2.2]
  rw [tau_of_refinement encoder href, ← bucketChildProbability_eq_thinned]
  exact mul_le_mul_of_nonneg_left hbound acceptanceRatio_pos.le

end PoissonDAG.GRSCC
