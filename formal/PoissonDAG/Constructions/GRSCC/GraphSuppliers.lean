import PoissonDAG.Constructions.GRSCC.RouteSupply
import PoissonDAG.Constructions.GRSCC.SchemeRoute
import PoissonDAG.Constructions.GRSCC.Supplier
import PoissonDAG.Probability.SchemeExperiment

/-! Protected pooled closure implies the literal accepted-route supplier event. -/
namespace PoissonDAG.GRSCC

open scoped BigOperators

set_option maxHeartbeats 20000

private theorem coordinateSupply_edge_true (target history : Slot)
    (profile : CodePosition → Bool) (depth : Depth)
    (hsupply : divergesAt target history depth = true ∨
      (history.val / 2 ^ (4 - depth.val) = target.val / 2 ^ (4 - depth.val) ∧
        profile (depthPosition depth) = true)) :
    coordinateSupply target history profile (depthPosition depth) = true := by
  unfold coordinateSupply
  rw [dif_pos (show (depthPosition depth).val < 5 from depth.isLt)]
  change (divergesAt target history depth ||
    (decide (history.val / 2 ^ (4 - depth.val) = target.val / 2 ^ (4 - depth.val)) &&
      profile (depthPosition depth))) = true
  rcases hsupply with hdiv | ⟨hprefix, hprofile⟩
  · rw [hdiv] <;> rfl
  · rw [decide_eq_true hprefix, hprofile] <;>
      (cases divergesAt target history depth <;> rfl)

private theorem coordinateSupply_guard_true (target history : Slot)
    (profile : CodePosition → Bool) (hslot : target = history)
    (hprofile : profile guardPosition = true) :
    coordinateSupply target history profile guardPosition = true := by
  change (decide (target = history) && profile guardPosition) = true
  rw [decide_eq_true hslot, hprofile] <;> rfl

theorem covered_accepted_route_supplied (encoder : Circuit) (href : CircuitRefines encoder)
    {q : Nat} (sample : Fin (q + 1) → Fin (schemeOfCircuit encoder).accepted.length)
    (hcovered : (schemeOfCircuit encoder).covered
      (indexHistory (schemeOfCircuit encoder).accepted (fun i => sample i.succ))
      (schemeOfCircuit encoder).accepted[sample 0] = true) :
    routeAllSupplied (acceptedIndexRoute encoder href (sample 0))
      (fun i => acceptedIndexRoute encoder href (sample i.succ)) := by
  let s := schemeOfCircuit encoder
  let target := acceptedIndexRoute encoder href (sample 0)
  let decode := fun raw => (decodeRaw raw).getD target
  let hs := indexHistory s.accepted (fun i => sample i.succ)
  have hroute (i : Fin (q + 1)) :
      decode s.accepted[sample i] = acceptedIndexRoute encoder href (sample i) := by
    exact congrArg (fun decoded : Option Route => decoded.getD target)
      (decodeRaw_acceptedIndex encoder href (sample i))
  have ht : s.frontier s.accepted[sample 0] = (decode s.accepted[sample 0]).frontier := by
    rw [hroute]
    exact frontier_acceptedIndex encoder href _
  have hh : ∀ raw ∈ hs, s.frontier raw = (decode raw).frontier := by
    intro raw hraw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hraw
    rw [hroute]
    exact frontier_acceptedIndex encoder href _
  have houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length := by
    change encoder.outputs.length = 1 + 2 * graph.length
    rw [graph_length']
    exact href.2.2.1
  intro layer requirement
  by_cases he : requirement.val < 5
  · let depth : Depth := ⟨requirement.val, he⟩
    have hposition : depthPosition depth = requirement := Fin.ext rfl
    obtain ⟨raw, hraw, hb, ho, hcases⟩ := covered_edge_supplier s hs s.accepted[sample 0]
      decode layer depth rfl houtputs ht hh hcovered
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hraw
    have hr : decode raw = acceptedIndexRoute encoder href (sample i.succ) := by
      rw [← hi]
      exact hroute i.succ
    rw [hroute, hr] at hb ho hcases
    refine ⟨i, Fin.ext hb, ho, ?_⟩
    rw [← hposition]
    apply coordinateSupply_edge_true _ _ _ depth
    rcases hcases with hdiv | ⟨hprefix, hcode⟩
    · exact Or.inl hdiv
    · exact Or.inr ⟨hprefix, decide_eq_true hcode⟩
  · have hposition : requirement = guardPosition := by
      apply Fin.ext
      have h := requirement.isLt
      dsimp [guardPosition]
      omega
    subst requirement
    obtain ⟨raw, hraw, hb, ho, hslot, hcode⟩ := covered_guard_supplier s hs s.accepted[sample 0]
      decode layer rfl houtputs ht hh hcovered
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hraw
    have hr : decode raw = acceptedIndexRoute encoder href (sample i.succ) := by
      rw [← hi]
      exact hroute i.succ
    rw [hroute, hr] at hb ho hslot hcode
    refine ⟨i, Fin.ext hb, ho, ?_⟩
    exact coordinateSupply_guard_true _ _ _ hslot (decide_eq_true hcode)

end PoissonDAG.GRSCC
