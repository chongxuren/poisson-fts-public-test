import PoissonDAG.Core.BVCompiler
import PoissonDAG.Core.RestrictedScan
import PoissonDAG.Constructions.GRSCC.EncoderFormula
import PoissonDAG.Constructions.GRSCC.Correctness
import PoissonDAG.Constructions.GRSCC.Costs

/-! The literal protected Scheme, obtained from the verified bitvector/AIG
compiler. No encoder-realization hypothesis is an input to this construction. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

@[irreducible] def literalCircuit : Circuit := BVCompiler.toCircuit rawBits EncoderFormula.outputs

theorem literalCircuit_refines : CircuitRefines literalCircuit := by
  rw [literalCircuit]
  refine ⟨BVCompiler.toCircuit_valid _ _, BVCompiler.toCircuit_inputs _ _, ?_, ?_⟩
  · rw [BVCompiler.toCircuit_outputs_length]
    exact EncoderFormula.outputs_length
  · intro raw hraw
    rw [BVCompiler.toCircuit_eval]
    simpa only [BVCompiler.rawAssignment, EncoderFormula.assignment,
      rawBits, thresholdBits, rankBits] using EncoderFormula.outputs_refine raw hraw

def scheme : Scheme := schemeOfCircuit literalCircuit

theorem scheme_wellFormed : scheme.WellFormed :=
  scheme_wellFormed_of_refinement literalCircuit literalCircuit_refines

theorem scheme_tau : scheme.tau = acceptanceRatio :=
  tau_of_refinement literalCircuit literalCircuit_refines

theorem scheme_signing_budget : scheme.signCost ≤ 2 ^ 24 := by
  apply signing_budget_of_refinement scheme (by change graph.length = graphNodes; exact graph_length')
  · change (literalCircuit.inputs + 127) / 128 = digestBlockCount
    simp [literalCircuit, digestBlockCount]
  · exact scheme_tau
  · rw [scheme_tau]
    exact acceptanceRatio_le_one

theorem scheme_failure_budget : scheme.failure ≤ (1 : ℚ) / 2 ^ 128 := by
  apply failure_budget_of_refinement scheme rfl scheme_tau
  rw [scheme_tau]
  exact acceptanceRatio_le_one

theorem scheme_frontier_route (raw : Nat) (hraw : raw ∈ scheme.accepted) :
    ∃ route : Route, scheme.frontier raw = route.frontier := by
  obtain ⟨hbound, haccept⟩ := (scheme_mem_accepted scheme raw).mp hraw
  have hraw' : raw < 2 ^ rawBits := by
    simpa only [scheme, schemeOfCircuit, literalCircuit, BVCompiler.toCircuit_inputs] using hbound
  have haccept' : rawAccept raw = true := by
    rw [← scheme_accept_of_refinement literalCircuit literalCircuit_refines raw hraw']
    exact haccept
  have hfields : rawThreshold raw < threshold ∧ rawRank raw < encodingCardinality := by
    simpa only [rawAccept, decide_eq_true_eq] using haccept'
  let route := decodedRoute ⟨rawRank raw, hfields.2⟩
  refine ⟨route, ?_⟩
  exact scheme_frontier_of_refinement literalCircuit literalCircuit_refines raw hraw' route
    (by simp [decodeRaw, hfields, route])

theorem scheme_size_budget : scheme.size ≤ 756 :=
  size_budget_of_refinement scheme rfl scheme_frontier_route

theorem Route.reconstructs_planDerives (route : Route) (vertex : Nat)
    (h : route.Reconstructs vertex) :
    PlanDerives graph (maskSet route.frontier) route.plan vertex := by
  induction h with
  | disclosed hi =>
      apply PlanDerives.disclosed
      apply mem_maskSet.mpr
      have hb := disclosure_bounds route _ hi
      rw [frontier_get route _ hb]
      exact decide_eq_true hi
  | unary hi hn _ ih =>
      apply PlanDerives.unary
      · have hb := recovery_bounds route _ hi
        simpa only [hn] using graph_get ⟨_, hb⟩
      · have hb := recovery_bounds route _ hi
        rw [plan_get route _ hb]
        exact decide_eq_true hi
      · exact ih
  | binary hi hn _ _ ihl ihr =>
      apply PlanDerives.binary
      · have hb := recovery_bounds route _ hi
        simpa only [hn] using graph_get ⟨_, hb⟩
      · have hb := recovery_bounds route _ hi
        rw [plan_get route _ hb]
        exact decide_eq_true hi
      · exact ihl
      · exact ihr

theorem route_close_root (route : Route) :
    get (close graph route.frontier route.plan).1 (graph.length - 1) = true := by
  have hlen : route.frontier.length = graph.length := by
    rw [frontier_length, graph_length']
  have hroot : graphNodes - 1 < graph.length := by
    rw [graph_length, fixed_geometry.2.2.2.1]
    decide
  have hd := Route.reconstructs_planDerives route _ (root_reconstructs route)
  have h := close_of_planDerives graph_valid route.frontier route.plan hlen hroot hd
  simpa only [graph_length'] using h

theorem route_close_calls (route : Route) :
    (close graph route.frontier route.plan).2 ≤ 439 := by
  have hlen : route.plan.length = graph.length := by
    rw [plan_length, graph_length']
  have hscan := close_calls_le_weight graph route.frontier route.plan hlen
  have hweight := plan_weight_le route
  rw [recovery_length] at hweight
  exact hscan.trans hweight

theorem scheme_layout_route (raw : Nat) (hraw : raw ∈ scheme.accepted) :
    ∃ route : Route, scheme.frontier raw = route.frontier ∧ scheme.plan raw = route.plan := by
  obtain ⟨hbound, haccept⟩ := (scheme_mem_accepted scheme raw).mp hraw
  have hraw' : raw < 2 ^ rawBits := by
    simpa only [scheme, schemeOfCircuit, literalCircuit, BVCompiler.toCircuit_inputs] using hbound
  have haccept' : rawAccept raw = true := by
    rw [← scheme_accept_of_refinement literalCircuit literalCircuit_refines raw hraw']
    exact haccept
  have hfields : rawThreshold raw < threshold ∧ rawRank raw < encodingCardinality := by
    simpa only [rawAccept, decide_eq_true_eq] using haccept'
  let route := decodedRoute ⟨rawRank raw, hfields.2⟩
  have hdecode : decodeRaw raw = some route := by simp [decodeRaw, hfields, route]
  exact ⟨route,
    scheme_frontier_of_refinement literalCircuit literalCircuit_refines raw hraw' route hdecode,
    scheme_plan_of_refinement literalCircuit literalCircuit_refines raw hraw' route hdecode⟩

theorem correctness_of_route_layout (s : Scheme) (hgraph : s.graph = graph)
    (hlayout : ∀ raw ∈ s.accepted,
      ∃ route : Route, s.frontier raw = route.frontier ∧ s.plan raw = route.plan) :
    s.Correct := by
  intro raw hraw
  obtain ⟨route, hf, hp⟩ := hlayout raw hraw
  change get (close s.graph (s.frontier raw) (s.plan raw)).1 (s.graph.length - 1) = true
  rw [hgraph, hf, hp]
  exact route_close_root route

theorem scheme_correct : scheme.Correct :=
  correctness_of_route_layout scheme rfl scheme_layout_route

theorem scheme_verifyCalls_bound (raw : Nat) (hraw : raw ∈ scheme.accepted) :
    scheme.verifyCalls raw ≤ 441 := by
  obtain ⟨route, hf, hp⟩ := scheme_layout_route raw hraw
  have hdigest : scheme.digestCalls = 2 := by
    simp [Scheme.digestCalls, scheme, schemeOfCircuit, literalCircuit, rawBits,
      thresholdBits, rankBits]
  change scheme.digestCalls + (close graph (scheme.frontier raw) (scheme.plan raw)).2 ≤ 441
  rw [hdigest, hf, hp]
  have h := route_close_calls route
  omega

theorem scheme_verification_budget : scheme.verifyCost ≤ 512 := by
  obtain ⟨_, _, _, _, _, haccepted⟩ := scheme_wellFormed
  have htau : scheme.tau ≤ 1 := by rw [scheme_tau]; exact acceptanceRatio_le_one
  have hfzero : 0 ≤ scheme.failure := by
    change 0 ≤ (1 - scheme.tau) ^ scheme.trials
    exact pow_nonneg (sub_nonneg.mpr htau) _
  have hfone : scheme.failure ≤ 1 :=
    scheme_failure_budget.trans (by norm_num)
  exact verification_budget_of_refinement scheme haccepted hfzero hfone scheme_verifyCalls_bound

end PoissonDAG.GRSCC
