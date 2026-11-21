import PoissonDAG.Constructions.PORS.LiteralCosts
import PoissonDAG.Constructions.PORS.RoutedOpening
import PoissonDAG.Constructions.PORS.Transfer
import PoissonDAG.Constructions.PORS.SingleRefinedChecks
import PoissonDAG.Constructions.PORS.BucketRefinedChecks
import PoissonDAG.Constructions.PORS.ChainRefinedChecks

namespace PoissonDAG.PORS.Literal

abbrev rowTree (p : Row) :=
  (shape p.K).fill ((shape p.buckets).fill ((shape p.t).fill (PORS.chain (p.cap+1))))

/-- Concrete remaining decoder-to-model obligations for the production gates.
The resource laws and all-cuts inequality are derived, never supplied. -/
structure Refinement (p : Row) (bound : Nat → ℚ) : Prop extends OutputFacts p where
  traversal : ∀ raw ∈ (scheme p).accepted, ∃ (bucket : Nat → Nat)
      (depth : Nat → Nat → Option Nat) (a : Opening (rowTree p)),
      routedOpening (shape p.K) (shape p.buckets) (shape p.t) p.cap bucket depth = some a ∧
      (scheme p).frontier raw = a.marks.map Prod.fst ∧
      (scheme p).plan raw = a.marks.map Prod.snd
  historicalCount : ∀ q, (scheme p).coverCoefficient q ≤ bound q

private theorem route_authenticated (p : Row) (bound : Nat → ℚ) (h : Refinement p bound) :
    ∀ raw ∈ (scheme p).accepted,
      V2.Authenticated (scheme p).graph ((scheme p).frontier raw) ((scheme p).plan raw) := by
  intro raw hr
  obtain ⟨b,d,a,route,hs,hp⟩ := h.traversal raw hr
  rw [hs,hp]
  exact routed_authenticated route

theorem of_refinement (p : Row) (bound : Nat → ℚ) (bytes : Nat) (h : Refinement p bound)
    (hr : 0<p.r) (ha : 0<p.acceptedWords)
    (unit : ∀ q, bound q ≤ 1)
    (finite : weightedCut bound 1 40 +
      ((1 : ℚ)^40 / factorial 40) / (1 - 1 / (40+1 : ℚ)) ≤
      ((1 : ℚ)/2^128) * exponentialCut 1 4)
    (resources : (scheme p).failure ≤ (1 : ℚ)/2^128 ∧ (scheme p).signCost ≤ 2^24 ∧
      (scheme p).verifyCost ≤ 512 ∧ (scheme p).size ≤ bytes) :
    V2.ConstructionCertificate (scheme p) bytes := by
  have hgraph : 0 < (scheme p).graph.length := by
    change 0 < ((rowTree p).emit 0).length
    rw [Tree.emit_length]
    cases rowTree p <;> simp [Tree.nodes]
  have hw : (scheme p).WellFormed := ⟨hgraph,hr,scheme_circuit_valid p,scheme_output_arity p,
    graph_valid _ _ _ _,by rw [h.count]; exact ha⟩
  have auth := route_authenticated p bound h
  have correct : (scheme p).Correct := fun raw hr => (auth raw hr).2.1
  exact ⟨⟨⟨hw,correct,resources.1,resources.2.1,resources.2.2.1,
    covering_of_envelope _ _ h.historicalCount unit finite⟩,auth⟩,resources.2.2.2⟩

theorem single_conditional (h : Refinement SingleRefined.p SingleRefined.p.rawEnvelope) :
    V2.ConstructionCertificate single 1780 :=
  of_refinement _ _ _ h (by decide) (by decide)
    (rawEnvelope_le_one _ (by decide +kernel)) SingleRefined.finite_moment
    (single_resources h.toOutputFacts)

theorem bucket_conditional (h : Refinement BucketRefined.p BucketRefined.p.rawEnvelope) :
    V2.ConstructionCertificate bucket 1492 :=
  of_refinement _ _ _ h (by decide) (by decide)
    (rawEnvelope_le_one _ (by decide +kernel)) BucketRefined.finite_moment
    (bucket_resources h.toOutputFacts)

theorem chain_conditional
    (h : Refinement ChainRefined.p (ChainRefined.p.simplexEnvelope ChainRefined.coefs)) :
    V2.ConstructionCertificate chainBuckets 1188 := by
  apply of_refinement _ _ _ h (by decide) (by decide) _ ChainRefined.finite_moment
    (chain_resources h.toOutputFacts)
  intro q
  unfold Row.simplexEnvelope
  exact (min_le_left _ _).trans (by decide +kernel)

end PoissonDAG.PORS.Literal
