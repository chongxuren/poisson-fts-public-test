import PoissonDAG.Constructions.FORS.Derived
import PoissonDAG.Constructions.FORS.ScanCost
import PoissonDAG.Constructions.GRSCC.CostBasic
import PoissonDAG.Probability.Counting

namespace PoissonDAG.FORS.Config

def pathAddress (p : Config) (raw : Nat) (x : Fin p.trees × Fin (p.height+1)) :=
  p.heapAddress x.1 (p.projectedHeap raw x.1 x.2)

def pathSet (p : Config) (raw : Nat) := Finset.univ.image (p.pathAddress raw)
def joinSet (p : Config) := (Finset.range (p.trees-1)).image (p.heapEnd+·)

theorem known_containment (p : Config) (raw : Nat) :
    maskSet (close p.graph (p.scheme.frontier raw) (p.scheme.plan raw)).1 ⊆
      (p.scheme.disclosures raw ∪ p.pathSet raw) ∪ p.joinSet := by
  intro v hv
  have hlen := GRSCC.scheme_frontier_length p.scheme p.output_length raw
  have hk := mem_maskSet.mp hv
  have hbound := get_true_lt hk
  rw [GRSCC.close_length,hlen] at hbound
  change v < p.graph.length at hbound
  have hint := (p.complete_scan raw v hbound).1 hk
  have hvmax : v < p.vertexCount := by simpa [graph_length] using hbound
  by_cases hs : v < p.sources
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((derives_source_iff (p.source_at hs)).1 hint))
  by_cases hh : v < p.heapEnd
  · let t := (v-p.sources)/p.heapSize
    let h := p.heapSize-(v-p.sources)%p.heapSize
    have hr := Nat.mod_lt (v-p.sources) p.heap_pos
    have he := Nat.div_add_mod' (v-p.sources) p.heapSize
    have ht : t < p.trees := by
      apply (Nat.div_lt_iff_lt_mul p.heap_pos).2
      unfold heapEnd at hh
      omega
    have hlo : 0<h := by unfold h; omega
    have hhi : h ≤ p.heapSize := by unfold h; omega
    have haddr : v = p.heapAddress t h := by unfold heapAddress h t; omega
    rw [haddr] at hint
    rcases p.derived_heap raw t h ht hlo hhi hint with sup | path
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_maskSet.mpr (by simpa only [haddr] using sup)))
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      have heq := (p.heap_prefix_iff raw t h hlo).1 path
      have hdepth : h.log2 < p.height+1 := by
        apply (Nat.log2_lt (by omega)).2
        unfold heapSize leaves at hhi
        rw [Nat.pow_succ]
        omega
      apply Finset.mem_image.mpr
      refine ⟨(⟨t,ht⟩,⟨h.log2,hdepth⟩),Finset.mem_univ _,?_⟩
      change p.heapAddress t (p.projectedHeap raw t h.log2) = v
      rw [heq,haddr]
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨v-p.heapEnd,Finset.mem_range.mpr ?_,?_⟩
    · unfold vertexCount at hvmax
      omega
    · omega

theorem verification_calls (p : Config) (raw : Nat) :
    p.scheme.verifyCalls raw ≤ p.scheme.digestCalls+p.trees*(p.height+1)+(p.trees-1) := by
  let s := p.scheme
  let a := s.frontier raw
  let closeResult := close p.graph a (s.plan raw)
  have hcons : weight closeResult.1 = weight a + closeResult.2 :=
    calls_conservation _ _ _ (GRSCC.scheme_frontier_length _ p.output_length _)
  have hsubset := Finset.card_le_card (p.known_containment raw)
  have hcard := Finset.card_union_le (p.scheme.disclosures raw ∪ p.pathSet raw) p.joinSet
  have hcard₂ := Finset.card_union_le (p.scheme.disclosures raw) (p.pathSet raw)
  have hpath : (p.pathSet raw).card ≤ p.trees*(p.height+1) :=
    Finset.card_image_le.trans (by simp)
  have hj : p.joinSet.card ≤ p.trees-1 := Finset.card_image_le.trans (by simp)
  rw [maskSet_card] at hsubset
  change weight closeResult.1 ≤ _ at hsubset
  have hdis : (p.scheme.disclosures raw).card = weight a := maskSet_card _
  change s.digestCalls+closeResult.2 ≤ s.digestCalls+p.trees*(p.height+1)+(p.trees-1)
  omega

theorem verification_budget (p : Config) (hp : 0 < p.scheme.accepted.length)
    (hb : p.scheme.digestCalls+p.trees*(p.height+1)+(p.trees-1) ≤ 441) :
    p.scheme.verifyCost ≤ 512 := by
  apply GRSCC.verification_budget_of_refinement _ hp (failure_nonneg _) ?_
    (fun raw _ => (p.verification_calls raw).trans hb)
  unfold Scheme.failure
  exact pow_le_one₀ (sub_nonneg.mpr (tau_le_one _)) (sub_le_self _ (tau_nonneg _))

end PoissonDAG.FORS.Config
