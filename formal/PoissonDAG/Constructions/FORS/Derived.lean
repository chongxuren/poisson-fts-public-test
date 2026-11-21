import PoissonDAG.Constructions.FORS.Correctness

namespace PoissonDAG.FORS.Config

private theorem prefix_parent {p : Config} {raw tree h : Nat} (hh : 2 ≤ h)
    (hm : p.prefixMatches raw tree h = true) :
    p.prefixMatches raw tree (h/2) = true := by
  rw [prefixMatches,if_neg (by omega),Bool.and_eq_true] at hm
  exact hm.1

theorem derived_heap (p : Config) (raw tree h : Nat) (ht : tree < p.trees)
    (hlo : 0 < h) (hhi : h ≤ p.heapSize)
    (hderive : Derives p.graph (p.scheme.disclosures raw) (p.heapAddress tree h)) :
    get (p.scheme.frontier raw) (p.heapAddress tree h) = true ∨
    p.prefixMatches raw tree h = true := by
  have hg := p.heap_at ht hlo hhi
  by_cases hleaf : p.leaves ≤ h
  · rw [if_pos hleaf] at hg
    rcases (derives_unary_iff hg).1 hderive with hsup | hpriv
    · exact Or.inl (mem_maskSet.mp hsup)
    · right
      have hj : h-p.leaves < p.leaves := by unfold heapSize at hhi; omega
      have hm := Nat.mul_le_mul_right p.leaves ht
      rw [Nat.succ_mul] at hm
      have hs : p.secret tree (h-p.leaves) < p.sources := by unfold secret sources; omega
      have hf := mem_maskSet.mp ((derives_source_iff (p.source_at hs)).1 hpriv)
      rw [p.secret_frontier raw tree _ ht hj, show p.leaves+(h-p.leaves)=h by omega] at hf
      exact hf
  · rw [if_neg hleaf] at hg
    rcases (derives_binary_iff hg).1 hderive with hsup | ⟨hl,_⟩
    · exact Or.inl (mem_maskSet.mp hsup)
    · right
      have hc : 2*h ≤ p.heapSize := by unfold heapSize; omega
      rcases p.derived_heap raw tree (2*h) ht (by omega) hc hl with hf | hm
      · rw [p.heap_frontier raw tree _ ht (by omega) hc] at hf
        have hs : sibling (2*h)=2*h+1 := by simp [sibling]
        rw [hs] at hf
        simpa only [show (2*h+1)/2=h by omega] using prefix_parent (show 2≤2*h+1 by omega) hf
      · simpa [Nat.mul_comm] using prefix_parent (show 2≤2*h by omega) hm
termination_by p.heapSize-h
decreasing_by omega

end PoissonDAG.FORS.Config
