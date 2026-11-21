import PoissonDAG.Constructions.FORS.Frontier

namespace PoissonDAG.FORS.Config

theorem plan_all (p : Config) (raw : Nat) :
    p.scheme.plan raw = List.replicate p.graph.length true := by
  let read := get (p.state raw (p.prefixBase+p.trees*p.heapSize))
  let ds := (List.range p.vertexCount).map p.disclosureGate
  let head := if p.zeroBits=0 then 1 else p.prefixBase-1
  have hn : (([head]++ds).map read).length = 1+p.graph.length := by simp [ds,graph_length,Nat.add_comm]
  have h1 : read 1 = true := by
    have hh : 1 < p.prefixBase+p.trees*p.heapSize := by unfold prefixBase; omega
    change get (p.state raw _) 1 = true
    rw [p.state_get raw _ _ hh]
    simp [wire,gate,evalGate]
  change (((([head]++ds++List.replicate p.vertexCount 1).map read).drop
    (1+p.graph.length)).take p.graph.length) = _
  rw [List.map_append,List.drop_left' hn,graph_length]
  simp [h1]

theorem complete_scan (p : Config) (raw v : Nat) (hv : v < p.graph.length) :
    get (close p.graph (p.scheme.frontier raw) (p.scheme.plan raw)).1 v = true ↔
    Derives p.graph (p.scheme.disclosures raw) v := by
  rw [p.plan_all]
  exact close_complete_iff p.graph_valid _ (GRSCC.scheme_frontier_length p.scheme p.output_length raw) hv

theorem path_derives (p : Config) (raw tree d : Nat) (ht : tree < p.trees)
    (hd : d ≤ p.height) : Derives p.graph (p.scheme.disclosures raw)
      (p.heapAddress tree (p.projectedHeap raw tree d)) := by
  apply Nat.decreasingInduction (motive := fun n _ => Derives p.graph (p.scheme.disclosures raw)
    (p.heapAddress tree (p.projectedHeap raw tree n))) _ _ hd
  · intro n hn hchild
    let h := p.projectedHeap raw tree n
    let c := p.projectedHeap raw tree (n+1)
    have hr := p.path_bounds raw tree n (by omega)
    have hlt : h < p.leaves := by
      have hu := (p.projectedHeap_range raw tree n).2
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hn
      unfold h leaves
      omega
    have hg := p.heap_at ht hr.1 hr.2.1
    change p.graph[p.heapAddress tree h]? = _ at hg
    rw [if_neg (Nat.not_le.mpr hlt)] at hg
    have hs : Derives p.graph (p.scheme.disclosures raw) (p.heapAddress tree (sibling c)) :=
      .disclosed (mem_maskSet.mpr (p.path_and_sibling raw tree n ht hn).2)
    change Derives _ _ (p.heapAddress tree c) at hchild
    have hc : c=2*h ∨ c=2*h+1 := by
      unfold c projectedHeap
      cases raw.testBit (tree*p.height+(p.height-(n+1))) <;> simp [h]
    rcases hc with he | he
    · rw [he] at hs hchild
      have hsi : sibling (2*h) = 2*h+1 := by simp [sibling]
      rw [hsi] at hs
      exact .binary hg hchild hs
    · rw [he] at hs hchild
      have hsi : sibling (2*h+1) = 2*h := by unfold sibling; split <;> omega
      rw [hsi] at hs
      exact .binary hg hs hchild
  · have hr := p.path_bounds raw tree p.height (by omega)
    have hleaf : p.leaves ≤ p.projectedHeap raw tree p.height :=
      (p.projectedHeap_range raw tree p.height).1
    have hg := p.heap_at ht hr.1 hr.2.1
    rw [if_pos hleaf] at hg
    apply Derives.unary hg
    apply Derives.disclosed
    apply mem_maskSet.mpr
    exact (p.secret_frontier_iff_index raw tree _ ht (p.projectedIndex_lt raw tree)).2 rfl

theorem aggregate_at (p : Config) {j : Nat} (hj : j+1 < p.trees) :
    p.graph[p.heapEnd+j]? = some (.binary
       (if j=0 then p.heapAddress 0 1 else p.heapEnd+j-1) (p.heapAddress (j+1) 1)) := by
  have hv : p.heapEnd+j < p.vertexCount := by unfold vertexCount; omega
  have hs : ¬p.heapEnd+j < p.sources := by unfold heapEnd; omega
  simp [graph,List.getElem?_map,List.getElem?_range hv,node,hs]

theorem aggregate_derives (p : Config) (raw j : Nat) (hj : j+1 < p.trees) :
    Derives p.graph (p.scheme.disclosures raw) (p.heapEnd+j) := by
  induction j with
  | zero =>
    have hg := p.aggregate_at hj
    simp only [if_true,Nat.zero_add,Nat.add_zero] at hg ⊢
    apply Derives.binary hg
    · exact p.path_derives raw 0 0 (by omega) (by omega)
    · exact p.path_derives raw 1 0 hj (by omega)
  | succ j ih =>
    have hg := p.aggregate_at hj
    rw [if_neg (by omega : j+1≠0)] at hg
    apply Derives.binary hg
    · rw [show p.heapEnd+(j+1)-1 = p.heapEnd+j by omega]
      exact ih (by omega)
    · exact p.path_derives raw _ 0 hj (by omega)

theorem correct (p : Config) (ht : 2 ≤ p.trees) : p.scheme.Correct := by
  intro raw _
  have hv : p.scheme.graph.length-1 < p.graph.length := by
    change p.graph.length-1 < p.graph.length
    rw [graph_length]
    unfold vertexCount
    omega
  apply (p.complete_scan raw _ hv).2
  have he : p.scheme.graph.length-1 = p.heapEnd+(p.trees-2) := by
    change p.graph.length-1 = _
    rw [graph_length]
    unfold vertexCount
    omega
  rw [he]
  exact p.aggregate_derives raw _ (by omega)

end PoissonDAG.FORS.Config
