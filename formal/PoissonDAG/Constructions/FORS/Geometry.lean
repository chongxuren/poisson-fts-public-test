import PoissonDAG.Constructions.FORS.Literal
import PoissonDAG.Core.GraphFacts

namespace PoissonDAG.FORS.Config

theorem heap_pos (p : Config) : 0 < p.heapSize := by
  have ht : 0 < p.leaves := Nat.two_pow_pos _
  unfold heapSize
  omega

theorem heap_bounds (p : Config) {tree h : Nat} (ht : tree < p.trees)
    (hlo : 0 < h) (hhi : h ≤ p.heapSize) :
    p.sources ≤ p.heapAddress tree h ∧ p.heapAddress tree h < p.heapEnd := by
  have step := Nat.mul_le_mul_right p.heapSize ht
  rw [Nat.succ_mul] at step
  unfold heapAddress heapEnd
  omega

theorem heap_locate (p : Config) {tree h : Nat} (hlo : 0 < h) (hhi : h ≤ p.heapSize) :
    (p.heapAddress tree h-p.sources)/p.heapSize = tree ∧
    p.heapSize-(p.heapAddress tree h-p.sources)%p.heapSize = h := by
  have he : p.heapAddress tree h-p.sources = (p.heapSize-h)+p.heapSize*tree := by
    unfold heapAddress
    rw [Nat.mul_comm tree]
    omega
  have hr : p.heapSize-h < p.heapSize := by omega
  rw [he, Nat.add_mul_div_left _ _ p.heap_pos, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
  omega

theorem heap_at (p : Config) {tree h : Nat} (ht : tree < p.trees)
    (hlo : 0 < h) (hhi : h ≤ p.heapSize) :
    p.graph[p.heapAddress tree h]? = some
      (if h ≥ p.leaves then .unary (p.secret tree (h-p.leaves)) else
        .binary (p.heapAddress tree (2*h)) (p.heapAddress tree (2*h+1))) := by
  have hb := p.heap_bounds ht hlo hhi
  have hd := p.heap_locate (tree := tree) hlo hhi
  have hv : p.heapAddress tree h < p.vertexCount := by unfold vertexCount; omega
  simp only [graph, List.getElem?_map, List.getElem?_range hv, Option.map_some,
    node, if_neg (Nat.not_lt.mpr hb.1), if_pos hb.2, hd.1, hd.2]

theorem graph_valid (p : Config) : GraphValid p.graph := by
  intro v n hn
  obtain ⟨hv,hnode⟩ := List.getElem?_eq_some_iff.mp hn
  have hv' : v < p.vertexCount := by simpa [p.graph_length] using hv
  have he : n = p.node v := by simpa [graph] using hnode.symm
  rw [he]
  by_cases hs : v < p.sources
  · simp [node, hs, Node.ValidAt]
  by_cases hh : v < p.heapEnd
  · let tree := (v-p.sources)/p.heapSize
    let r := (v-p.sources)%p.heapSize
    let h := p.heapSize-r
    have hr : r < p.heapSize := Nat.mod_lt _ p.heap_pos
    have hvsplit : tree*p.heapSize+r = v-p.sources := Nat.div_add_mod' _ _
    have ht : tree < p.trees := by
      unfold heapEnd at hh
      exact (Nat.div_lt_iff_lt_mul p.heap_pos).2 (by omega)
    have hlo : 0 < h := by unfold h; omega
    have hhi : h ≤ p.heapSize := by unfold h; omega
    have haddr : v = p.heapAddress tree h := by unfold heapAddress h; omega
    rw [haddr] at hn
    rw [p.heap_at ht hlo hhi] at hn
    have hn2 := Option.some.inj hn
    rw [← he, ← hn2]
    by_cases hl : h ≥ p.leaves
    · simp only [if_pos hl, Node.ValidAt]
      have hstep := Nat.mul_le_mul_right p.leaves ht
      rw [Nat.succ_mul] at hstep
      unfold secret
      unfold heapSize at hhi
      unfold sources at hs
      omega
    · simp only [if_neg hl, Node.ValidAt]
      rw [haddr]
      unfold heapAddress
      unfold heapSize at *
      omega
  · let link := v-p.heapEnd
    have hk : link+1 < p.trees := by unfold vertexCount at hv'; unfold link; omega
    have hz : 0 < p.trees := by omega
    have left := (p.heap_bounds (tree := 0) hz (h := 1) (by decide) p.heap_pos).2
    have right := (p.heap_bounds hk (h := 1) (by decide) p.heap_pos).2
    simp only [node, if_neg hs, if_neg hh, Node.ValidAt]
    change (if link=0 then p.heapAddress 0 1 else v-1) < v ∧ p.heapAddress (link+1) 1 < v
    split <;> omega

end PoissonDAG.FORS.Config
