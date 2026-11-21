import PoissonDAG.Constructions.FORS.AuthPath
import PoissonDAG.Constructions.FORS.Size

namespace PoissonDAG.FORS.Config

theorem aggregate_hidden (p : Config) (raw j : Nat) (hj : j+1 < p.trees) :
    get (p.scheme.frontier raw) (p.heapEnd+j) = false := by
  have hv : p.heapEnd+j < p.vertexCount := by unfold vertexCount; omega
  have hs : ¬p.heapEnd+j < p.sources := by unfold heapEnd; omega
  rw [p.get_frontier_gate raw _ hv]
  simp [disclosureGate,hs,zero_wire]

theorem aggregate_known (p : Config) (raw j : Nat) (hj : j+1 < p.trees) :
    get (close p.graph (p.scheme.frontier raw) (p.scheme.plan raw)).1 (p.heapEnd+j) = true := by
  apply (p.complete_scan raw _ ?_).2 (p.aggregate_derives raw j hj)
  rw [graph_length]
  unfold vertexCount
  omega

theorem root_is_aggregate (p : Config) (ht : 2 ≤ p.trees) :
    p.graph.length-1 = p.heapEnd+(p.trees-2) := by rw [graph_length]; unfold vertexCount; omega

theorem aggregate_lifts (p : Config) (raw label j : Nat) (hj : j+1 < p.trees)
    (uses : p.follows raw label (p.heapEnd+j)) :
    p.follows raw label (p.graph.length-1) := by
  have ht : 2 ≤ p.trees := by omega
  rw [p.root_is_aggregate ht]
  have target (n : Nat) (hjn : j ≤ n) (hn : n+1 < p.trees) :
      p.follows raw label (p.heapEnd+n) := by
    induction n, hjn using Nat.le_induction with
    | base => exact uses
    | succ n _ ih =>
      have hg := p.aggregate_at hn
      rw [if_neg (by omega : n+1≠0)] at hg
      apply V2.Uses.hash (ih (by omega)) (p.aggregate_hidden raw _ hn) (p.aggregate_known raw _ hn)
      simp [V2.IsParent,hg]
  exact target (p.trees-2) (by omega) (by omega)

theorem tree_lifts (p : Config) (raw label tree : Nat) (ht : tree < p.trees) (hk : 2 ≤ p.trees)
    (uses : p.follows raw label (p.heapAddress tree 1)) : p.follows raw label (p.graph.length-1) := by
  cases tree with
  | zero =>
    have hf : 0+1 < p.trees := by omega
    apply p.aggregate_lifts raw label 0 hf
    apply V2.Uses.hash uses (p.aggregate_hidden raw 0 hf) (p.aggregate_known raw 0 hf)
    have hlookup : p.graph[p.heapEnd]? = some (.binary (p.heapAddress 0 1) (p.heapAddress 1 1)) := by
      simpa using p.aggregate_at hf
    simp [V2.IsParent,hlookup]
  | succ tree =>
    apply p.aggregate_lifts raw label tree ht
    apply V2.Uses.hash uses (p.aggregate_hidden raw tree ht) (p.aggregate_known raw tree ht)
    simp only [V2.IsParent,p.aggregate_at ht]
    exact Or.inr trivial

theorem authenticated (p : Config) (raw : Nat) (ht : 2 ≤ p.trees) :
    V2.Authenticated p.graph (p.scheme.frontier raw) (p.scheme.plan raw) := by
  refine ⟨?_,?_,?_⟩
  · rw [p.root_is_aggregate ht]
    exact p.aggregate_hidden raw _ (by omega)
  · rw [p.root_is_aggregate ht]
    exact p.aggregate_known raw _ (by omega)
  · intro v hv
    obtain ⟨tree,j,hv'⟩ := p.mem_openings_of_frontier raw v (by simpa [graph_length] using v.isLt) hv
    rw [hv']
    apply p.tree_lifts raw _ tree tree.isLt ht
    by_cases hj : j.val=0
    · simpa [openingAt,hj] using p.secret_to_tree raw tree tree.isLt
    · have hd : j.val-1 < p.height := by have := j.isLt; omega
      have he : j.val-1+1 = j.val := by omega
      simpa [openingAt,hj,he] using p.sibling_to_tree raw tree (j.val-1) tree.isLt hd

end PoissonDAG.FORS.Config
