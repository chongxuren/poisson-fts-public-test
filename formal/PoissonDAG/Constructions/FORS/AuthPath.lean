import PoissonDAG.Constructions.FORS.Correctness
import PoissonDAG.V2.Model

namespace PoissonDAG.FORS.Config

abbrev follows (p : Config) (raw label v : Nat) :=
  V2.Uses p.graph (p.scheme.frontier raw) (close p.graph (p.scheme.frontier raw) (p.scheme.plan raw)).1 label v

theorem zero_wire (p : Config) (raw : Nat) :
    get (p.state raw (p.prefixBase+p.trees*p.heapSize)) 0 = false := by
  have hh : 0 < p.prefixBase+p.trees*p.heapSize := by unfold prefixBase; omega
  rw [p.state_get raw _ _ hh]
  simp [wire,gate,evalGate]

theorem treeRoot_hidden (p : Config) (raw tree : Nat) (ht : tree < p.trees) :
    get (p.scheme.frontier raw) (p.heapAddress tree 1) = false := by
  have hb := p.heap_bounds ht (h := 1) (by decide) p.heap_pos
  have hl := p.heap_locate (tree := tree) (h := 1) (by decide) p.heap_pos
  have hsize : p.heapAddress tree 1 < p.vertexCount := by unfold vertexCount; omega
  rw [p.get_frontier_gate raw _ hsize]
  simp [disclosureGate,Nat.not_lt.mpr hb.1,hb.2,hl.2,zero_wire]

theorem path_hidden (p : Config) (raw tree d : Nat) (ht : tree < p.trees) (hd : d ≤ p.height) :
    get (p.scheme.frontier raw) (p.heapAddress tree (p.projectedHeap raw tree d)) = false := by
  cases d with
  | zero => exact p.treeRoot_hidden raw tree ht
  | succ d => exact (p.path_and_sibling raw tree d ht hd).1

theorem path_known (p : Config) (raw tree d : Nat) (ht : tree < p.trees) (hd : d ≤ p.height) :
    get (close p.graph (p.scheme.frontier raw) (p.scheme.plan raw)).1
      (p.heapAddress tree (p.projectedHeap raw tree d)) = true := by
  have hr := p.path_bounds raw tree d hd
  have hb := (p.heap_bounds ht hr.1 hr.2.1).2
  apply (p.complete_scan raw _ ?_).2 (p.path_derives raw tree d ht hd)
  rw [graph_length]
  unfold vertexCount
  omega

theorem path_parents (p : Config) (raw tree d : Nat) (ht : tree < p.trees) (hd : d < p.height) :
    let a := p.heapAddress tree
    let h := p.projectedHeap raw tree d
    let c := p.projectedHeap raw tree (d+1)
    V2.IsParent p.graph (a c) (a h) ∧ V2.IsParent p.graph (a (sibling c)) (a h) := by
  let h := p.projectedHeap raw tree d
  have hp := p.path_bounds raw tree d (by omega)
  have hlt : h < p.leaves := by
    have hu := (p.projectedHeap_range raw tree d).2
    have hm := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    unfold h leaves
    omega
  have hn := p.heap_at ht hp.1 hp.2.1
  have hlt' : p.projectedHeap raw tree d < p.leaves := hlt
  rw [if_neg (Nat.not_le.mpr hlt')] at hn
  dsimp only
  simp only [V2.IsParent,hn,projectedHeap]
  cases raw.testBit (tree*p.height+(p.height-(d+1))) <;>
    simp [sibling,Nat.add_mod]

theorem path_lifts (p : Config) (raw label tree d : Nat) (ht : tree < p.trees) (hd : d ≤ p.height)
    (uses : p.follows raw label (p.heapAddress tree (p.projectedHeap raw tree d))) :
    p.follows raw label (p.heapAddress tree 1) := by
  induction d with
  | zero => exact uses
  | succ d ih =>
    apply ih (by omega)
    exact .hash uses (p.path_hidden raw tree d ht (by omega))
      (p.path_known raw tree d ht (by omega)) (p.path_parents raw tree d ht hd).1

theorem secret_to_tree (p : Config) (raw tree : Nat) (ht : tree < p.trees) :
    p.follows raw (p.secret tree (p.projectedIndex raw tree)) (p.heapAddress tree 1) := by
  let j := p.projectedIndex raw tree
  have hfront := (p.secret_frontier_iff_index raw tree j ht (p.projectedIndex_lt raw tree)).2 rfl
  have hr := p.path_bounds raw tree p.height (by omega)
  have hl : p.leaves ≤ p.projectedHeap raw tree p.height := (p.projectedHeap_range raw tree p.height).1
  have hn := p.heap_at ht hr.1 hr.2.1
  rw [if_pos hl] at hn
  apply p.path_lifts raw _ tree p.height ht (by omega)
  apply V2.Uses.hash (.input hfront) (p.path_hidden raw tree _ ht (by omega))
    (p.path_known raw tree _ ht (by omega))
  simp only [V2.IsParent,hn]
  rfl

theorem sibling_to_tree (p : Config) (raw tree d : Nat) (ht : tree < p.trees) (hd : d < p.height) :
    p.follows raw (p.heapAddress tree (sibling (p.projectedHeap raw tree (d+1))))
      (p.heapAddress tree 1) := by
  apply p.path_lifts raw _ tree d ht (by omega)
  exact .hash (.input (p.path_and_sibling raw tree d ht hd).2)
    (p.path_hidden raw tree d ht (by omega)) (p.path_known raw tree d ht (by omega))
    (p.path_parents raw tree d ht hd).2

end PoissonDAG.FORS.Config
