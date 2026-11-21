import PoissonDAG.Constructions.FORS.Prefix

namespace PoissonDAG.FORS.Config

/-- Read the specified MSB-first prefix directly from the raw digest. The heap
number h encodes its path with an implicit leading 1. -/
def prefixMatches (p : Config) (raw tree h : Nat) : Bool :=
  if h < 2 then true
  else p.prefixMatches raw tree (h/2) &&
    (if h%2=0 then !(raw.testBit (tree*p.height+(p.height-h.log2)))
     else raw.testBit (tree*p.height+(p.height-h.log2)))
termination_by h
decreasing_by omega

theorem prefix_wire_matches (p : Config) (raw tree : Nat) (htree : tree < p.trees)
    (h : Nat) (hlo : 1 ≤ h) (hhi : h ≤ p.heapSize) :
    p.wire raw (p.prefixGate tree h) = p.prefixMatches raw tree h := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hsmall : h < 2
    · have heq : h = 1 := by omega
      subst h
      rw [p.wire_root raw tree hhi, prefixMatches]
      rfl
    · rw [p.wire_child raw tree h (by omega) hhi htree, prefixMatches,
          if_neg hsmall, ih (h/2) (by omega) (by omega) (by omega)]

theorem get_frontier_gate (p : Config) (raw v : Nat) (hv : v < p.vertexCount) :
    get (p.scheme.frontier raw) v =
      get (p.state raw (p.prefixBase+p.trees*p.heapSize)) (p.disclosureGate v) := by
  let read := get (p.state raw (p.prefixBase+p.trees*p.heapSize))
  let ds := (List.range p.vertexCount).map p.disclosureGate
  have hd : (ds.map read).length = p.vertexCount := by simp [ds]
  change get ((([if p.zeroBits = 0 then 1 else p.prefixBase-1] ++ ds ++
    List.replicate p.vertexCount 1).map read).drop 1 |>.take p.graph.length) v = _
  rw [graph_length]
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.drop_succ_cons, List.drop_zero, List.take_left' hd]
  change ((ds.map read)[v]?).getD false = _
  simp [ds, List.getElem?_map, List.getElem?_range hv, read]

theorem secret_frontier (p : Config) (raw tree index : Nat)
    (ht : tree < p.trees) (hj : index < p.leaves) :
    get (p.scheme.frontier raw) (p.secret tree index) =
      p.prefixMatches raw tree (p.leaves+index) := by
  have hpos : 0 < p.leaves := by omega
  have hsecret : p.secret tree index < p.sources := by
    have hstep := Nat.mul_le_mul_right p.leaves (show tree+1 ≤ p.trees from ht)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    unfold secret sources
    omega
  have hv : p.secret tree index < p.vertexCount := by
    unfold vertexCount heapEnd
    omega
  have hjdiv : p.secret tree index/p.leaves = tree := by
    unfold secret
    rw [Nat.add_comm, Nat.mul_comm tree, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj]
    omega
  have hjmod : p.secret tree index%p.leaves = index := by
    simp [secret, Nat.mod_eq_of_lt hj]
  have hh : p.leaves+index ≤ p.heapSize := by unfold heapSize; omega
  have hgate : p.disclosureGate (p.secret tree index) = p.prefixGate tree (p.leaves+index) := by
    simp [disclosureGate, hsecret, hjdiv, hjmod]
  have hbound : p.prefixGate tree (p.leaves+index) < p.prefixBase+p.trees*p.heapSize := by
    have hstep := Nat.mul_le_mul_right p.heapSize (show tree+1 ≤ p.trees from ht)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    unfold prefixGate
    omega
  rw [p.get_frontier_gate raw _ hv, hgate, p.state_get raw _ _ hbound,
      p.prefix_wire_matches raw tree ht _ (by omega) hh]

/-- Concrete protected coverage requires every selected physical-tree path to
have appeared in some prior raw input, with unrestricted pooled closure. -/
theorem covered_requires_prefix (p : Config) (target tree index : Nat) (history : List Nat)
    (ht : tree < p.trees) (hj : index < p.leaves)
    (hselected : p.prefixMatches target tree (p.leaves+index) = true)
    (hc : p.scheme.covered history target = true) :
    ∃ raw ∈ history, p.prefixMatches raw tree (p.leaves+index) = true := by
  have hstep := Nat.mul_le_mul_right p.leaves (show tree+1 ≤ p.trees from ht)
  rw [Nat.add_mul, Nat.one_mul] at hstep
  have hs : p.secret tree index < p.sources := by unfold secret sources; omega
  have hHeap : 0 < p.heapSize := by unfold heapSize; omega
  have hNonempty : 0 < p.trees*p.heapSize := Nat.mul_pos (by omega) hHeap
  have hr : p.scheme.graph.length-1 ≠ p.secret tree index := by
    change p.graph.length-1 ≠ _
    rw [graph_length]
    unfold vertexCount heapEnd
    omega
  obtain ⟨raw, hh, hraw⟩ := p.source_has_history hs hr
    ((p.secret_frontier target tree index ht hj).trans hselected) hc
  exact ⟨raw, hh, (p.secret_frontier raw tree index ht hj).symm.trans hraw⟩

end PoissonDAG.FORS.Config
