import PoissonDAG.Constructions.FORS.Frontier
import PoissonDAG.Constructions.GRSCC.CostBasic

namespace PoissonDAG.FORS.Config

/-- Position zero transmits the secret. Each positive position transmits the
sibling of the selected vertex at that depth. -/
def openingAt (p : Config) (raw : Nat) (tree : Fin p.trees) (j : Fin (p.height+1)) :=
  if j.val = 0 then p.secret tree (p.projectedIndex raw tree)
  else p.heapAddress tree (sibling (p.projectedHeap raw tree j))

private theorem false_gate (p : Config) (raw v : Nat) (hv : v < p.vertexCount)
    (hz : p.disclosureGate v = 0) : get (p.scheme.frontier raw) v = false := by
  rw [p.get_frontier_gate raw v hv, hz, p.state_get]
  · rfl
  · unfold prefixBase; omega

theorem mem_openings_of_frontier (p : Config) (raw v : Nat) (hv : v < p.vertexCount)
    (front : get (p.scheme.frontier raw) v = true) :
    ∃ tree : Fin p.trees, ∃ j : Fin (p.height+1), v = p.openingAt raw tree j := by
  have hl : 0 < p.leaves := Nat.two_pow_pos _
  by_cases hs : v < p.sources
  · let i := v/p.leaves
    let x := v%p.leaves
    have hx : x < p.leaves := Nat.mod_lt _ hl
    have hi : i < p.trees := (Nat.div_lt_iff_lt_mul hl).2 hs
    have addr : p.secret i x = v := Nat.div_add_mod' _ _
    have hidx := (p.secret_frontier_iff_index raw i x hi hx).1 (addr ▸ front)
    exact ⟨⟨i,hi⟩, ⟨0,by omega⟩, by simpa [openingAt,hidx] using addr.symm⟩
  by_cases hh : v < p.heapEnd
  · let i := (v-p.sources)/p.heapSize
    let off := (v-p.sources)%p.heapSize
    let h := p.heapSize-off
    have hoff : off < p.heapSize := Nat.mod_lt _ p.heap_pos
    have he : i*p.heapSize+off = v-p.sources := Nat.div_add_mod' _ _
    have hi : i < p.trees := (Nat.div_lt_iff_lt_mul p.heap_pos).2 (by unfold heapEnd at hh; omega)
    have hlo : 0 < h := by unfold h; omega
    have hhi : h ≤ p.heapSize := by unfold h; omega
    have addr : v = p.heapAddress i h := by unfold heapAddress h; omega
    have hn : h ≠ 1 := by
      intro h1
      have hz : p.disclosureGate v = 0 := by
        simp only [disclosureGate, if_neg hs, if_pos hh, show p.heapSize-(v-p.sources)%p.heapSize=h from rfl, h1, if_true]
      rw [p.false_gate raw v hv hz] at front
      contradiction
    have sib := p.sibling_bounds (h := h) (by omega) hhi
    have hsel := (p.heap_prefix_iff raw i (sibling h) (by omega)).1
      ((p.heap_frontier raw i h hi (by omega) hhi).symm.trans (addr ▸ front))
    let d := (sibling h).log2
    have hpow := (Nat.log2_eq_iff (show sibling h ≠ 0 by omega)).1 (rfl : (sibling h).log2 = d)
    change 2^d ≤ sibling h ∧ sibling h < 2^(d+1) at hpow
    change p.projectedHeap raw i d = sibling h at hsel
    have hd : d ≤ p.height := by
      have hp : sibling h < 2^(p.height+1) := by
        have ht := sib.2.1
        unfold heapSize leaves at ht
        rw [Nat.pow_succ]
        omega
      exact Nat.le_of_lt_succ ((Nat.log2_lt (by omega)).2 hp)
    have hdpos : d ≠ 0 := by
      intro hz
      rw [hz] at hpow
      omega
    refine ⟨⟨i,hi⟩, ⟨d,by omega⟩, ?_⟩
    simpa only [openingAt, Fin.val_mk, if_neg hdpos, hsel, sib.2.2.1] using addr
  · have hz : p.disclosureGate v = 0 := by simp [disclosureGate, hs, hh]
    rw [p.false_gate raw v hv hz] at front
    contradiction

private theorem count_indices (xs : List Bool) :
    weight xs = ((Finset.range xs.length).filter (fun i => get xs i = true)).card := by
  have heq : (List.range xs.length).map (get xs) = xs := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp [get, List.getElem?_eq_getElem h₂]
  let selected := (List.range xs.length).filter (get xs)
  have hlen : weight xs = selected.length := by
    conv_lhs => rw [← heq]
    unfold weight
    rw [List.count_eq_countP, List.countP_map]
    have hpred : ((· == true) ∘ get xs) = get xs := by
      funext i
      cases hv : get xs i <;> simp [Function.comp_def, hv]
    rw [hpred, List.countP_eq_length_filter]
  rw [hlen, ← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_range (n:=xs.length)))]
  simp [selected, List.toFinset_filter, List.toFinset_range]

theorem frontier_weight (p : Config) (raw : Nat) :
    weight (p.scheme.frontier raw) ≤ p.trees * (p.height+1) := by
  classical
  let addr (x : Fin p.trees × Fin (p.height+1)) := p.openingAt raw x.1 x.2
  rw [count_indices]
  have hlen : (p.scheme.frontier raw).length = p.vertexCount :=
    (GRSCC.scheme_frontier_length p.scheme p.output_length raw).trans p.graph_length
  have hsub : ((Finset.range (p.scheme.frontier raw).length).filter
      (fun i => get (p.scheme.frontier raw) i = true)) ⊆ Finset.univ.image addr := by
    intro v hv
    obtain ⟨hv,hf⟩ := Finset.mem_filter.mp hv
    obtain ⟨tree,j,he⟩ := p.mem_openings_of_frontier raw v (hlen ▸ Finset.mem_range.mp hv) hf
    exact Finset.mem_image.mpr ⟨(tree,j),Finset.mem_univ _,he.symm⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

theorem size_upper (p : Config) :
    p.scheme.size ≤ (p.counterBits+7)/8 + 16*(p.trees*(p.height+1)) := by
  unfold Scheme.size
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply GRSCC.foldMax_le _ _ _ (Nat.zero_le _)
  intro w hw
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hw
  exact p.frontier_weight raw

end PoissonDAG.FORS.Config
