import PoissonDAG.Constructions.FORS.Geometry
import PoissonDAG.Constructions.FORS.AcceptedRange
import PoissonDAG.Core.AIGCompiler

namespace PoissonDAG.FORS.Config

def gateCount (p : Config) := p.prefixBase+p.trees*p.heapSize

theorem prefix_bounded (p : Config) {tree h : Nat} (ht : tree < p.trees)
    (hh : h ≤ p.heapSize) : p.prefixGate tree h < p.gateCount := by
  have hpos := p.heap_pos
  have hstep := Nat.mul_le_mul_right p.heapSize ht
  rw [Nat.succ_mul] at hstep
  unfold prefixGate gateCount
  omega

theorem valid_gate (p : Config) {i : Nat} (hi : i < p.gateCount) :
    AIGCompiler.ValidGate p.rawBits i (p.gate i) := by
  unfold gate
  split
  · trivial
  split
  · change i-2 < p.rawBits
    omega
  split
  · change 2+(i-(2+p.rawBits)) < i
    omega
  split
  · simp only [AIGCompiler.ValidGate]
    unfold prefixBase rawBits at *
    split <;> omega
  · let j := i-p.prefixBase
    let tree := j/p.heapSize
    let h := j%p.heapSize+1
    have htree : tree < p.trees := by
      apply (Nat.div_lt_iff_lt_mul p.heap_pos).2
      unfold gateCount at hi
      unfold j
      omega
    have hhi : h ≤ p.heapSize := by have := Nat.mod_lt j p.heap_pos; unfold h; omega
    have hadd : tree*p.heapSize+j%p.heapSize = j := Nat.div_add_mod' _ _
    have hi_eq : i = p.prefixGate tree h := by unfold prefixGate h j at *; omega
    change AIGCompiler.ValidGate _ i (if h=1 then .constant true else
      .conj (p.prefixGate tree (h/2)) (if h%2=0 then
        2+p.rawBits+(tree*p.height+(p.height-h.log2)) else
        2+(tree*p.height+(p.height-h.log2))))
    split
    · trivial
    · have hlo : 2 ≤ h := by unfold h at *; omega
      have hlevel : 1 ≤ h.log2 := (Nat.le_log2 (by omega)).2 (by simpa using hlo)
      have hheight : 0 < p.height := by
        by_contra hn
        have hp : p.height=0 := by omega
        simp [heapSize,leaves,hp] at hhi
        omega
      have hstep := Nat.mul_le_mul_right p.height htree
      rw [Nat.succ_mul] at hstep
      change _ < i ∧ _ < i
      rw [hi_eq]
      unfold prefixGate prefixBase rawBits
      split <;> omega

theorem disclosure_bounded (p : Config) {v : Nat} : p.disclosureGate v < p.gateCount := by
  have hleaf : 0 < p.leaves := Nat.two_pow_pos _
  have hheap := p.heap_pos
  unfold disclosureGate
  split
  · rename_i h
    have ht : v/p.leaves < p.trees := (Nat.div_lt_iff_lt_mul hleaf).2 h
    apply p.prefix_bounded ht
    have := Nat.mod_lt v hleaf
    unfold heapSize
    omega
  split
  · rename_i hh
    have ht : (v-p.sources)/p.heapSize < p.trees := by
      apply (Nat.div_lt_iff_lt_mul hheap).2
      unfold heapEnd at hh
      omega
    let h := p.heapSize-(v-p.sources)%p.heapSize
    have hupper : h ≤ p.heapSize := Nat.sub_le _ _
    have hodd : p.heapSize%2=1 := by unfold heapSize; omega
    change (if h=1 then 0 else p.prefixGate _ (if h%2=0 then h+1 else h-1)) < _
    split
    · unfold gateCount prefixBase; omega
    · apply p.prefix_bounded ht
      split <;> omega
  · unfold gateCount prefixBase; omega

theorem encoder_valid (p : Config) : p.encoder.Valid := by
  constructor
  · intro i g hg
    obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp hg
    have hbound : i < p.gateCount := by simpa [encoder,gateCount] using hi
    have hgate : g = p.gate i := by simpa [encoder] using he.symm
    rw [hgate]
    exact p.valid_gate hbound
  · intro o ho
    change o < ((List.range p.gateCount).map p.gate).length
    rw [List.length_map,List.length_range]
    change o ∈ [if p.zeroBits=0 then 1 else p.prefixBase-1] ++
      (List.range p.vertexCount).map p.disclosureGate ++ List.replicate p.vertexCount 1 at ho
    simp only [List.mem_append,List.mem_singleton,List.mem_map,List.mem_replicate] at ho
    rcases ho with (h | ⟨i,_,rfl⟩) | ⟨_,h⟩
    · subst o
      unfold gateCount prefixBase
      split <;> omega
    · exact p.disclosure_bounded
    · subst o; unfold gateCount prefixBase; omega

theorem wellFormed (p : Config) (ht : 0 < p.trees) (hr : 0 < p.rawBits) : p.scheme.WellFormed := by
  have hp := Nat.mul_pos ht p.heap_pos
  refine ⟨?_,hr,p.encoder_valid,p.output_length,p.graph_valid,?_⟩
  · change 0 < p.graph.length
    rw [graph_length]
    unfold vertexCount heapEnd
    omega
  · simp [p.accepted_eq_range,messageCount]

end PoissonDAG.FORS.Config
