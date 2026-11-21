import PoissonDAG.Constructions.FORS.Geometry
import PoissonDAG.Constructions.FORS.Projection

namespace PoissonDAG.FORS.Config

def sibling (h : Nat) := if h%2=0 then h+1 else h-1

theorem sibling_bounds (p : Config) {h : Nat} (hlo : 2 ≤ h) (hhi : h ≤ p.heapSize) :
    2 ≤ sibling h ∧ sibling h ≤ p.heapSize ∧ sibling (sibling h) = h ∧
      (sibling h)/2 = h/2 ∧ sibling h ≠ h := by
  have ht : 0 < p.leaves := Nat.two_pow_pos _
  unfold heapSize at *
  unfold sibling
  split <;> split <;> omega

theorem heap_frontier (p : Config) (raw tree h : Nat) (ht : tree < p.trees)
    (hlo : 2 ≤ h) (hhi : h ≤ p.heapSize) :
    get (p.scheme.frontier raw) (p.heapAddress tree h) = p.prefixMatches raw tree (sibling h) := by
  have loc := p.heap_locate (tree := tree) (h := h) (by omega) hhi
  have bounds := p.heap_bounds ht (h := h) (by omega) hhi
  have sib := p.sibling_bounds hlo hhi
  have hsize : p.heapAddress tree h < p.vertexCount := by unfold vertexCount; omega
  have hout : p.disclosureGate (p.heapAddress tree h) = p.prefixGate tree (sibling h) := by
    simp only [disclosureGate, if_neg (Nat.not_lt.mpr bounds.1), if_pos bounds.2,loc.1,loc.2,
      if_neg (show h≠1 by omega),sibling]
  have hb : p.prefixGate tree (sibling h) < p.prefixBase+p.trees*p.heapSize := by
    have hstep := Nat.mul_le_mul_right p.heapSize ht
    rw [Nat.succ_mul] at hstep
    unfold prefixGate
    omega
  rw [p.get_frontier_gate raw _ hsize,hout,p.state_get raw _ _ hb,
    p.prefix_wire_matches raw tree ht _ (by omega) sib.2.1]

theorem path_bounds (p : Config) (raw tree d : Nat) (hd : d ≤ p.height) :
    0 < p.projectedHeap raw tree d ∧ p.projectedHeap raw tree d ≤ p.heapSize ∧
      (p.projectedHeap raw tree d).log2 = d := by
  have hr := p.projectedHeap_range raw tree d
  have hpow := Nat.two_pow_pos d
  have hgt : p.projectedHeap raw tree d ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hgt).2 hr
  have hmon := Nat.pow_le_pow_right (by decide : 0 < 2) hd
  rw [Nat.pow_succ] at hr
  unfold heapSize leaves
  omega

theorem path_and_sibling (p : Config) (raw tree d : Nat) (ht : tree < p.trees)
    (hd : d+1 ≤ p.height) :
    let h := p.projectedHeap raw tree (d+1)
    get (p.scheme.frontier raw) (p.heapAddress tree h) = false ∧
      get (p.scheme.frontier raw) (p.heapAddress tree (sibling h)) = true := by
  let h := p.projectedHeap raw tree (d+1)
  change get _ (p.heapAddress tree h) = false ∧ get _ (p.heapAddress tree (sibling h)) = true
  have hr := p.path_bounds raw tree (d+1) hd
  have hlog : h.log2 = d+1 := hr.2.2
  have hgt : 2 ≤ h := by
    have hpow := (p.projectedHeap_range raw tree (d+1)).1
    rw [Nat.pow_succ] at hpow
    have hp := Nat.two_pow_pos d
    unfold h
    omega
  have hhi : h ≤ p.heapSize := hr.2.1
  have sib := p.sibling_bounds hgt hhi
  have same : (sibling h).log2 = h.log2 := by
    rw [Nat.log2_def (sibling h),Nat.log2_def h,if_pos sib.1,if_pos hgt,sib.2.2.2.1]
  rw [p.heap_frontier raw tree h ht hgt hhi,
    p.heap_frontier raw tree (sibling h) ht sib.1 sib.2.1,sib.2.2.1]
  constructor
  · apply Bool.eq_false_iff.mpr
    intro hm
    have hwrong := (p.heap_prefix_iff raw tree (sibling h) (by omega)).1 hm
    rw [same,hlog] at hwrong
    exact sib.2.2.2.2 hwrong.symm
  · apply (p.heap_prefix_iff raw tree h (by omega)).2
    rw [hlog]

end PoissonDAG.FORS.Config
