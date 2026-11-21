import PoissonDAG.Constructions.FORS.Incidence

namespace PoissonDAG.FORS.Config

/-- Walk down a tree for depth positions, consuming one actual digest bit per
edge. The leading 1 in the heap index is retained. -/
def projectedHeap (p : Config) (raw tree : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => 2*p.projectedHeap raw tree n +
      (raw.testBit (tree*p.height+(p.height-(n+1)))).toNat

theorem heap_prefix_iff (p : Config) (raw tree h : Nat) (hh : 1 ≤ h) :
    p.prefixMatches raw tree h = true ↔ p.projectedHeap raw tree h.log2 = h := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hs : h < 2
    · have : h = 1 := by omega
      subst h
      rw [prefixMatches]
      change true = true ↔ (1:Nat) = 1
      simp
    · have hd : h.log2 = (h/2).log2+1 := by rw [Nat.log2_def h, if_pos (by omega)]
      have hprev := ih (h/2) (by omega) (by omega)
      rw [prefixMatches, if_neg hs, Bool.and_eq_true, hprev, hd, projectedHeap]
      cases hb : raw.testBit (tree*p.height+(p.height-((h/2).log2+1))) <;>
        by_cases he : h%2=0 <;> simp [hb, he] <;> omega

theorem projectedHeap_range (p : Config) (raw tree n : Nat) :
    2^n ≤ p.projectedHeap raw tree n ∧ p.projectedHeap raw tree n < 2^(n+1) := by
  induction n with
  | zero => simp [projectedHeap]
  | succ n ih =>
    obtain ⟨hl, hu⟩ := ih
    rw [Nat.pow_succ] at hu
    simp only [projectedHeap, Nat.pow_succ]
    cases raw.testBit (tree*p.height+(p.height-(n+1))) <;> simp <;> omega

def projectedIndex (p : Config) (raw tree : Nat) :=
  p.projectedHeap raw tree p.height - p.leaves

theorem projectedIndex_lt (p : Config) (raw tree : Nat) :
    p.projectedIndex raw tree < p.leaves := by
  have hh := p.projectedHeap_range raw tree p.height
  rw [Nat.pow_succ] at hh
  unfold projectedIndex leaves
  omega

theorem secret_frontier_iff_index (p : Config) (raw tree index : Nat)
    (ht : tree < p.trees) (hi : index < p.leaves) :
    get (p.scheme.frontier raw) (p.secret tree index) = true ↔
    p.projectedIndex raw tree = index := by
  have hp : 0 < p.leaves := by omega
  have hlog : (p.leaves+index).log2 = p.height := by
    apply (Nat.log2_eq_iff (by omega)).2
    unfold leaves at hi ⊢
    rw [Nat.pow_succ]
    omega
  have hrange := (p.projectedHeap_range raw tree p.height).1
  change p.leaves ≤ p.projectedHeap raw tree p.height at hrange
  rw [p.secret_frontier raw tree index ht hi, p.heap_prefix_iff raw tree _ (by omega), hlog]
  unfold projectedIndex
  omega

theorem covered_requires_index (p : Config) (target tree : Nat) (history : List Nat)
    (ht : tree < p.trees) (hc : p.scheme.covered history target = true) :
    ∃ raw ∈ history, p.projectedIndex raw tree = p.projectedIndex target tree := by
  let idx := p.projectedIndex target tree
  have hj : idx < p.leaves := p.projectedIndex_lt target tree
  have hs := (p.secret_frontier_iff_index target tree idx ht hj).2 rfl
  rw [p.secret_frontier target tree idx ht hj] at hs
  obtain ⟨raw,hh,hr⟩ := p.covered_requires_prefix target tree idx history ht hj hs hc
  rw [← p.secret_frontier raw tree idx ht hj] at hr
  exact ⟨raw,hh,(p.secret_frontier_iff_index raw tree idx ht hj).1 hr⟩

end PoissonDAG.FORS.Config
