import PoissonDAG.Constructions.FORS.Projection

namespace PoissonDAG.FORS.Config

private theorem bit_as_remainder (raw bit : Nat) :
    (raw.testBit bit).toNat = raw / 2^bit % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases he : raw / 2^bit % 2 = 1
  · simp [he]
  · have hzero : raw / 2^bit % 2 = 0 := by omega
    simp [hzero]

theorem projectedHeap_block (p : Config) (raw tree depth : Nat) (hd : depth ≤ p.height) :
    p.projectedHeap raw tree depth = 2^depth +
      raw / 2^(tree*p.height+(p.height-depth)) % 2^depth := by
  induction depth with
  | zero => simp [projectedHeap, Nat.mod_one]
  | succ n ih =>
    let b := tree*p.height+(p.height-(n+1))
    have hshift : tree*p.height+(p.height-n) = b+1 := by unfold b; omega
    rw [projectedHeap, ih (by omega), hshift, bit_as_remainder]
    change 2*(2^n+raw/2^(b+1)%2^n)+raw/2^b%2 =
      2^(n+1)+raw/2^b%2^(n+1)
    rw [Nat.pow_succ 2 b, ← Nat.div_div_eq_div_mul]
    rw [show 2^(n+1) = 2*2^n by rw [Nat.pow_succ, Nat.mul_comm]]
    rw [Nat.mod_mul (x := raw / 2^b) (a := 2) (b := 2^n)]
    omega

/-- The digest projection in the protected source-incidence theorem is exactly
a base-2^height digit of the original raw input. -/
theorem projectedIndex_block (p : Config) (raw tree : Nat) :
    p.projectedIndex raw tree = raw / 2^(tree*p.height) % 2^p.height := by
  simp [projectedIndex, p.projectedHeap_block raw tree p.height (by omega), leaves]

theorem covered_requires_block (p : Config) (target tree : Nat) (history : List Nat)
    (ht : tree < p.trees) (hc : p.scheme.covered history target = true) :
    ∃ raw ∈ history, raw / 2^(tree*p.height) % 2^p.height =
      target / 2^(tree*p.height) % 2^p.height := by
  simpa only [p.projectedIndex_block] using p.covered_requires_index target tree history ht hc

end PoissonDAG.FORS.Config
