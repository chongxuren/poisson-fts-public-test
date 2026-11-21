import PoissonDAG.Constructions.FORS.Literal
import PoissonDAG.Core.CircuitFacts

namespace PoissonDAG.FORS.Config

/-- Protected evaluation after the first n literal gates. -/
def state (p : Config) (raw : Nat) (n : Nat) :=
  executeGates raw ((List.range n).map p.gate)

theorem state_succ (p : Config) (raw n : Nat) :
    p.state raw (n+1) = p.state raw n ++ [evalGate raw (p.state raw n) (p.gate n)] := by
  simp [state, executeGates, List.range_succ, List.foldl_append]

theorem state_length (p : Config) (raw n : Nat) : (p.state raw n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [state_succ, ih]

def wire (p : Config) (raw i : Nat) := evalGate raw (p.state raw i) (p.gate i)

theorem state_get (p : Config) (raw n i : Nat) (hi : i < n) :
    get (p.state raw n) i = p.wire raw i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [state_succ]
    by_cases heq : i = n
    · subst i
      simp [get, state_length, wire]
    · have hlt : i < n := by omega
      simpa [get, List.getElem?_append, state_length, hlt] using ih hlt

theorem wire_input (p : Config) (raw j : Nat) (hj : j < p.rawBits) :
    p.wire raw (2+j) = raw.testBit j := by
  have h0 : ¬ 2+j < 2 := by omega
  have h1 : 2+j < 2+p.rawBits := by omega
  simp [wire, gate, h0, h1, evalGate]

theorem wire_neg (p : Config) (raw j : Nat) (hj : j < p.rawBits) :
    p.wire raw (2+p.rawBits+j) = !(raw.testBit j) := by
  have h0 : ¬ 2+p.rawBits+j < 2 := by omega
  have h1 : ¬ 2+p.rawBits+j < 2+p.rawBits := by omega
  have h2 : 2+p.rawBits+j < 2+2*p.rawBits := by omega
  have hp : 2+j < 2+p.rawBits+j := by omega
  simp [wire, gate, h0, h1, h2, evalGate, state_get p raw _ _ hp, hj]

theorem prefix_decode (p : Config) (tree h : Nat) (hlo : 1 ≤ h) (hhi : h ≤ p.heapSize) :
    (p.prefixGate tree h-p.prefixBase)/p.heapSize = tree ∧
    (p.prefixGate tree h-p.prefixBase)%p.heapSize+1 = h := by
  have hd : 0 < p.heapSize := by omega
  have hoff : h-1 < p.heapSize := by omega
  have hadd : p.prefixGate tree h-p.prefixBase = (h-1)+p.heapSize*tree := by
    unfold prefixGate
    rw [Nat.mul_comm tree p.heapSize]
    omega
  rw [hadd, Nat.add_mul_div_left _ _ hd, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt hoff, Nat.mod_eq_of_lt hoff]
  omega

private theorem prefix_case (p : Config) (tree h : Nat) :
    ¬p.prefixGate tree h < 2 ∧ ¬p.prefixGate tree h < 2+p.rawBits ∧
    ¬p.prefixGate tree h < 2+2*p.rawBits ∧ ¬p.prefixGate tree h < p.prefixBase := by
  unfold prefixGate prefixBase
  omega

theorem wire_root (p : Config) (raw tree : Nat) (hh : 1 ≤ p.heapSize) :
    p.wire raw (p.prefixGate tree 1) = true := by
  have hd := p.prefix_decode tree 1 (by decide) hh
  obtain ⟨h0,h1,h2,h3⟩ := p.prefix_case tree 1
  simp [wire, gate, h0, h1, h2, h3, hd.2, evalGate]

/-- The literal gate for heap position h is true exactly when its parent
prefix matches and the selected digest bit takes the branch leading to h. -/
theorem wire_child (p : Config) (raw tree h : Nat) (hlo : 2 ≤ h)
    (hhi : h ≤ p.heapSize) (htree : tree < p.trees) :
    p.wire raw (p.prefixGate tree h) =
      (p.wire raw (p.prefixGate tree (h/2)) &&
        (if h%2=0 then !(raw.testBit (tree*p.height+(p.height-h.log2)))
         else raw.testBit (tree*p.height+(p.height-h.log2)))) := by
  have hd := p.prefix_decode tree h (by omega) hhi
  obtain ⟨h0,h1,h2,h3⟩ := p.prefix_case tree h
  have hh : h ≠ 1 := by omega
  have hparent : p.prefixGate tree (h/2) < p.prefixGate tree h := by
    unfold prefixGate
    omega
  have hlevel : 0 < h.log2 := by
    exact (Nat.le_log2 (by omega : h ≠ 0)).2 (by simpa using hlo)
  have hheight : 0 < p.height := by
    by_contra hz
    have hp : p.height = 0 := by omega
    simp [heapSize, leaves, hp] at hhi
    omega
  have hnext : (tree+1)*p.height ≤ p.trees*p.height :=
    Nat.mul_le_mul_right p.height htree
  rw [Nat.add_mul] at hnext
  let bit := tree*p.height+(p.height-h.log2)
  have hbit : bit < p.rawBits := by unfold bit rawBits; omega
  have hi0 : 2+bit < p.prefixGate tree h := by unfold prefixGate prefixBase; omega
  have hi1 : 2+p.rawBits+bit < p.prefixGate tree h := by unfold prefixGate prefixBase; omega
  change evalGate raw _ (p.gate _) = _
  simp only [gate, if_neg h0, if_neg h1, if_neg h2, if_neg h3, hd.2, hd.1, if_neg hh, evalGate]
  rw [state_get p raw _ _ hparent]
  change (_ && get _ (if h%2=0 then 2+p.rawBits+bit else 2+bit)) = _
  by_cases he : h%2=0
  · simp only [if_pos he, state_get p raw _ _ hi1, wire_neg p raw bit hbit] <;> rfl
  · simp only [if_neg he, state_get p raw _ _ hi0, wire_input p raw bit hbit] <;> rfl

end PoissonDAG.FORS.Config
