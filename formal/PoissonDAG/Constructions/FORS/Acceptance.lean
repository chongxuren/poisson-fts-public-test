import PoissonDAG.Constructions.FORS.Prefix

namespace PoissonDAG.FORS.Config

def virtualZero (p : Config) (raw : Nat) (n : Nat) : Bool :=
  ((List.range n).map (fun j => !(raw.testBit (p.trees*p.height+j)))).all id

def virtualGate (p : Config) (n : Nat) :=
  if n=0 then 1 else 2+2*p.rawBits+(n-1)

theorem wire_virtual (p : Config) (raw n : Nat) (hn : n ≤ p.zeroBits) :
    p.wire raw (p.virtualGate n) = p.virtualZero raw n := by
  induction n with
  | zero =>
    simp [virtualGate, wire, gate, evalGate, virtualZero]
  | succ j ih =>
    have hprev := ih (by omega)
    have hbit : p.trees*p.height+j < p.rawBits := by unfold rawBits; omega
    let i := 2+2*p.rawBits+j
    have h0 : ¬i < 2 := by unfold i; omega
    have h1 : ¬i < 2+p.rawBits := by unfold i; omega
    have h2 : ¬i < 2+2*p.rawBits := by unfold i; omega
    have h3 : i < p.prefixBase := by unfold i prefixBase; omega
    have hindex : i-(2+2*p.rawBits) = j := by unfold i; omega
    have hbefore : (if j=0 then 1 else i-1) = p.virtualGate j := by
      by_cases hz : j = 0 <;> simp [virtualGate, hz, i] <;> omega
    have hprevlt : p.virtualGate j < i := by unfold virtualGate i; split <;> omega
    have hneglt : 2+p.rawBits+(p.trees*p.height+j) < i := by unfold i; omega
    have hi : p.virtualGate (j+1) = i := by simp [virtualGate, i]
    rw [hi]
    change evalGate raw (p.state raw i) (p.gate i) = _
    simp only [gate, if_neg h0, if_neg h1, if_neg h2, if_pos h3, hindex, hbefore, evalGate]
    rw [show 2+p.rawBits+p.trees*p.height+j = 2+p.rawBits+(p.trees*p.height+j) by omega,
      state_get _ _ _ _ hprevlt, state_get _ _ _ _ hneglt, hprev,
      wire_neg _ _ _ hbit]
    simp [virtualZero, List.range_succ]

theorem protected_accept_zero (p : Config) (raw : Nat) :
    p.scheme.accept raw = p.virtualZero raw p.zeroBits := by
  have hi : (if p.zeroBits=0 then 1 else p.prefixBase-1) = p.virtualGate p.zeroBits := by
    unfold virtualGate prefixBase
    split <;> omega
  have hlt : p.virtualGate p.zeroBits < p.prefixBase+p.trees*p.heapSize := by
    unfold virtualGate prefixBase
    split <;> omega
  change get ((([if p.zeroBits=0 then 1 else p.prefixBase-1] ++
    (List.range p.vertexCount).map p.disclosureGate ++ List.replicate p.vertexCount 1).map
    (get (p.state raw (p.prefixBase+p.trees*p.heapSize))))) 0 = _
  simp only [List.cons_append, List.nil_append, List.map_cons, get, List.getElem?_cons_zero,
    Option.getD_some, hi]
  exact (p.state_get raw _ _ hlt).trans (p.wire_virtual raw _ (by omega))

end PoissonDAG.FORS.Config
