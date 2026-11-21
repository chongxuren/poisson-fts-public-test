import PoissonDAG.Constructions.FORS.Acceptance

namespace PoissonDAG.FORS.Config

def messageCount (p : Config) := 2^(p.trees*p.height)

theorem accept_iff_lt (p : Config) (raw : Nat) (hr : raw < 2^p.rawBits) :
    p.scheme.accept raw = true ↔ raw < p.messageCount := by
  rw [p.protected_accept_zero]
  simp only [virtualZero, List.all_map, List.all_eq_true, List.mem_range]
  change (∀ j < p.zeroBits, (!(raw.testBit (p.trees*p.height+j))) = true) ↔ _
  constructor
  · intro ha
    by_contra hn
    have hmin : 2^(p.trees*p.height) ≤ raw := Nat.le_of_not_gt hn
    have hp : 0 < 2^(p.trees*p.height) := by positivity
    have hne : raw ≠ 0 := by omega
    have hlo := (Nat.le_log2 hne).2 hmin
    have hhi := (Nat.log2_lt hne).2 hr
    unfold rawBits at hhi
    have hz := ha (raw.log2-p.trees*p.height) (by omega)
    rw [show p.trees*p.height+(raw.log2-p.trees*p.height) = raw.log2 by omega,
      Nat.testBit_log2 hne] at hz
    contradiction
  · intro ha j _
    have hpow : 2^(p.trees*p.height) ≤ 2^(p.trees*p.height+j) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hpow)]
    rfl

theorem accepted_eq_range (p : Config) : p.scheme.accepted = List.range p.messageCount := by
  have hb : p.messageCount ≤ 2^p.rawBits := by
    apply Nat.pow_le_pow_right (by decide)
    unfold rawBits
    omega
  change (List.range (2^p.rawBits)).filter p.scheme.accept = _
  have hsplit : 2^p.rawBits = p.messageCount+(2^p.rawBits-p.messageCount) := by omega
  conv_lhs => rw [hsplit, List.range_add]
  rw [List.filter_append]
  have hl : (List.range p.messageCount).filter p.scheme.accept = List.range p.messageCount := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hx' := List.mem_range.mp hx
    exact (p.accept_iff_lt x (hx'.trans_le hb)).2 hx'
  have hr : (((List.range (2^p.rawBits-p.messageCount)).map (p.messageCount+·)).filter
      p.scheme.accept) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    have hj' := List.mem_range.mp hj
    intro hf
    have := (p.accept_iff_lt _ (by omega)).1 hf
    omega
  rw [hl,hr,List.append_nil]

theorem tau_eq (p : Config) : p.scheme.tau = 1/(2:ℚ)^p.zeroBits := by
  change ((p.scheme.accepted.length:Nat):ℚ)/((2^p.rawBits:Nat):ℚ) = _
  rw [p.accepted_eq_range,List.length_range]
  simp only [messageCount, rawBits, Nat.pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

end PoissonDAG.FORS.Config
