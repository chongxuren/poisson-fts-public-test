import PoissonDAG.Constructions.FORS.HistoryCount
import PoissonDAG.Constructions.FORS.Poisson

namespace PoissonDAG.FORS.Config

private theorem history_average_le (p : Config) (q : Nat) (cap : ℚ)
    (hcap : ∀ h : List Nat, h.length = q →
      (∑ x : Fin p.messageCount, if p.scheme.covered h x then (1:ℚ) else 0) ≤ cap) :
    p.scheme.acceptedCoverProbability q ≤ cap/(p.messageCount:ℚ) := by
  have hlen : p.scheme.accepted.length = p.messageCount := by simp [p.accepted_eq_range]
  have hposN : 0 < p.messageCount := by unfold messageCount; positivity
  have hp : (0:ℚ) < p.messageCount := by exact_mod_cast hposN
  unfold Scheme.acceptedCoverProbability
  apply le_trans (div_le_div_of_nonneg_right (b := ∑ _h : Fin q → Fin p.scheme.accepted.length, cap)
    (Finset.sum_le_sum ?_) (by positivity)) _
  · intro sample _
    let h := indexHistory p.scheme.accepted sample
    have hsize : h.length = q := by simp [h,indexHistory]
    have := hcap h hsize
    change (∑ target : Fin p.scheme.accepted.length,
      if p.scheme.covered h p.scheme.accepted[target] then (1:ℚ) else 0) ≤ cap
    apply le_trans (le_of_eq (Fintype.sum_equiv (finCongr hlen)
      (fun t : Fin p.scheme.accepted.length => if p.scheme.covered h p.scheme.accepted[t] then (1:ℚ) else 0)
      (fun t : Fin p.messageCount => if p.scheme.covered h t then (1:ℚ) else 0) ?_)) this
    intro t
    have ht : p.scheme.accepted[t] = t.val := by simp [p.accepted_eq_range]
    rw [ht] <;> rfl
  · apply le_of_eq
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,hlen,nsmul_eq_mul,Nat.cast_pow,pow_succ]
    field_simp [hp.ne'] <;> ring

theorem protected_envelope (p : Config) (q : Nat) :
    p.scheme.coverCoefficient q ≤ momentEnvelope p.height p.trees p.zeroBits q := by
  have hpos : 0 < p.scheme.accepted.length := by
    simp [p.accepted_eq_range,messageCount]
  rw [p.scheme.coverCoefficient_eq_acceptedProbability hpos, p.tau_eq]
  have havg := p.history_average_le q ((q:ℚ)^p.trees)
    (fun h hh => by simpa only [hh] using p.fixed_history_sum h)
  apply le_trans (mul_le_mul_of_nonneg_left havg (by positivity)) _
  unfold momentEnvelope messageCount
  push_cast
  rw [Nat.mul_comm p.trees p.height, pow_mul]
  rw [mul_pow, div_pow]
  field_simp <;> ring_nf <;> exact le_rfl

theorem protected_le_one (p : Config) (q : Nat) : p.scheme.coverCoefficient q ≤ 1 := by
  have hm : (0:ℚ) < p.messageCount := by
    have : 0 < p.messageCount := by unfold messageCount; positivity
    exact_mod_cast this
  have hpos : 0 < p.scheme.accepted.length := by simp [p.accepted_eq_range,messageCount]
  rw [p.scheme.coverCoefficient_eq_acceptedProbability hpos]
  have hb := p.history_average_le q (p.messageCount:ℚ) (by
    intro history _
    calc
      _ ≤ ∑ _ : Fin p.messageCount, (1:ℚ) := Finset.sum_le_sum (by intro t _; split <;> norm_num)
      _ = _ := by simp)
  rw [div_self hm.ne'] at hb
  exact (mul_le_mul_of_nonneg_left hb (tau_nonneg _)).trans (by simpa using tau_le_one p.scheme)

theorem protected_poisson (p : Config)
    (hfinite : weightedCut (momentEnvelope p.height p.trees p.zeroBits) 1 40 +
      ((1:ℚ)^40 / factorial 40) / (1 - 1/(40+1:ℚ)) ≤
      ((1:ℚ)/2^128) * exponentialCut 1 4) :
    PoissonLE p.scheme.coverCoefficient ((1:ℚ)/2^128) := by
  apply PORS.poissonLE_of_forty_terms (coverCoefficient_nonneg _) p.protected_le_one (by positivity)
  apply le_trans _ hfinite
  apply add_le_add _ le_rfl
  unfold weightedCut
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_right (p.protected_envelope q) (by positivity)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem ordinary_literal_poisson : PoissonLE (scheme ⟨18,8,0,0⟩).coverCoefficient ((1:ℚ)/2^128) := by
  apply protected_poisson
  simp only [weightedCut,exponentialCut]
  decide +kernel

theorem equal_width_literal_poisson : PoissonLE (scheme ⟨18,7,18,25⟩).coverCoefficient ((1:ℚ)/2^128) := by
  apply protected_poisson
  simp only [weightedCut,exponentialCut]
  decide +kernel

theorem variable_width_literal_poisson : PoissonLE (scheme ⟨17,7,19,26⟩).coverCoefficient ((1:ℚ)/2^128) := by
  apply protected_poisson
  simp only [weightedCut,exponentialCut]
  decide +kernel

end PoissonDAG.FORS.Config
