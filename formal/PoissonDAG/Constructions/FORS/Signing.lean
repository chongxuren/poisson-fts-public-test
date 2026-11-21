import PoissonDAG.Constructions.FORS.AcceptedRange
import PoissonDAG.Constructions.GRSCC.Reliability
import PoissonDAG.Probability.Counting

namespace PoissonDAG.FORS.Config

/-- With success probability 1/N a block of N independent trials fails
with probability at most one half. The 128 blocks include counter exhaustion. -/
private theorem blocks (n : Nat) (hn : 0 < n) :
    (1-1/(n:ℚ))^(n*128) ≤ (1:ℚ)/2^128 := by
  have hp : (0:ℚ) < n := by exact_mod_cast hn
  have hu : (1:ℚ) / n ≤ 1 := by
    apply (div_le_one hp).2
    exact_mod_cast hn
  have h := GRSCC.failure_times_linear_le_one (1/(n:ℚ)) (by positivity) hu n
  rw [show (n:ℚ) * (1/n) = 1 by field_simp] at h
  have hh : (1-1/(n:ℚ))^n ≤ 1/2 := by linarith
  rw [pow_mul, show (1:ℚ)/2^128 = ((1:ℚ)/2)^128 by rw [div_pow, one_pow]]
  exact pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr hu) _) hh _

theorem signing_upper (p : Config) : p.scheme.signCost ≤
    p.vertexCount + (((p.rawBits+127)/128 : Nat) : ℚ) * 2^p.zeroBits := by
  have ht : 0 < p.scheme.tau := by rw [tau_eq]; positivity
  have h := GRSCC.expectedTrials_le_inverse p.scheme ht (tau_le_one _)
  rw [p.tau_eq, one_div_one_div] at h
  change (p.graph.length : ℚ) + (((p.rawBits+127)/128 : Nat) : ℚ) * _ ≤ _
  rw [p.graph_length]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h (by positivity))

theorem counter_failure (p : Config) (hc : p.counterBits = p.zeroBits+7) :
    p.scheme.failure ≤ (1:ℚ)/2^128 := by
  change (1-p.scheme.tau)^(2^p.counterBits : Nat) ≤ _
  rw [p.tau_eq, hc, Nat.pow_add]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using blocks (2^p.zeroBits) (by positivity)

theorem ordinary_sign_and_failure :
    (scheme ⟨18,8,0,0⟩).signCost ≤ 6291457 ∧
    (scheme ⟨18,8,0,0⟩).failure = 0 := by
  constructor
  · exact (signing_upper _).trans (by decide +kernel)
  · change (1-(scheme ⟨18,8,0,0⟩).tau)^(1:Nat) = (0:ℚ)
    rw [tau_eq]
    decide +kernel

theorem equal_width_sign_and_failure :
    (scheme ⟨18,7,18,25⟩).signCost ≤ 6029311 ∧
    (scheme ⟨18,7,18,25⟩).failure ≤ (1:ℚ)/2^128 :=
  ⟨(signing_upper _).trans (by decide +kernel), counter_failure _ rfl⟩

theorem variable_width_sign_and_failure :
    (scheme ⟨17,7,19,26⟩).signCost ≤ 3801087 ∧
    (scheme ⟨17,7,19,26⟩).failure ≤ (1:ℚ)/2^128 :=
  ⟨(signing_upper _).trans (by decide +kernel), counter_failure _ rfl⟩

end PoissonDAG.FORS.Config
