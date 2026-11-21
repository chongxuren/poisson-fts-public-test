import PoissonDAG.Constructions.PORS.Literal
import PoissonDAG.Constructions.GRSCC.Costs
import PoissonDAG.Probability.Counting

namespace PoissonDAG.PORS.Literal

theorem leftShape_card (h extra : Nat) (bound : extra ≤ 2^h) :
    (leftShape h extra).leaves = 2^h+extra := by
  induction h generalizing extra with
  | zero =>
    have hb : extra ≤ 1 := by simpa using bound
    by_cases he : extra=0
    · simp [leftShape,Shape.leaves,he]
    · have : extra=1 := by omega
      simp [leftShape,Shape.leaves,this]
  | succ h ih =>
    simp only [leftShape,Shape.leaves]
    rw [ih _ (Nat.min_le_left _ _), ih _ (by rw [pow_succ] at bound; omega)]
    rw [pow_succ]
    omega

theorem shape_card (n : Nat) (hp : 0<n) : (shape n).leaves=n := by
  have hn : n ≠ 0 := by omega
  have hlo := Nat.log2_self_le hn
  have hhi : n < 2^(n.log2+1) := (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
  rw [pow_succ] at hhi
  unfold shape
  rw [leftShape_card _ _ (by omega)]
  omega

theorem actual_graph_length (p : Row) (hk : 0<p.K) (ht : 0<p.t) :
    (scheme p).graph.length = p.graphNodes := by
  have hb : 0 < p.buckets := by simp [Row.buckets]
  have hh := graph_length (shape p.K) (shape p.buckets) (shape p.t) p.cap
  rw [shape_card _ hk,shape_card _ hb,shape_card _ ht] at hh
  change (graph (shape p.K) (shape p.buckets) (shape p.t) p.cap).length = _
  unfold Row.graphNodes
  simpa only [← Nat.mul_assoc] using Nat.eq_sub_of_add_eq hh

theorem block_failure {τ : ℚ} (n : Nat) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (mass : 7 ≤ 16*(n : ℚ)*τ) :
    (1-τ)^(n*256) ≤ (1 : ℚ)/2^128 := by
  have hp : 0 ≤ (1-τ)^n := pow_nonneg (by linarith) _
  have hlin := GRSCC.failure_times_linear_le_one τ h0 h1 n
  have hf : (23 : ℚ)/16 ≤ 1+(n : ℚ)*τ := by linarith
  have hsmall : (1-τ)^n ≤ (16 : ℚ)/23 := by
    have hm := mul_le_mul_of_nonneg_left hf hp
    linarith
  rw [pow_mul]
  exact (pow_le_pow_left₀ hp hsmall 256).trans (by norm_num)

structure OutputFacts (p : Row) : Prop where
  count : (scheme p).accepted.length = p.acceptedWords
  work : ∀ raw ∈ (scheme p).accepted, (scheme p).verifyCalls raw ≤ p.verifyCeiling
  labels : ∀ raw ∈ (scheme p).accepted,
    weight ((scheme p).frontier raw) ≤ p.K*(p.k+p.b)+p.M

def RowTau (p : Row) : ℚ := (p.acceptedWords : ℚ) / 2^p.r

theorem actual_costs (p : Row) (hk : 0<p.K) (ht : 0<p.t) (ha : 0<p.acceptedWords)
    (hn : 2^p.ctr = 2^(p.ctr-8)*256)
    (hm : 7 ≤ 16*((2^(p.ctr-8) : Nat) : ℚ)*RowTau p)
    (hs : (p.graphNodes : ℚ)+(p.digestCalls : ℚ)/RowTau p ≤ 2^24)
    (hv : p.verifyCeiling ≤ 441) (facts : OutputFacts p) :
    (scheme p).failure ≤ (1 : ℚ)/2^128 ∧ (scheme p).signCost ≤ 2^24 ∧
    (scheme p).verifyCost ≤ 512 ∧ (scheme p).size ≤ p.bytes := by
  let s := scheme p
  have hlen : s.accepted.length = p.acceptedWords := facts.count
  have hτ : s.tau = RowTau p := by
    change (s.accepted.length : ℚ) / ((2^p.r : Nat) : ℚ) = _
    rw [hlen]
    simp [RowTau]
  have hτpos : 0<s.tau := by rw [hτ]; unfold RowTau; positivity
  have hτone := tau_le_one s
  have hf : s.failure ≤ (1 : ℚ)/2^128 := by
    change (1-s.tau)^(2^p.ctr) ≤ _
    rw [hn]
    apply block_failure _ hτpos.le hτone
    rwa [hτ]
  refine ⟨hf,?_,?_,?_⟩
  · change (s.graph.length : ℚ)+ (p.digestCalls : ℚ)*s.expectedTrials ≤ _
    rw [actual_graph_length p hk ht]
    apply GRSCC.affine_inverse_bound _ _ _ _ _ (Nat.cast_nonneg _)
      (GRSCC.expectedTrials_le_inverse s hτpos hτone)
    rwa [hτ]
  · apply GRSCC.verification_budget_of_refinement s (by simpa only [hlen] using ha) (failure_nonneg s)
      (hf.trans (by norm_num))
    exact fun raw h => (facts.work raw h).trans hv
  · change (p.ctr+7)/8+16*((s.accepted.map (fun raw => weight (s.frontier raw))).foldl max 0) ≤
      (p.ctr+7)/8+16*(p.K*(p.k+p.b)+p.M)
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply GRSCC.foldMax_le _ _ _ (by omega)
    intro w hw
    obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp hw
    exact facts.labels raw hr

theorem single_resources (facts : OutputFacts SingleRefined.p) :
    single.failure ≤ (1 : ℚ)/2^128 ∧ single.signCost ≤ 2^24 ∧
    single.verifyCost ≤ 512 ∧ single.size ≤ 1780 := by
  apply actual_costs SingleRefined.p <;> first | exact facts | decide +kernel

theorem bucket_resources (facts : OutputFacts BucketRefined.p) :
    bucket.failure ≤ (1 : ℚ)/2^128 ∧ bucket.signCost ≤ 2^24 ∧
    bucket.verifyCost ≤ 512 ∧ bucket.size ≤ 1492 := by
  apply actual_costs BucketRefined.p <;> first | exact facts | decide +kernel

theorem chain_resources (facts : OutputFacts ChainRefined.p) :
    chainBuckets.failure ≤ (1 : ℚ)/2^128 ∧ chainBuckets.signCost ≤ 2^24 ∧
    chainBuckets.verifyCost ≤ 512 ∧ chainBuckets.size ≤ 1188 := by
  apply actual_costs ChainRefined.p <;> first | exact facts | decide +kernel

end PoissonDAG.PORS.Literal
