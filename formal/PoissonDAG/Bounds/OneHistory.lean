import PoissonDAG.Bounds.GraphChains
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Aesop

/-!
# An exact finite one-history lower bound

Only the coefficient with one accepted history is needed here. The target is
still sampled from all raw encodings, so acceptance occurs exactly once. No
Poisson truncation, real exponential, or approximation enters this argument.
-/

namespace PoissonDAG

/-- A finite family partitioned into at most `keys.card` classes, each total for
the covering relation, has at least `family.card² / (2 * keys.card)` covered
ordered pairs. Reflexive pairs and ties only increase the count. -/
theorem finite_chain_pairs_lower {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (family : Finset α) (keys : Finset κ) (key : α → κ)
    (covers : α → α → Prop) [DecidableRel covers]
    (hkey : ∀ x ∈ family, key x ∈ keys)
    (htotal : ∀ x ∈ family, ∀ y ∈ family, key x = key y → covers x y ∨ covers y x) :
    family.card ^ 2 ≤ 2 * keys.card *
      ((family ×ˢ family).filter (fun p => covers p.1 p.2)).card := by
  let fiber := fun k => family.filter (fun x => key x = k)
  let same := (family ×ˢ family).filter (fun p => key p.1 = key p.2)
  let good := (family ×ˢ family).filter (fun p => covers p.1 p.2)
  have hsum : family.card = ∑ k ∈ keys, (fiber k).card :=
    Finset.card_eq_sum_card_fiberwise hkey
  have hsame : same.card = ∑ k ∈ keys, (fiber k).card ^ 2 := by
    have hm : (same : Set (α × α)).MapsTo (fun p => key p.1) keys := by
      intro p hp
      exact hkey p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    rw [Finset.card_eq_sum_card_fiberwise hm]
    apply Finset.sum_congr rfl
    intro k hk
    have hf : same.filter (fun p => key p.1 = k) = (fiber k) ×ˢ (fiber k) := by
      ext p
      rcases p with ⟨x, y⟩
      simp only [same, fiber, Finset.mem_filter, Finset.mem_product]
      aesop
    rw [hf, Finset.card_product, pow_two]
  have hcs : family.card ^ 2 ≤ keys.card * same.card := by
    calc
      family.card ^ 2 = (∑ k ∈ keys, (fiber k).card) ^ 2 := by rw [hsum]
      _ ≤ keys.card * ∑ k ∈ keys, (fiber k).card ^ 2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := Nat) keys
          (fun _ => 1) (fun k => (fiber k).card)
      _ = keys.card * same.card := by rw [← hsame]
  have hsub : same ⊆ good ∪ good.image Prod.swap := by
    intro p hp
    rcases p with ⟨x, y⟩
    rcases Finset.mem_filter.mp hp with ⟨hxy, heq⟩
    rcases Finset.mem_product.mp hxy with ⟨hx, hy⟩
    rcases htotal x hx y hy heq with hc | hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hxy, hc⟩))
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨(y, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, hc⟩, rfl⟩
  have hswap : (good.image Prod.swap).card = good.card :=
    Finset.card_image_of_injective _ (by
      intro a b hab
      simpa using congrArg Prod.swap hab)
  have htwo : same.card ≤ 2 * good.card := by
    calc
      same.card ≤ (good ∪ good.image Prod.swap).card := Finset.card_le_card hsub
      _ ≤ good.card + (good.image Prod.swap).card := Finset.card_union_le _ _
      _ = 2 * good.card := by rw [hswap]; omega
  exact hcs.trans (by
    simpa [good, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left keys.card htwo)

theorem Scheme.same_chain_covered (s : Scheme) (hs : s.WellFormed) (hc : s.Correct)
    {x y : Nat} (hx : x ∈ s.accepted) (hy : y ∈ s.accepted)
    (hkey : s.chainKey x = s.chainKey y) :
    s.covered [x] y = true ∨ s.covered [y] x = true := by
  rcases s.same_chain_comparable hs hc hx hy hkey with hxy | hyx
  · exact Or.inr (s.covered_singleton_of_derives hs hx hxy)
  · exact Or.inl (s.covered_singleton_of_derives hs hy hyx)

theorem Scheme.raws_nodup (s : Scheme) : s.raws.Nodup := List.nodup_range

theorem Scheme.accepted_nodup (s : Scheme) : s.accepted.Nodup :=
  s.raws_nodup.filter _

theorem Scheme.accepted_mem_raws (s : Scheme) {x : Nat} (hx : x ∈ s.accepted) :
    x ∈ s.raws := (List.mem_filter.mp hx).1

/-- The exact finite numerator in the protected `q = 1` coefficient. -/
def Scheme.oneHistoryPairs (s : Scheme) : Nat :=
  ((s.accepted ×ˢ s.raws).filter (fun p => s.covered [p.1] p.2)).length

theorem Scheme.oneHistoryPairs_eq_count (s : Scheme) :
    s.oneHistoryPairs =
      ((s.accepted.flatMap (fun h => s.raws.map (fun t => s.covered [h] t))).count true) := by
  simp [Scheme.oneHistoryPairs, SProd.sprod, List.product, List.count_eq_countP,
    ← List.countP_eq_length_filter, List.countP_flatMap, List.countP_map, Function.comp_def]

theorem Scheme.oneHistoryPairs_eq_card (s : Scheme) :
    s.oneHistoryPairs =
      ((s.accepted.toFinset ×ˢ s.raws.toFinset).filter
        (fun p => s.covered [p.1] p.2 = true)).card := by
  have hn := (s.accepted_nodup.product s.raws_nodup).filter
    (fun p => s.covered [p.1] p.2)
  have heq : ((s.accepted ×ˢ s.raws).filter
      (fun p => s.covered [p.1] p.2)).toFinset =
      ((s.accepted.toFinset ×ˢ s.raws.toFinset).filter
        (fun p => s.covered [p.1] p.2 = true)) := by
    ext p
    rcases p with ⟨h, t⟩
    simp
  calc
    s.oneHistoryPairs = ((s.accepted ×ˢ s.raws).filter
        (fun p => s.covered [p.1] p.2)).toFinset.card :=
      (List.toFinset_card_of_nodup hn).symm
    _ = _ := congrArg Finset.card heq

/-- The exact ordered-pair inequality, before division by the common raw and
accepted sample-space sizes. -/
theorem Scheme.oneHistoryPairs_lower (s : Scheme) (hs : s.WellFormed) (hc : s.Correct) :
    s.accepted.length ^ 2 ≤
      2 * chainCount s.graph.length s.maxWords * s.oneHistoryPairs := by
  have hfinite := finite_chain_pairs_lower s.accepted.toFinset
    (chainUniverse s.graph.length s.maxWords) s.chainKey
    (fun h t => s.covered [h] t = true)
    (by intro x hx; exact s.chainKey_mem hs hc (List.mem_toFinset.mp hx))
    (by
      intro x hx y hy heq
      exact s.same_chain_covered hs hc (List.mem_toFinset.mp hx)
        (List.mem_toFinset.mp hy) heq)
  have hsub :
      ((s.accepted.toFinset ×ˢ s.accepted.toFinset).filter
        (fun p => s.covered [p.1] p.2 = true)) ⊆
      ((s.accepted.toFinset ×ˢ s.raws.toFinset).filter
        (fun p => s.covered [p.1] p.2 = true)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hm, hc⟩
    rcases Finset.mem_product.mp hm with ⟨hh, ht⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hh, List.mem_toFinset.mpr
        (s.accepted_mem_raws (List.mem_toFinset.mp ht))⟩, hc⟩
  rw [List.toFinset_card_of_nodup s.accepted_nodup, chainUniverse_card] at hfinite
  exact hfinite.trans (Nat.mul_le_mul_left _ (by
    rw [s.oneHistoryPairs_eq_card]
    exact Finset.card_le_card hsub))

theorem Scheme.coverCoefficient_one_eq (s : Scheme) :
    s.coverCoefficient 1 = (s.oneHistoryPairs : Rat) /
      ((s.accepted.length * 2 ^ s.encoder.inputs : Nat) : Rat) := by
  have hh : histories s.accepted 1 = s.accepted.map (fun h => [h]) := by
    simp [histories]
  rw [Scheme.coverCoefficient, hh, List.flatMap_map, ← s.oneHistoryPairs_eq_count]
  simp

/-- A one-history covering lower bound in the exact original scheme model. -/
theorem Scheme.oneHistory_lower (s : Scheme) (hs : s.WellFormed) (hc : s.Correct) :
    s.tau / (2 * (chainCount s.graph.length s.maxWords : Rat)) ≤ s.coverCoefficient 1 := by
  have hm : 0 < s.accepted.length := hs.2.2.2.2.2
  have hr : 0 < 2 ^ s.encoder.inputs := by positivity
  have hd : 0 < chainCount s.graph.length s.maxWords :=
    chainCount_pos (s.maxWords_pos hs hc)
  have hnat := s.oneHistoryPairs_lower hs hc
  have hrat : (s.accepted.length : Rat) ^ 2 ≤
      2 * (chainCount s.graph.length s.maxWords : Rat) * s.oneHistoryPairs := by
    exact_mod_cast hnat
  rw [s.coverCoefficient_one_eq, Scheme.tau]
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hcancel : ((s.accepted.length : Rat) / (2 ^ s.encoder.inputs : Rat)) *
      ((s.accepted.length : Rat) * (2 ^ s.encoder.inputs : Rat)) =
      (s.accepted.length : Rat) ^ 2 := by
    field_simp
  rw [hcancel]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hrat

end PoissonDAG
