import PoissonDAG.Constructions.GRSCC.TwoHistoryCounts
import PoissonDAG.Constructions.GRSCC.MaskedCounts
import PoissonDAG.Probability.PackedCounts
import Mathlib.Tactic.FinCases

/-! With two same-slot histories, encode the depths of both histories and
the target at one position as a single degree. The coefficient of the sixth
power enforces all three sums. The proof maps the public counting event into
that coefficient, preserving the order of the two histories. -/
namespace PoissonDAG.GRSCC.TwoSame

set_option maxRecDepth 8000
attribute [local irreducible] decodedCodeword localCoveredSet localConditionalCount

private abbrev Atom := Fin 9 × Fin 9 × Fin 9
private abbrev B : Nat := 2^64
private def degree (a : Atom) := a.1.val+49*a.2.1.val+49^2*a.2.2.val
private def index : Nat := 16+49*16+49^2*16
private def alphabet := Finset.univ.filter (fun a : Atom => a.2.2 ≤ max a.1 a.2.1)
private def strings := Fintype.piFinset (fun _ : CodePosition => alphabet)
private def total (x : CodePosition → Atom) := ∑ j, degree (x j)
private def words := strings.filter (fun x => total x = index)
private def basis := ∑ a ∈ alphabet, B^degree a

private theorem card_words : words.card = ((basis^6)/B^index)%B := by
  classical
  have bound : strings.card < B := by
    have h : alphabet.card ≤ 729 := (Finset.card_filter_le _ _).trans (by decide +kernel)
    have he : strings.card = alphabet.card ^ 6 := by simp [strings,Fintype.card_piFinset]
    rw [he]
    exact (Nat.pow_le_pow_left h 6).trans_lt (by decide +kernel)
  have he : basis^6 = ∑ x ∈ strings, B^total x := by
    calc
      basis^6 = ∏ _ : CodePosition, ∑ a ∈ alphabet, B^degree a := by simp [basis]
      _ = _ := by
        rw [Finset.prod_univ_sum]
        exact Finset.sum_congr rfl (fun x _ => Finset.prod_pow_eq_pow_sum _ _ _)
  rw [he, PackedCounts.digit_sum _ _ _ _ bound]
  rfl

private abbrev Samples (r : Fin codeCardinality) :=
  ↥(localCoveredSet 2 0 (sameSlotSupply (decodedCodeword r))
    (differentSlotSupply (0 : Slot) (decodedCodeword r)))

private def encode (x : Σ r, Samples r) (j : CodePosition) : Atom :=
  ((decodedCodeword (x.2.val.1 0)).depth j, (decodedCodeword (x.2.val.1 1)).depth j,
    (decodedCodeword x.1).depth j)

private theorem encode_mem (x : Σ r, Samples r) : encode x ∈ words := by
  unfold words
  apply Finset.mem_filter.mpr
  constructor
  · unfold strings
    apply Fintype.mem_piFinset.mpr
    intro j
    unfold alphabet
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases (localCoveredSet_mem _ _ _ _ _).mp x.2.property j with ⟨i,hi⟩ | ⟨i,_⟩
    · have hh := of_decide_eq_true hi
      fin_cases i
      · exact le_max_of_le_left hh
      · exact le_max_of_le_right hh
    · exact Fin.elim0 i
  · simp only [total,encode,degree,Finset.sum_add_distrib,← Finset.mul_sum,Codeword.sum_eq]
    rfl

private theorem encode_inj : Function.Injective encode := by
  rintro ⟨r, ⟨⟨xs,ys⟩, hx⟩⟩ ⟨s, ⟨⟨us,vs⟩, hu⟩⟩ he
  have hr : r = s := decodedCodeword_injective (Codeword.ext (fun j =>
    congrArg (fun f => (f j).2.2) he))
  subst s
  have hs : xs = us := by
    funext i
    fin_cases i
    · exact decodedCodeword_injective (Codeword.ext (fun j => congrArg (fun f => (f j).1) he))
    · exact decodedCodeword_injective (Codeword.ext (fun j => congrArg (fun f => (f j).2.1) he))
  have hd : ys = vs := funext (fun i => Fin.elim0 i)
  subst us
  subst vs
  rfl

private theorem event_le : localConditionalCount 0 2 2 ≤ words.card := by
  classical
  let f : (Σ r, Samples r) → ↥words := fun x => ⟨encode x,encode_mem x⟩
  have hb := Fintype.card_le_of_injective f (fun _ _ h => encode_inj (congrArg Subtype.val h))
  simpa only [Fintype.card_sigma, Fintype.card_coe, localConditionalCount,
    localSuccessNumerator, show 2-2=0 from rfl] using hb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem digit_value : ((basis^6)/B^index)%B = 135928911021 := by decide +kernel

theorem local_two_same : localCover 2 2 ≤ (35826 : Rat)/1000000 := by
  rw [localCover_event_count (0 : Slot) 2 2 (by decide) (by decide)]
  have hv := event_le
  rw [card_words, digit_value] at hv
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hv) (by positivity)).trans (by decide +kernel)

#print axioms local_two_same
end PoissonDAG.GRSCC.TwoSame
