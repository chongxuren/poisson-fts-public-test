import PoissonDAG.Constructions.GRSCC.Codebook

/-! Canonical mixed-radix decoding, exact raw counting, and protected-circuit refinement. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

def routeDigit (rank : Nat) (layer : Layer) : Fin coordinateRadix :=
  ⟨rank / coordinateRadix ^ layer.val % coordinateRadix,
    Nat.mod_lt _ (by rw [coordinateRadix, codeCardinality_eq]; decide)⟩

def decodedSlot (digit : Fin coordinateRadix) : Slot :=
  ⟨digit.val / codeCardinality, by
    have hdigit : digit.val < 499104 := digit.isLt
    change digit.val / 15597 < 32
    omega⟩

def decodedCodeRank (digit : Fin coordinateRadix) : Fin codeCardinality :=
  ⟨digit.val % codeCardinality,
    Nat.mod_lt _ (by rw [codeCardinality_eq]; decide)⟩

/-- Mixed-radix unranking, with layer zero as the least significant digit. -/
def decodedRoute (rank : Fin encodingCardinality) : Route where
  bucket := ⟨rank.val / (2 * coordinateRadix ^ 7), by
    apply Nat.div_lt_of_lt_mul
    have h := rank.isLt
    change rank.val < 32 * coordinateRadix ^ 7 at h
    omega⟩
  initialOwner := ⟨rank.val / coordinateRadix ^ 7 % 2, Nat.mod_lt _ (by decide)⟩
  slot := fun layer => decodedSlot (routeDigit rank.val layer)
  code := fun layer => decodedCodeword (decodedCodeRank (routeDigit rank.val layer))

def rawThreshold (raw : Nat) : Nat := raw % 2 ^ 32
def rawRank (raw : Nat) : Nat := raw / 2 ^ 32
def rawAccept (raw : Nat) : Bool :=
  decide (rawThreshold raw < threshold ∧ rawRank raw < encodingCardinality)

def acceptedRawSetFor (space gate ranks : Nat) : Finset Nat :=
  (Finset.range space).filter (fun raw => rawThreshold raw < gate ∧ rawRank raw < ranks)

theorem mem_acceptedRawSetFor (space gate ranks raw : Nat) :
    raw ∈ acceptedRawSetFor space gate ranks ↔
      raw < space ∧ rawThreshold raw < gate ∧ rawRank raw < ranks := by
  simp only [acceptedRawSetFor, Finset.mem_filter, Finset.mem_range]

@[irreducible] def acceptedRawSet : Finset Nat :=
  acceptedRawSetFor (2 ^ rawBits) threshold encodingCardinality

theorem acceptedRawSet_eq :
    acceptedRawSet = acceptedRawSetFor (2 ^ rawBits) threshold encodingCardinality := by
  unfold acceptedRawSet
  rfl

theorem mem_acceptedRawSet (raw : Nat) : raw ∈ acceptedRawSet ↔
    raw < 2 ^ rawBits ∧ rawThreshold raw < threshold ∧ rawRank raw < encodingCardinality := by
  calc
    raw ∈ acceptedRawSet ↔ raw ∈ acceptedRawSetFor (2 ^ rawBits) threshold encodingCardinality := by
      rw [acceptedRawSet_eq]
    _ ↔ _ := mem_acceptedRawSetFor _ _ _ _

def acceptedRawPairsFor (gate ranks : Nat) : Finset (Nat × Nat) :=
  (Finset.range gate) ×ˢ (Finset.range ranks)

theorem mem_acceptedRawPairsFor (gate ranks : Nat) (pair : Nat × Nat) :
    pair ∈ acceptedRawPairsFor gate ranks ↔ pair.1 < gate ∧ pair.2 < ranks := by
  simp only [acceptedRawPairsFor, Finset.mem_product, Finset.mem_range]

theorem acceptedRawPairsFor_card (gate ranks : Nat) :
    (acceptedRawPairsFor gate ranks).card = gate * ranks := by
  simp only [acceptedRawPairsFor, Finset.card_product, Finset.card_range]

@[irreducible] def acceptedRawPairs : Finset (Nat × Nat) :=
  acceptedRawPairsFor threshold encodingCardinality

theorem acceptedRawPairs_eq : acceptedRawPairs = acceptedRawPairsFor threshold encodingCardinality := by
  unfold acceptedRawPairs
  rfl

theorem mem_acceptedRawPairs (pair : Nat × Nat) : pair ∈ acceptedRawPairs ↔
    pair.1 < threshold ∧ pair.2 < encodingCardinality := by
  calc
    pair ∈ acceptedRawPairs ↔ pair ∈ acceptedRawPairsFor threshold encodingCardinality := by
      rw [acceptedRawPairs_eq]
    _ ↔ _ := mem_acceptedRawPairsFor _ _ _

theorem acceptedRawPairs_card : acceptedRawPairs.card = threshold * encodingCardinality := by
  exact (congrArg Finset.card acceptedRawPairs_eq).trans (acceptedRawPairsFor_card _ _)

theorem raw_fields_of_pair (y z : Nat) (hy : y < threshold) :
    rawThreshold (y + 2 ^ 32 * z) = y ∧
      rawRank (y + 2 ^ 32 * z) = z := by
  have hy' : y < 2 ^ 32 := by
    norm_num [threshold] at hy ⊢
    omega
  unfold rawThreshold rawRank
  constructor <;> omega

theorem raw_pair_bound (y z : Nat) (hy : y < threshold)
    (hz : z < encodingCardinality) : y + 2 ^ 32 * z < 2 ^ rawBits := by
  have hU : encodingCardinality ≤ 2 ^ rankBits := fixed_encoder.2.2.2
  have hy' : y < 2 ^ 32 := by
    norm_num [threshold] at hy ⊢
    omega
  have hz' : z < 2 ^ rankBits := lt_of_lt_of_le hz hU
  norm_num [rankBits, rawBits, thresholdBits] at hz' ⊢
  omega

theorem acceptedRawSet_card :
    acceptedRawSet.card = threshold * encodingCardinality := by
  have hcard : acceptedRawSet.card = acceptedRawPairs.card := by
    apply Finset.card_bij (s := acceptedRawSet) (t := acceptedRawPairs)
      (fun raw _ => (rawThreshold raw, rawRank raw))
    · intro raw hraw
      obtain ⟨_, hy, hz⟩ := (mem_acceptedRawSet raw).mp hraw
      exact (mem_acceptedRawPairs _).mpr ⟨hy, hz⟩
    · intro a ha b hb hab
      have hy : rawThreshold a = rawThreshold b := congrArg Prod.fst hab
      have hz : rawRank a = rawRank b := congrArg Prod.snd hab
      have ha' := Nat.mod_add_div a (2 ^ 32)
      have hb' := Nat.mod_add_div b (2 ^ 32)
      change rawThreshold a + 2 ^ 32 * rawRank a = a at ha'
      change rawThreshold b + 2 ^ 32 * rawRank b = b at hb'
      omega
    · intro pair hpair
      obtain ⟨hy', hz'⟩ := (mem_acceptedRawPairs pair).mp hpair
      refine ⟨pair.1 + 2 ^ 32 * pair.2, ?_, ?_⟩
      · apply (mem_acceptedRawSet _).mpr
        exact ⟨raw_pair_bound _ _ hy' hz',
          by rw [(raw_fields_of_pair _ _ hy').1]; exact hy',
          by rw [(raw_fields_of_pair _ _ hy').2]; exact hz'⟩
      · exact Prod.ext (raw_fields_of_pair _ _ hy').1
          (raw_fields_of_pair _ _ hy').2
  simpa only [acceptedRawPairs_card] using hcard

end PoissonDAG.GRSCC
