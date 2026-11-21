import PoissonDAG.Constructions.GRSCC.RankEncoding

/-! Exact finite product law of the *actual* rank decoder. The inverse
equivalences in this proof are mathematical indexing devices; the executable
encoder remains the canonical `decodedRoute` defined in RankEncoding. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

noncomputable def codeEquiv : Fin codeCardinality ≃ Codeword :=
  Equiv.ofBijective decodedCodeword
    ⟨decodedCodeword_injective, decodedCodeword_surjective⟩

noncomputable def digitEquiv : Fin coordinateRadix ≃ Slot × Codeword :=
  (finCongr (by rfl : coordinateRadix = 32 * codeCardinality)).trans
    ((finProdFinEquiv (m := 32) (n := codeCardinality)).symm.trans
      (Equiv.prodCongr (Equiv.refl Slot) codeEquiv))

def routePack : Route ≃ Bucket × Fin 2 × (Layer → Slot × Codeword) where
  toFun r := (r.bucket, r.initialOwner, fun layer => (r.slot layer, r.code layer))
  invFun r :=
    { bucket := r.1
      initialOwner := r.2.1
      slot := fun layer => (r.2.2 layer).1
      code := fun layer => (r.2.2 layer).2 }
  left_inv _ := rfl
  right_inv _ := rfl

def rankPieces : Fin encodingCardinality ≃ Bucket × Fin 2 × (Layer → Fin coordinateRadix) :=
  (finCongr (by
    change (16 * 2) * coordinateRadix ^ 7 = 16 * (2 * coordinateRadix ^ 7)
    exact Nat.mul_assoc _ _ _ :
      encodingCardinality = 16 * (2 * coordinateRadix ^ 7))).trans
    ((finProdFinEquiv (m := 16) (n := 2 * coordinateRadix ^ 7)).symm.trans
      (Equiv.prodCongr (Equiv.refl Bucket)
        ((finProdFinEquiv (m := 2) (n := coordinateRadix ^ 7)).symm.trans
          (Equiv.prodCongr (Equiv.refl (Fin 2))
            (finFunctionFinEquiv (m := coordinateRadix) (n := 7)).symm))))

noncomputable def routeEquiv : Fin encodingCardinality ≃ Route :=
  rankPieces.trans
    ((Equiv.prodCongr (Equiv.refl Bucket)
      (Equiv.prodCongr (Equiv.refl (Fin 2))
        (Equiv.piCongrRight fun _ : Layer => digitEquiv))).trans routePack.symm)

theorem digit_of_remainder (rank : Nat) (layer : Layer) :
    (rank % coordinateRadix ^ 7) / coordinateRadix ^ layer.val % coordinateRadix =
      rank / coordinateRadix ^ layer.val % coordinateRadix := by
  have hl := layer.isLt
  have hp : coordinateRadix ^ 7 =
      coordinateRadix ^ layer.val * coordinateRadix ^ (7 - layer.val) := by
    rw [← pow_add]
    congr 1
    omega
  have hd : coordinateRadix ∣ coordinateRadix ^ (7 - layer.val) := by
    refine ⟨coordinateRadix ^ (6 - layer.val), ?_⟩
    have he : 7 - layer.val = (6 - layer.val) + 1 := by omega
    rw [he, pow_succ']
  rw [hp, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ hd

theorem rankPieces_digit (rank : Fin encodingCardinality) (layer : Layer) :
    ((rankPieces rank).2.2 layer).val = (routeDigit rank.val layer).val := by
  change ((rank.val % (2 * coordinateRadix ^ 7)) % coordinateRadix ^ 7) /
      coordinateRadix ^ layer.val % coordinateRadix =
    rank.val / coordinateRadix ^ layer.val % coordinateRadix
  rw [Nat.mod_mul_left_mod]
  exact digit_of_remainder rank.val layer

@[ext] theorem Route.ext {left right : Route} (hb : left.bucket = right.bucket)
    (ho : left.initialOwner = right.initialOwner) (hs : left.slot = right.slot)
    (hc : left.code = right.code) : left = right := by
  cases left
  cases right
  cases hb
  cases ho
  cases hs
  cases hc
  rfl

theorem routeEquiv_apply (rank : Fin encodingCardinality) : routeEquiv rank = decodedRoute rank := by
  apply Route.ext
  · apply Fin.ext
    rfl
  · apply Fin.ext
    change rank.val % (2 * coordinateRadix ^ 7) / coordinateRadix ^ 7 =
      rank.val / coordinateRadix ^ 7 % 2
    exact Nat.mod_mul_left_div_self _ _ _
  · funext layer
    apply Fin.ext
    change ((rankPieces rank).2.2 layer).val / codeCardinality =
      (routeDigit rank.val layer).val / codeCardinality
    rw [rankPieces_digit]
  · funext layer
    change decodedCodeword _ = decodedCodeword _
    congr 1
    apply Fin.ext
    change ((rankPieces rank).2.2 layer).val % codeCardinality =
      (routeDigit rank.val layer).val % codeCardinality
    rw [rankPieces_digit]

theorem decodedRoute_bijective : Function.Bijective decodedRoute := by
  have hfun : decodedRoute = routeEquiv := funext (fun rank => (routeEquiv_apply rank).symm)
  rw [hfun]
  exact routeEquiv.bijective

noncomputable instance : Fintype Codeword := Fintype.ofEquiv (Fin codeCardinality) codeEquiv
noncomputable instance : Fintype Route := Fintype.ofEquiv (Fin encodingCardinality) routeEquiv

theorem codeword_card : Fintype.card Codeword = codeCardinality := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr codeEquiv).symm

theorem route_card : Fintype.card Route = encodingCardinality := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr routeEquiv).symm

theorem decodedRoute_sum {A : Type*} [AddCommMonoid A] (f : Route → A) :
    Finset.univ.sum (fun rank : Fin encodingCardinality => f (decodedRoute rank)) =
      Finset.univ.sum f := decodedRoute_bijective.sum_comp f

def decodeAccepted (raw : ↥acceptedRawSet) : Route :=
  decodedRoute ⟨rawRank raw.val, (mem_acceptedRawSet raw.val).mp raw.property |>.2.2⟩

def acceptedPairEquiv : ↥acceptedRawSet ≃ Fin threshold × Fin encodingCardinality where
  toFun raw :=
    let fields := (mem_acceptedRawSet raw.val).mp raw.property
    (⟨rawThreshold raw.val, fields.2.1⟩, ⟨rawRank raw.val, fields.2.2⟩)
  invFun pair := ⟨pair.1.val + 2 ^ 32 * pair.2.val, (mem_acceptedRawSet _).mpr
    ⟨raw_pair_bound _ _ pair.1.isLt pair.2.isLt,
      by rw [(raw_fields_of_pair _ _ pair.1.isLt).1]; exact pair.1.isLt,
      by rw [(raw_fields_of_pair _ _ pair.1.isLt).2]; exact pair.2.isLt⟩⟩
  left_inv raw := by
    apply Subtype.ext
    exact Nat.mod_add_div raw.val (2 ^ 32)
  right_inv pair := by
    apply Prod.ext
    · apply Fin.ext
      exact (raw_fields_of_pair _ _ pair.1.isLt).1
    · apply Fin.ext
      exact (raw_fields_of_pair _ _ pair.1.isLt).2

theorem acceptedPairEquiv_decode (raw : ↥acceptedRawSet) :
    decodedRoute (acceptedPairEquiv raw).2 = decodeAccepted raw := rfl

theorem accepted_raw_pushforward {A : Type*} [AddCommMonoid A] (f : Route → A) :
    Finset.univ.sum (fun raw : ↥acceptedRawSet => f (decodeAccepted raw)) =
      threshold • Finset.univ.sum f := by
  calc
    Finset.univ.sum (fun raw : ↥acceptedRawSet => f (decodeAccepted raw)) =
        Finset.univ.sum (fun pair : Fin threshold × Fin encodingCardinality =>
          f (decodedRoute pair.2)) :=
      Fintype.sum_equiv acceptedPairEquiv _ _ (fun raw => by rw [acceptedPairEquiv_decode])
    _ = threshold • Finset.univ.sum f := by
      simp only [Fintype.sum_prod_type, decodedRoute_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]

theorem accepted_raw_pushforward_rat (f : Route → ℚ) :
    Finset.univ.sum (fun raw : ↥acceptedRawSet => f (decodeAccepted raw)) =
      (threshold : ℚ) * Finset.univ.sum f := by
  simpa only [nsmul_eq_mul] using accepted_raw_pushforward f

end PoissonDAG.GRSCC
