import PoissonDAG.Constructions.GRSCC.Kernel
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Counting the actual joint layer transition

Every history retains its identity until the matching-index sets have been
counted. This connects the finite layer sample space to the joint recurrence;
no transition law or independent layer-cover probability is an input.
-/

namespace PoissonDAG.GRSCC

abbrev LayerRank := Fin codeCardinality
abbrev PackedLayer (q : Nat) := LayerRank × (Fin q → Slot × LayerRank)

def packedSample {q : Nat} (slot : Slot) (sample : PackedLayer q) : LayerSample q :=
  (slot, sample.1, (fun i => (sample.2 i).1), fun i => (sample.2 i).2)

def packedLocalEvent {q : Nat} (current : Finset (Fin q)) (slot : Slot)
    (sample : PackedLayer q) : Prop :=
  ∀ requirement : CodePosition, ∃ i ∈ current,
    coordinateSupply slot (sample.2 i).1
      (sameSlotSupply (decodedCodeword sample.1) (sample.2 i).2) requirement = true

instance packedLocalEvent_decidable {q : Nat} (current : Finset (Fin q)) (slot : Slot)
    (sample : PackedLayer q) : Decidable (packedLocalEvent current slot sample) := by
  unfold packedLocalEvent
  infer_instance

theorem packedLocalEvent_iff {q : Nat} (current : Finset (Fin q)) (slot : Slot)
    (sample : PackedLayer q) :
    packedLocalEvent current slot sample ↔ localLayerEvent current (packedSample slot sample) :=
  Iff.rfl

theorem coordinateSupply_self (slot : Slot) (profile : CodePosition → Bool)
    (requirement : CodePosition) : coordinateSupply slot slot profile requirement = profile requirement := by
  unfold coordinateSupply
  split <;> simp [divergesAt]

/-- Target rank together with the actual successful local tuple. -/
abbrev LocalEventData (slot : Slot) (same different : Nat) :=
  Σ target : LayerRank,
    {sample : LocalTuple LayerRank (DifferentHistory slot) same different //
      sample ∈ localCoveredSet same different (sameSlotSupply (decodedCodeword target))
        (differentSlotSupply slot (decodedCodeword target))}

theorem localEventData_card (slot : Slot) (same different : Nat) :
    Fintype.card (LocalEventData slot same different) =
      ∑ target : LayerRank,
        localSuccessNumerator slot (decodedCodeword target) same different := by
  simp only [LocalEventData, Fintype.card_sigma, Fintype.card_coe, localSuccessNumerator]

theorem localConditionalCount_event (slot : Slot) (incoming same : Nat) :
    Fintype.card (LocalEventData slot same (incoming - same)) =
      localConditionalCount slot incoming same := by
  exact localEventData_card slot same (incoming - same)

def fixedMatches {q : Nat} (slot : Slot) (sameCurrent sameOutside : Finset (Fin q))
    (history : Fin q → Slot × LayerRank) : Prop :=
  ∀ i, (history i).1 = slot ↔ i ∈ sameCurrent ∪ sameOutside

instance fixedMatches_decidable {q : Nat} (slot : Slot)
    (sameCurrent sameOutside : Finset (Fin q)) (history : Fin q → Slot × LayerRank) :
    Decidable (fixedMatches slot sameCurrent sameOutside history) := by
  unfold fixedMatches
  infer_instance

abbrev FixedLayerEvent {q : Nat} (slot : Slot) (current sameCurrent sameOutside : Finset (Fin q)) :=
  {sample : PackedLayer q //
    packedLocalEvent current slot sample ∧ fixedMatches slot sameCurrent sameOutside sample.2}

/-- The constrained current histories form the local event. Histories outside
the current owner retain independent code ranks, and every nonmatching one
retains one of the 31 different slots. -/
abbrev FixedLayerData {q : Nat} (slot : Slot) (current sameCurrent sameOutside : Finset (Fin q)) :=
  LocalEventData slot sameCurrent.card (current \ sameCurrent).card ×
    (((currentᶜ : Finset (Fin q)) → LayerRank) ×
      ((currentᶜ \ sameOutside : Finset (Fin q)) → {history : Slot // history ≠ slot}))

theorem fixed_current_different {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ho : sameOutside ⊆ currentᶜ) (history : Fin q → Slot × LayerRank)
    (hm : fixedMatches slot sameCurrent sameOutside history)
    {i : Fin q} (hi : i ∈ current \ sameCurrent) : (history i).1 ≠ slot := by
  intro heq
  rcases Finset.mem_union.mp ((hm i).mp heq) with ht | hu
  · exact (Finset.mem_sdiff.mp hi).2 ht
  · exact (Finset.mem_compl.mp (ho hu)) (Finset.mem_sdiff.mp hi).1

theorem fixed_outside_different {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (history : Fin q → Slot × LayerRank)
    (hm : fixedMatches slot sameCurrent sameOutside history)
    {i : Fin q} (hi : i ∈ currentᶜ \ sameOutside) : (history i).1 ≠ slot := by
  intro heq
  rcases Finset.mem_union.mp ((hm i).mp heq) with hti | hui
  · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hi).1) (ht hti)
  · exact (Finset.mem_sdiff.mp hi).2 hui

noncomputable def fixedLocalTuple {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ho : sameOutside ⊆ currentᶜ) (sample : FixedLayerEvent slot current sameCurrent sameOutside) :
    LocalTuple LayerRank (DifferentHistory slot) sameCurrent.card (current \ sameCurrent).card :=
  (fun i => (sample.val.2 (sameCurrent.equivFin.symm i)).2,
    fun i =>
      let index := (current \ sameCurrent).equivFin.symm i
      (⟨(sample.val.2 index).1,
        fixed_current_different ho sample.val.2 sample.property.2 index.property⟩,
        (sample.val.2 index).2))

theorem fixedLocalTuple_covered {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (_ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ)
    (sample : FixedLayerEvent slot current sameCurrent sameOutside) :
    fixedLocalTuple ho sample ∈ localCoveredSet sameCurrent.card (current \ sameCurrent).card
      (sameSlotSupply (decodedCodeword sample.val.1))
      (differentSlotSupply slot (decodedCodeword sample.val.1)) := by
  apply (localCoveredSet_mem _ _ _ _ _).mpr
  intro requirement
  obtain ⟨i, hi, hsupply⟩ := sample.property.1 requirement
  by_cases hti : i ∈ sameCurrent
  · left
    refine ⟨sameCurrent.equivFin ⟨i, hti⟩, ?_⟩
    have hslot : (sample.val.2 i).1 = slot :=
      (sample.property.2 i).mpr (Finset.mem_union.mpr (Or.inl hti))
    rw [hslot, coordinateSupply_self] at hsupply
    simpa only [fixedLocalTuple, Equiv.symm_apply_apply] using hsupply
  · right
    refine ⟨(current \ sameCurrent).equivFin ⟨i, Finset.mem_sdiff.mpr ⟨hi, hti⟩⟩, ?_⟩
    simpa only [fixedLocalTuple, Equiv.symm_apply_apply, differentSlotSupply] using hsupply

noncomputable def fixedLayerData {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ)
    (sample : FixedLayerEvent slot current sameCurrent sameOutside) :
    FixedLayerData slot current sameCurrent sameOutside :=
  (⟨sample.val.1, fixedLocalTuple ho sample, fixedLocalTuple_covered ht ho sample⟩,
    (fun i => (sample.val.2 i).2,
      fun i => ⟨(sample.val.2 i).1,
        fixed_outside_different ht sample.val.2 sample.property.2 i.property⟩))

noncomputable def restoreHistory {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (data : FixedLayerData slot current sameCurrent sameOutside) (i : Fin q) : Slot × LayerRank :=
  if hc : i ∈ current then
    if ht : i ∈ sameCurrent then
      (slot, data.1.2.val.1 (sameCurrent.equivFin ⟨i, ht⟩))
    else
      let h := data.1.2.val.2 ((current \ sameCurrent).equivFin
        ⟨i, Finset.mem_sdiff.mpr ⟨hc, ht⟩⟩)
      (h.1.val, h.2)
  else
    let outside : (currentᶜ : Finset (Fin q)) := ⟨i, Finset.mem_compl.mpr hc⟩
    if ho : i ∈ sameOutside then
      (slot, data.2.1 outside)
    else
      ((data.2.2 ⟨i, Finset.mem_sdiff.mpr ⟨outside.property, ho⟩⟩).val, data.2.1 outside)

theorem restoreHistory_matches {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ)
    (data : FixedLayerData slot current sameCurrent sameOutside) :
    fixedMatches slot sameCurrent sameOutside (restoreHistory data) := by
  intro i
  by_cases hc : i ∈ current
  · have hou : i ∉ sameOutside := fun h => (Finset.mem_compl.mp (ho h)) hc
    by_cases hti : i ∈ sameCurrent
    · simp [restoreHistory, hc, hti]
    · have hne := (data.1.2.val.2 ((current \ sameCurrent).equivFin
        ⟨i, Finset.mem_sdiff.mpr ⟨hc, hti⟩⟩)).1.property
      simp [restoreHistory, hc, hti, hou, hne]
  · have hti : i ∉ sameCurrent := fun h => hc (ht h)
    by_cases hou : i ∈ sameOutside
    · simp [restoreHistory, hc, hou]
    · have hne := (data.2.2
        ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hc, hou⟩⟩).property
      simp [restoreHistory, hc, hti, hou, hne]

theorem restoreHistory_event {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current)
    (data : FixedLayerData slot current sameCurrent sameOutside) :
    packedLocalEvent current slot (data.1.1, restoreHistory data) := by
  intro requirement
  rcases (localCoveredSet_mem _ _ _ _ _).mp data.1.2.property requirement with
    ⟨i, hsupply⟩ | ⟨i, hsupply⟩
  · let index := sameCurrent.equivFin.symm i
    have hti : index.val ∈ sameCurrent := index.property
    have hc : index.val ∈ current := ht hti
    refine ⟨index.val, hc, ?_⟩
    simpa [restoreHistory, hc, hti, index, coordinateSupply_self] using hsupply
  · let index := (current \ sameCurrent).equivFin.symm i
    have hc : index.val ∈ current := (Finset.mem_sdiff.mp index.property).1
    have hti : index.val ∉ sameCurrent := (Finset.mem_sdiff.mp index.property).2
    refine ⟨index.val, hc, ?_⟩
    simpa [restoreHistory, hc, hti, index, differentSlotSupply] using hsupply

noncomputable def restoreLayerEvent {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ)
    (data : FixedLayerData slot current sameCurrent sameOutside) :
    FixedLayerEvent slot current sameCurrent sameOutside :=
  ⟨(data.1.1, restoreHistory data), restoreHistory_event ht data,
    restoreHistory_matches ht ho data⟩

theorem restore_fixedLayerData {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ)
    (sample : FixedLayerEvent slot current sameCurrent sameOutside) :
    restoreLayerEvent ht ho (fixedLayerData ht ho sample) = sample := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    change restoreHistory (fixedLayerData ht ho sample) i = sample.val.2 i
    by_cases hc : i ∈ current
    · by_cases hti : i ∈ sameCurrent
      · have hslot : (sample.val.2 i).1 = slot :=
          (sample.property.2 i).mpr (Finset.mem_union.mpr (Or.inl hti))
        apply Prod.ext <;>
          simp [restoreHistory, fixedLayerData, fixedLocalTuple, hc, hti, hslot]
      · apply Prod.ext <;>
          simp [restoreHistory, fixedLayerData, fixedLocalTuple, hc, hti]
    · by_cases hou : i ∈ sameOutside
      · have hslot : (sample.val.2 i).1 = slot :=
          (sample.property.2 i).mpr (Finset.mem_union.mpr (Or.inr hou))
        apply Prod.ext <;>
          simp [restoreHistory, fixedLayerData, fixedLocalTuple, hc, hou, hslot]
      · apply Prod.ext <;>
          simp [restoreHistory, fixedLayerData, fixedLocalTuple, hc, hou]

theorem fixedLayerData_restore {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ)
    (data : FixedLayerData slot current sameCurrent sameOutside) :
    fixedLayerData ht ho (restoreLayerEvent ht ho data) = data := by
  rcases data with ⟨⟨target, tuple⟩, codes, slots⟩
  apply Prod.ext
  · refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hti := (sameCurrent.equivFin.symm i).property
      have hc := ht hti
      simp [fixedLayerData, fixedLocalTuple, restoreLayerEvent, restoreHistory, hc]
    · funext i
      have hc := (Finset.mem_sdiff.mp ((current \ sameCurrent).equivFin.symm i).property).1
      have hti := (Finset.mem_sdiff.mp ((current \ sameCurrent).equivFin.symm i).property).2
      apply Prod.ext
      · apply Subtype.ext
        simp [fixedLayerData, fixedLocalTuple, restoreLayerEvent, restoreHistory, hc, hti]
      · simp [fixedLayerData, fixedLocalTuple, restoreLayerEvent, restoreHistory, hc, hti]
  · apply Prod.ext
    · funext i
      have hc := Finset.mem_compl.mp i.property
      by_cases hou : i.val ∈ sameOutside <;>
        simp [fixedLayerData, restoreLayerEvent, restoreHistory, hc, hou]
    · funext i
      have hc := Finset.mem_compl.mp (Finset.mem_sdiff.mp i.property).1
      have hou := (Finset.mem_sdiff.mp i.property).2
      apply Subtype.ext
      simp [fixedLayerData, restoreLayerEvent, restoreHistory, hc, hou]

noncomputable def fixedLayerEventEquiv {q : Nat} {slot : Slot}
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ) :
    FixedLayerEvent slot current sameCurrent sameOutside ≃
      FixedLayerData slot current sameCurrent sameOutside where
  toFun := fixedLayerData ht ho
  invFun := restoreLayerEvent ht ho
  left_inv := restore_fixedLayerData ht ho
  right_inv := fixedLayerData_restore ht ho

/-- The fixed matching-set count. The factor from current-owner histories is
the already proved local event count; every remaining rank and slot is counted
through an explicit finite function space. -/
theorem fixedLayerEvent_card {q : Nat} (slot : Slot)
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ) :
    Fintype.card (FixedLayerEvent slot current sameCurrent sameOutside) =
      localConditionalCount slot current.card sameCurrent.card *
        codeCardinality ^ (q - current.card) *
        31 ^ (q - current.card - sameOutside.card) := by
  have hdiff := Finset.card_sdiff_of_subset ht
  have hcomp : (currentᶜ : Finset (Fin q)).card = q - current.card := by
    simp [Finset.card_compl]
  have hout := Finset.card_sdiff_of_subset ho
  have hlocal : Fintype.card (LocalEventData slot sameCurrent.card (current \ sameCurrent).card) =
      localConditionalCount slot current.card sameCurrent.card := by
    rw [hdiff]
    exact localConditionalCount_event slot current.card sameCurrent.card
  rw [Fintype.card_congr (fixedLayerEventEquiv ht ho)]
  simp only [FixedLayerData, Fintype.card_prod]
  rw [hlocal]
  simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, different_slot_card,
    LayerRank, hcomp, hout]
  ring

def currentMatches {q : Nat} (current : Finset (Fin q)) (sample : LayerSample q) : Finset (Fin q) :=
  current.filter (fun i => sample.2.2.1 i = sample.1)

def outsideMatches {q : Nat} (current : Finset (Fin q)) (sample : LayerSample q) : Finset (Fin q) :=
  currentᶜ.filter (fun i => sample.2.2.1 i = sample.1)

def layerKey {q : Nat} (current : Finset (Fin q)) (sample : LayerSample q) :
    Slot × (Finset (Fin q) × Finset (Fin q)) :=
  (sample.1, currentMatches current sample, outsideMatches current sample)

theorem nextOwnerCount_split {q : Nat} (current : Finset (Fin q)) (sample : LayerSample q) :
    nextOwnerCount sample = (currentMatches current sample).card +
      (outsideMatches current sample).card := by
  have hu : (Finset.univ.filter (fun i => sample.2.2.1 i = sample.1)) =
      currentMatches current sample ∪ outsideMatches current sample := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, currentMatches,
      outsideMatches, Finset.mem_union, Finset.mem_compl]
    tauto
  have hd : Disjoint (currentMatches current sample) (outsideMatches current sample) := by
    apply Finset.disjoint_left.mpr
    intro i hi ho
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp ho).1) (Finset.mem_filter.mp hi).1
  change (Finset.univ.filter (fun i => sample.2.2.1 i = sample.1)).card = _
  rw [hu, Finset.card_union_of_disjoint hd]

theorem layerKey_packed_iff {q : Nat} (slot : Slot) (sample : PackedLayer q)
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ) :
    layerKey current (packedSample slot sample) = (slot, sameCurrent, sameOutside) ↔
      fixedMatches slot sameCurrent sameOutside sample.2 := by
  constructor
  · intro hk i
    have htc : currentMatches current (packedSample slot sample) = sameCurrent := congrArg
      (fun p : Slot × (Finset (Fin q) × Finset (Fin q)) => p.2.1) hk
    have hoc : outsideMatches current (packedSample slot sample) = sameOutside := congrArg
      (fun p : Slot × (Finset (Fin q) × Finset (Fin q)) => p.2.2) hk
    constructor
    · intro hslot
      by_cases hc : i ∈ current
      · apply Finset.mem_union.mpr
        left
        rw [← htc]
        exact Finset.mem_filter.mpr ⟨hc, hslot⟩
      · apply Finset.mem_union.mpr
        right
        rw [← hoc]
        exact Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hc, hslot⟩
    · intro hi
      rcases Finset.mem_union.mp hi with hit | hio
      · rw [← htc] at hit
        exact (Finset.mem_filter.mp hit).2
      · rw [← hoc] at hio
        exact (Finset.mem_filter.mp hio).2
  · intro hm
    change (slot, currentMatches current (packedSample slot sample),
      outsideMatches current (packedSample slot sample)) = (slot, sameCurrent, sameOutside)
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ext i
        simp only [currentMatches, packedSample, Finset.mem_filter]
        constructor
        · rintro ⟨hc, hslot⟩
          rcases Finset.mem_union.mp ((hm i).mp hslot) with hti | hou
          · exact hti
          · exact False.elim ((Finset.mem_compl.mp (ho hou)) hc)
        · intro hti
          exact ⟨ht hti, (hm i).mpr (Finset.mem_union.mpr (Or.inl hti))⟩
      · ext i
        simp only [outsideMatches, packedSample, Finset.mem_filter]
        constructor
        · rintro ⟨hc, hslot⟩
          rcases Finset.mem_union.mp ((hm i).mp hslot) with hti | hou
          · exact False.elim ((Finset.mem_compl.mp hc) (ht hti))
          · exact hou
        · intro hou
          exact ⟨ho hou, (hm i).mpr (Finset.mem_union.mpr (Or.inr hou))⟩

theorem packedSample_repack {q : Nat} (sample : LayerSample q) (slot : Slot)
    (hslot : sample.1 = slot) :
    packedSample slot (sample.2.1, fun i => (sample.2.2.1 i, sample.2.2.2 i)) = sample := by
  rcases sample with ⟨original, target, slots, codes⟩
  dsimp at hslot
  subst original
  rfl

noncomputable def layerFiberEquiv {q : Nat} (slot : Slot)
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ) :
    {sample : LayerSample q // localLayerEvent current sample ∧
      layerKey current sample = (slot, sameCurrent, sameOutside)} ≃
      FixedLayerEvent slot current sameCurrent sameOutside where
  toFun sample := by
    let packed : PackedLayer q :=
      (sample.val.2.1, fun i => (sample.val.2.2.1 i, sample.val.2.2.2 i))
    have hp : packedSample slot packed = sample.val :=
      packedSample_repack sample.val slot (congrArg Prod.fst sample.property.2)
    refine ⟨packed, ?_, ?_⟩
    · apply (packedLocalEvent_iff current slot packed).mpr
      rw [hp]
      exact sample.property.1
    · apply (layerKey_packed_iff slot packed ht ho).mp
      rw [hp]
      exact sample.property.2
  invFun sample := ⟨packedSample slot sample.val,
    (packedLocalEvent_iff current slot sample.val).mp sample.property.1,
    (layerKey_packed_iff slot sample.val ht ho).mpr sample.property.2⟩
  left_inv sample := by
    apply Subtype.ext
    exact packedSample_repack sample.val slot (congrArg Prod.fst sample.property.2)
  right_inv sample := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      apply Prod.ext <;> rfl

theorem layerFiber_card {q : Nat} (slot : Slot)
    {current sameCurrent sameOutside : Finset (Fin q)}
    (ht : sameCurrent ⊆ current) (ho : sameOutside ⊆ currentᶜ) :
    Fintype.card {sample : LayerSample q // localLayerEvent current sample ∧
      layerKey current sample = (slot, sameCurrent, sameOutside)} =
      localConditionalCount slot current.card sameCurrent.card *
        codeCardinality ^ (q - current.card) *
        31 ^ (q - current.card - sameOutside.card) := by
  rw [Fintype.card_congr (layerFiberEquiv slot ht ho)]
  exact fixedLayerEvent_card slot ht ho

def matchingKeys {q : Nat} (current : Finset (Fin q)) (next : Nat) :
    Finset (Slot × (Finset (Fin q) × Finset (Fin q))) :=
  (Finset.univ ×ˢ (current.powerset ×ˢ currentᶜ.powerset)).filter
    (fun key => key.2.1.card + key.2.2.card = next)

@[simp] theorem mem_matchingKeys {q : Nat} {current sameCurrent sameOutside : Finset (Fin q)}
    {slot : Slot} {next : Nat} :
    (slot, sameCurrent, sameOutside) ∈ matchingKeys current next ↔
      sameCurrent ⊆ current ∧ sameOutside ⊆ currentᶜ ∧
        sameCurrent.card + sameOutside.card = next := by
  simp [matchingKeys, and_assoc]

theorem nextOwnerCount_of_key {q : Nat} {current sameCurrent sameOutside : Finset (Fin q)}
    {slot : Slot} {sample : LayerSample q}
    (hk : layerKey current sample = (slot, sameCurrent, sameOutside)) :
    nextOwnerCount sample = sameCurrent.card + sameOutside.card := by
  have ht := congrArg
    (fun key : Slot × (Finset (Fin q) × Finset (Fin q)) => key.2.1) hk
  have ho := congrArg
    (fun key : Slot × (Finset (Fin q) × Finset (Fin q)) => key.2.2) hk
  rw [nextOwnerCount_split current sample]
  change (currentMatches current sample).card + (outsideMatches current sample).card = _
  rw [show currentMatches current sample = sameCurrent from ht,
    show outsideMatches current sample = sameOutside from ho]

def layerTransitionCount {q : Nat} (current : Finset (Fin q)) (next : Nat) : Nat :=
  ((Finset.univ : Finset (LayerSample q)).filter (fun sample =>
    localLayerEvent current sample ∧ nextOwnerCount sample = next)).card

private theorem filter_mapsTo {α β : Type*} (family : Finset α) (keys : Finset β)
    (event : α → Prop) [DecidablePred event] (key : α → β)
    (hkey : ∀ sample, event sample → key sample ∈ keys) :
    (family.filter event : Set α).MapsTo key keys := by
  intro sample hs
  exact hkey sample (Finset.mem_filter.mp hs).2

theorem layerTransitionCount_keysum {q : Nat} (current : Finset (Fin q)) (next : Nat) :
    layerTransitionCount current next =
      ∑ key ∈ matchingKeys current next,
        localConditionalCount key.1 current.card key.2.1.card *
          codeCardinality ^ (q - current.card) * 31 ^ (q - current.card - key.2.2.card) := by
  let event : LayerSample q → Prop := fun sample =>
    localLayerEvent current sample ∧ nextOwnerCount sample = next
  letI : DecidablePred event := fun sample => by dsimp [event]; infer_instance
  let samples : Finset (LayerSample q) := Finset.univ.filter event
  have hm : (samples : Set (LayerSample q)).MapsTo (layerKey current) (matchingKeys current next) :=
    filter_mapsTo Finset.univ (matchingKeys current next) event (layerKey current) (by
      intro sample hs
      have hnext : nextOwnerCount sample = next := hs.2
      apply mem_matchingKeys.mpr
      refine ⟨Finset.filter_subset _ _, Finset.filter_subset _ _, ?_⟩
      exact (nextOwnerCount_split current sample).symm.trans hnext)
  change samples.card = _
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro key hkey
  rcases key with ⟨slot, sameCurrent, sameOutside⟩
  rcases mem_matchingKeys.mp hkey with ⟨ht, ho, hcount⟩
  have hf : samples.filter (fun sample => layerKey current sample =
      (slot, sameCurrent, sameOutside)) =
      Finset.univ.filter (fun sample => localLayerEvent current sample ∧
        layerKey current sample = (slot, sameCurrent, sameOutside)) := by
    ext sample
    simp only [samples, event, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hevent, _hnext⟩, hk⟩
      exact ⟨hevent, hk⟩
    · rintro ⟨hevent, hk⟩
      exact ⟨⟨hevent, (nextOwnerCount_of_key hk).trans hcount⟩, hk⟩
  rw [hf]
  simpa only [Fintype.card_subtype] using layerFiber_card slot ht ho

/-- Reindex all subsets by their cardinalities, retaining their multiplicity
as the corresponding binomial coefficient. -/
theorem sum_powerset_by_card {α : Type*} [DecidableEq α] (s : Finset α) (f : Nat → Nat) :
    (∑ t ∈ s.powerset, f t.card) =
      ∑ size ∈ Finset.range (s.card + 1), Nat.choose s.card size * f size := by
  rw [s.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  apply Finset.sum_congr rfl
  intro size hsize
  calc
    (∑ t ∈ s.powersetCard size, f t.card) =
        ∑ _t ∈ s.powersetCard size, f size := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_powersetCard.mp ht).2]
    _ = Nat.choose s.card size * f size := by simp

theorem sum_range_matching_card (n next same : Nat) (f : Nat → Nat) :
    (∑ outside ∈ Finset.range (n + 1), Nat.choose n outside *
      (if same + outside = next then f outside else 0)) =
      if same ≤ next then Nat.choose n (next - same) * f (next - same) else 0 := by
  by_cases hs : same ≤ next
  · rw [if_pos hs]
    by_cases hn : next - same < n + 1
    · rw [Finset.sum_eq_single (next - same)]
      · simp [show same + (next - same) = next by omega]
      · intro other hother hne
        have hfalse : same + other ≠ next := by omega
        simp [hfalse]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hn))
    · have hz : Nat.choose n (next - same) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, zero_mul]
      apply Finset.sum_eq_zero
      intro outside houtside
      have hfalse : same + outside ≠ next := by
        have hb := Finset.mem_range.mp houtside
        omega
      simp [hfalse]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro outside houtside
    have hfalse : same + outside ≠ next := by omega
    simp [hfalse]

theorem layerTransitionCount_powersets {q : Nat} (current : Finset (Fin q)) (next : Nat) :
    layerTransitionCount current next =
      32 * codeCardinality ^ (q - current.card) *
        ∑ sameCurrent ∈ current.powerset,
          ∑ sameOutside ∈ (currentᶜ : Finset (Fin q)).powerset,
            if sameCurrent.card + sameOutside.card = next then
              localConditionalCount (0 : Slot) current.card sameCurrent.card *
                31 ^ (q - current.card - sameOutside.card)
            else 0 := by
  have hf (slot : Slot) :
      (∑ sameCurrent ∈ current.powerset,
        ∑ sameOutside ∈ (currentᶜ : Finset (Fin q)).powerset,
          if sameCurrent.card + sameOutside.card = next then
            localConditionalCount slot current.card sameCurrent.card *
              codeCardinality ^ (q - current.card) * 31 ^ (q - current.card - sameOutside.card)
          else 0) =
      codeCardinality ^ (q - current.card) *
        ∑ sameCurrent ∈ current.powerset,
          ∑ sameOutside ∈ (currentᶜ : Finset (Fin q)).powerset,
            if sameCurrent.card + sameOutside.card = next then
              localConditionalCount (0 : Slot) current.card sameCurrent.card *
                31 ^ (q - current.card - sameOutside.card)
            else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sameCurrent hsame
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sameOutside houtside
    by_cases hnext : sameCurrent.card + sameOutside.card = next
    · simp only [if_pos hnext]
      rw [localConditionalCount_slot_independent slot (0 : Slot)]
      ring
    · simp [hnext]
  rw [layerTransitionCount_keysum]
  unfold matchingKeys
  rw [Finset.sum_filter, Finset.sum_product]
  simp only [Finset.sum_product]
  simp_rw [hf]
  simp [Nat.mul_assoc]

def transitionCountTerm (q incoming next same : Nat) : Nat :=
  if same ≤ next then
    Nat.choose incoming same * Nat.choose (q - incoming) (next - same) *
      localConditionalCount (0 : Slot) incoming same *
        31 ^ (q - incoming - (next - same))
  else 0

theorem layerTransitionCount_binomial {q : Nat} (current : Finset (Fin q)) (next : Nat) :
    layerTransitionCount current next =
      32 * codeCardinality ^ (q - current.card) *
        ∑ same ∈ Finset.range (current.card + 1), transitionCountTerm q current.card next same := by
  rw [layerTransitionCount_powersets]
  apply congrArg (fun value => 32 * codeCardinality ^ (q - current.card) * value)
  have hcomp : (currentᶜ : Finset (Fin q)).card = q - current.card := by
    simp [Finset.card_compl]
  calc
    _ = ∑ sameCurrent ∈ current.powerset,
        ∑ outside ∈ Finset.range ((currentᶜ : Finset (Fin q)).card + 1),
          Nat.choose (currentᶜ : Finset (Fin q)).card outside *
            (if sameCurrent.card + outside = next then
              localConditionalCount (0 : Slot) current.card sameCurrent.card *
                31 ^ (q - current.card - outside) else 0) := by
      apply Finset.sum_congr rfl
      intro sameCurrent hsame
      exact sum_powerset_by_card (currentᶜ : Finset (Fin q)) (fun outside =>
        if sameCurrent.card + outside = next then
          localConditionalCount (0 : Slot) current.card sameCurrent.card *
            31 ^ (q - current.card - outside) else 0)
    _ = ∑ same ∈ Finset.range (current.card + 1), Nat.choose current.card same *
        (∑ outside ∈ Finset.range (q - current.card + 1),
          Nat.choose (q - current.card) outside *
            (if same + outside = next then
              localConditionalCount (0 : Slot) current.card same *
                31 ^ (q - current.card - outside) else 0)) := by
      have houter := sum_powerset_by_card current (fun same =>
        ∑ outside ∈ Finset.range ((currentᶜ : Finset (Fin q)).card + 1),
          Nat.choose (currentᶜ : Finset (Fin q)).card outside *
            (if same + outside = next then
              localConditionalCount (0 : Slot) current.card same *
                31 ^ (q - current.card - outside) else 0))
      simpa only [hcomp] using houter
    _ = _ := by
      apply Finset.sum_congr rfl
      intro same hsame
      rw [sum_range_matching_card]
      by_cases hs : same ≤ next
      · simp only [transitionCountTerm, if_pos hs]
        ring
      · simp [transitionCountTerm, hs]

theorem layerSample_card (q : Nat) :
    Fintype.card (LayerSample q) = 32 * codeCardinality * (32 * codeCardinality) ^ q := by
  simp only [LayerSample, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [mul_pow]
  ring

theorem layerTransitionCoefficient_count {q : Nat} (current : Finset (Fin q)) (next : Nat) :
    layerTransitionCoefficient current next =
      (layerTransitionCount current next : Rat) /
        ((32 * codeCardinality * (32 * codeCardinality) ^ q : Nat) : Rat) := by
  rw [layerTransitionCoefficient, layerSample_card]
  rfl

@[simp] theorem transitionCountTerm_zero (q incoming next : Nat) :
    transitionCountTerm q incoming next 0 = 0 := by
  simp [transitionCountTerm, localConditionalCount_no_same]

/-- Normalize one actual fixed-cardinality count into the two binomial slot
factors and the conditional local coverage count. -/
theorem jointKernel_term_count (q incoming next same : Nat) (hin : incoming ≤ q)
    (hs : 0 < same) (hsi : same ≤ incoming) :
    (if same ≤ next then
      binomialMass incoming same ((1 : Rat) / 32) * localCover incoming same *
        binomialMass (q - incoming) (next - same) ((1 : Rat) / 32)
      else 0) =
      (transitionCountTerm q incoming next same : Rat) /
        ((32 ^ q * 15597 ^ (incoming + 1) : Nat) : Rat) := by
  by_cases hsn : same ≤ next
  · rw [if_pos hsn]
    by_cases hout : next - same ≤ q - incoming
    · rw [binomialMass, if_pos hsi, binomialMass, if_pos hout,
        localCover_event_count (0 : Slot) incoming same hs hsi]
      simp only [transitionCountTerm, if_pos hsn]
      push_cast
      norm_num only [show (1 : Rat) - 1 / 32 = 31 / 32 by norm_num]
      simp only [div_pow, one_pow]
      have hpow : (32 : Rat) ^ q =
          32 ^ same * 32 ^ (incoming - same) *
            32 ^ (next - same) * 32 ^ (q - incoming - (next - same)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
    · have hchoose : Nat.choose (q - incoming) (next - same) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp [binomialMass, hout, transitionCountTerm, hsn, hchoose]
  · simp [hsn, transitionCountTerm]

private theorem sum_map_range_rat (f : Nat → Rat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem jointKernel_count (q incoming next : Nat) (hin : incoming ≤ q) :
    jointKernel q incoming next =
      ((∑ same ∈ Finset.range (incoming + 1),
        transitionCountTerm q incoming next same : Nat) : Rat) /
        ((32 ^ q * 15597 ^ (incoming + 1) : Nat) : Rat) := by
  unfold jointKernel
  rw [sum_map_range_rat]
  push_cast
  calc
    _ = ∑ index ∈ Finset.range incoming,
        (transitionCountTerm q incoming next (index + 1) : Rat) /
          (32 ^ q * 15597 ^ (incoming + 1)) := by
      apply Finset.sum_congr rfl
      intro index hindex
      have h := jointKernel_term_count q incoming next (index + 1) hin (by omega)
        (by have hi := Finset.mem_range.mp hindex; omega)
      push_cast at h
      exact h
    _ = (∑ index ∈ Finset.range incoming,
        (transitionCountTerm q incoming next (index + 1) : Rat)) /
          (32 ^ q * 15597 ^ (incoming + 1)) := (Finset.sum_div _ _ _).symm
    _ = _ := by
      congr 1
      rw [Finset.sum_range_succ']
      simp only [transitionCountTerm_zero, Nat.cast_zero, add_zero]

/-- The literal finite layer experiment is exactly the joint kernel. The
identity of the current owner set has been counted away, rather than assumed
irrelevant or replaced by a supplied transition law. -/
theorem layerTransitionCoefficient_eq_jointKernel {q : Nat}
    (current : Finset (Fin q)) (next : Nat) :
    layerTransitionCoefficient current next = jointKernel q current.card next := by
  have hin : current.card ≤ q := by
    simpa using Finset.card_le_card (Finset.subset_univ current)
  rw [layerTransitionCoefficient_count, layerTransitionCount_binomial,
    jointKernel_count q current.card next hin]
  push_cast
  rw [codeCardinality_eq]
  norm_num only
  have hpow : (15597 : Rat) ^ q =
      15597 ^ (q - current.card) * 15597 ^ current.card := by
    rw [← pow_add]
    congr 1
    omega
  have hbase : (499104 : Rat) = 32 * 15597 := by norm_num
  simp only [hbase, mul_pow, hpow, pow_succ]
  field_simp

end PoissonDAG.GRSCC
