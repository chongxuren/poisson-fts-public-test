import PoissonDAG.Constructions.GRSCC.RankEncoding

/-! Protected circuit output specification and exact refinement. -/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

/-- Generic interfaces keep the protected raw enumeration symbolic. -/
theorem scheme_mem_accepted (s : Scheme) (raw : Nat) :
    raw ∈ s.accepted ↔ raw < 2 ^ s.encoder.inputs ∧ s.accept raw = true := by
  simp only [Scheme.accepted, Scheme.raws, List.mem_filter, List.mem_range]

theorem scheme_accepted_nodup (s : Scheme) : s.accepted.Nodup :=
  List.Nodup.filter _ List.nodup_range

def decodeRaw (raw : Nat) : Option Route :=
  if h : rawThreshold raw < threshold ∧ rawRank raw < encodingCardinality then
    some (decodedRoute ⟨rawRank raw, h.2⟩)
  else none

theorem decodeRaw_isSome_iff (raw : Nat) :
    (decodeRaw raw).isSome = true ↔ rawAccept raw = true := by
  simp only [decodeRaw, rawAccept]
  split <;> simp_all

theorem accepted_raw_reconstruction (raw : Nat) :
    rawThreshold raw + 2 ^ 32 * rawRank raw = raw := by
  exact Nat.mod_add_div raw (2 ^ 32)

/-- Exact output string that the eventual Boolean encoder must compute.
Rejected encodings have zero masks. This is a transparent compilation target,
not an alternative encoder field in the protected Scheme type. -/
def rawOutputFor (n : Nat) (decoded : Option (List Bool × List Bool)) : List Bool :=
  match decoded with
  | none => false :: List.replicate (2 * n) false
  | some masks => true :: (masks.1 ++ masks.2)

def routeMasks (decoded : Option Route) : Option (List Bool × List Bool) :=
  decoded.map (fun route => (route.frontier, route.plan))

@[irreducible] def rawOutput (raw : Nat) : List Bool :=
  rawOutputFor graphNodes (routeMasks (decodeRaw raw))

theorem rawOutput_eq (raw : Nat) :
    rawOutput raw = rawOutputFor graphNodes (routeMasks (decodeRaw raw)) := by
  unfold rawOutput
  rfl

theorem rawOutputFor_length (n : Nat) (decoded : Option (List Bool × List Bool))
    (hlength : ∀ left right, decoded = some (left, right) →
      left.length = n ∧ right.length = n) :
    (rawOutputFor n decoded).length = 1 + 2 * n := by
  cases decoded with
  | none => simp only [rawOutputFor, List.length_cons, List.length_replicate]; omega
  | some masks =>
      obtain ⟨hl, hr⟩ := hlength masks.1 masks.2 rfl
      simp only [rawOutputFor, List.length_cons, List.length_append, hl, hr]
      omega

theorem routeMasks_lengths (decoded : Option Route) :
    ∀ left right, routeMasks decoded = some (left, right) →
      left.length = graphNodes ∧ right.length = graphNodes := by
  cases decoded with
  | none => intro left right h; cases h
  | some route =>
      intro left right h
      have hpair : (route.frontier, route.plan) = (left, right) := Option.some.inj h
      exact ⟨(congrArg List.length (congrArg Prod.fst hpair)).symm.trans (frontier_length route),
        (congrArg List.length (congrArg Prod.snd hpair)).symm.trans (plan_length route)⟩

theorem rawOutput_length (raw : Nat) :
    (rawOutput raw).length = 1 + 2 * graphNodes :=
  (congrArg List.length (rawOutput_eq raw)).trans
    (rawOutputFor_length graphNodes _ (routeMasks_lengths _))

theorem rawOutput_none (raw : Nat) (hdecode : decodeRaw raw = none) :
    rawOutput raw = false :: List.replicate (2 * graphNodes) false :=
  (rawOutput_eq raw).trans
    (congrArg (fun decoded => rawOutputFor graphNodes (routeMasks decoded)) hdecode)

theorem rawOutput_some (raw : Nat) (route : Route) (hdecode : decodeRaw raw = some route) :
    rawOutput raw = true :: (route.frontier ++ route.plan) :=
  (rawOutput_eq raw).trans
    (congrArg (fun decoded => rawOutputFor graphNodes (routeMasks decoded)) hdecode)

def schemeOfCircuit (encoder : Circuit) : Scheme :=
  { graph := graph, encoder := encoder, counterBits := counterWidth }

/-- All data are retained in `Circuit`; these are the precise syntactic and
extensional proof obligations for a compiler. No existence is asserted here. -/
def CircuitRefines (encoder : Circuit) : Prop :=
  encoder.Valid ∧ encoder.inputs = rawBits ∧
    encoder.outputs.length = 1 + 2 * graphNodes ∧
    ∀ raw < 2 ^ rawBits, encoder.eval raw = rawOutput raw

theorem rawOutputFor_accept (n : Nat) (decoded : Option (List Bool × List Bool)) :
    get (rawOutputFor n decoded) 0 = decoded.isSome := by
  cases decoded <;> rfl

theorem routeMasks_isSome (decoded : Option Route) :
    (routeMasks decoded).isSome = decoded.isSome := by
  cases decoded <;> rfl

theorem rawOutput_accept (raw : Nat) : get (rawOutput raw) 0 = rawAccept raw := by
  calc
    get (rawOutput raw) 0 =
        get (rawOutputFor graphNodes (routeMasks (decodeRaw raw))) 0 :=
      congrArg (fun bits => get bits 0) (rawOutput_eq raw)
    _ = (routeMasks (decodeRaw raw)).isSome := rawOutputFor_accept graphNodes _
    _ = (decodeRaw raw).isSome := routeMasks_isSome _
    _ = rawAccept raw := Bool.eq_iff_iff.mpr (decodeRaw_isSome_iff raw)

theorem scheme_accept_of_refinement (encoder : Circuit)
    (href : CircuitRefines encoder) (raw : Nat) (hraw : raw < 2 ^ rawBits) :
    (schemeOfCircuit encoder).accept raw = rawAccept raw := by
  simp only [Scheme.accept, schemeOfCircuit, href.2.2.2 raw hraw]
  exact rawOutput_accept raw

theorem scheme_frontier_of_refinement (encoder : Circuit)
    (href : CircuitRefines encoder) (raw : Nat) (hraw : raw < 2 ^ rawBits)
    (route : Route) (hdecode : decodeRaw raw = some route) :
    (schemeOfCircuit encoder).frontier raw = route.frontier := by
  simp only [Scheme.frontier, schemeOfCircuit, href.2.2.2 raw hraw,
    rawOutput_some raw route hdecode, List.drop_succ_cons, List.drop_zero,
    graph_length']
  exact List.take_left' (frontier_length route)

theorem scheme_plan_of_refinement (encoder : Circuit)
    (href : CircuitRefines encoder) (raw : Nat) (hraw : raw < 2 ^ rawBits)
    (route : Route) (hdecode : decodeRaw raw = some route) :
    (schemeOfCircuit encoder).plan raw = route.plan := by
  simp only [Scheme.plan, schemeOfCircuit, href.2.2.2 raw hraw,
    rawOutput_some raw route hdecode, graph_length']
  rw [Nat.add_comm 1 graphNodes, List.drop_succ_cons,
    List.drop_left' (frontier_length route), ← plan_length route,
    List.take_length]

theorem rawAccept_zero : rawAccept 0 = true := by
  norm_num [rawAccept, rawThreshold, rawRank, threshold,
    encodingCardinality, coordinateRadix, codeCardinality_eq,
    bucketCount, bucketBits, initialOwnerCount, initialOwnerBits,
    slotCount, treeHeight, layerCount]

theorem scheme_wellFormed_of_refinement (encoder : Circuit)
    (href : CircuitRefines encoder) : (schemeOfCircuit encoder).WellFormed := by
  have hinputs := href.2.1
  have hzeroRaw : (0 : Nat) < 2 ^ rawBits := by norm_num [rawBits]
  have hzeroAccept : (schemeOfCircuit encoder).accept 0 = true := by
    rw [scheme_accept_of_refinement encoder href 0 hzeroRaw]
    exact rawAccept_zero
  have hzero : 0 ∈ (schemeOfCircuit encoder).accepted := by
    apply (scheme_mem_accepted _ _).mpr
    refine ⟨?_, hzeroAccept⟩
    simpa only [schemeOfCircuit, hinputs] using hzeroRaw
  refine ⟨?_, ?_, href.1, ?_, ?_, ?_⟩
  · simp only [schemeOfCircuit, graph_length]
    decide
  · simpa only [schemeOfCircuit, hinputs, rawBits, thresholdBits, rankBits] using
      (by decide : 0 < (170 : Nat))
  · simpa only [schemeOfCircuit, graph_length'] using href.2.2.1
  · exact graph_valid
  · exact List.length_pos_iff_exists_mem.mpr ⟨0, hzero⟩

theorem accepted_toFinset_of_refinement (encoder : Circuit)
    (href : CircuitRefines encoder) :
    (schemeOfCircuit encoder).accepted.toFinset = acceptedRawSet := by
  let s := schemeOfCircuit encoder
  ext raw
  constructor
  · intro h
    obtain ⟨hraw, hacc⟩ := (scheme_mem_accepted s raw).mp (List.mem_toFinset.mp h)
    have hbound : raw < 2 ^ rawBits := by
      simpa only [s, schemeOfCircuit, href.2.1] using hraw
    have hac : rawAccept raw = true := by
      rw [← scheme_accept_of_refinement encoder href raw hbound]
      exact hacc
    exact (mem_acceptedRawSet raw).mpr ⟨hbound,
      by simpa only [rawAccept, decide_eq_true_eq] using hac⟩
  · intro h
    obtain ⟨hbound, hfields⟩ := (mem_acceptedRawSet raw).mp h
    apply List.mem_toFinset.mpr
    apply (scheme_mem_accepted s raw).mpr
    refine ⟨?_, ?_⟩
    · simpa only [s, schemeOfCircuit, href.2.1] using hbound
    · rw [scheme_accept_of_refinement encoder href raw hbound]
      simpa only [rawAccept, decide_eq_true_eq] using hfields

theorem accepted_count_of_refinement (encoder : Circuit)
    (href : CircuitRefines encoder) :
    (schemeOfCircuit encoder).accepted.length = threshold * encodingCardinality := by
  rw [← List.toFinset_card_of_nodup (scheme_accepted_nodup _),
    accepted_toFinset_of_refinement encoder href, acceptedRawSet_card]

theorem tau_of_refinement (encoder : Circuit) (href : CircuitRefines encoder) :
    (schemeOfCircuit encoder).tau = acceptanceRatio := by
  change ((schemeOfCircuit encoder).accepted.length : ℚ) /
    ((2 ^ encoder.inputs : Nat) : ℚ) = acceptanceRatio
  rw [accepted_count_of_refinement encoder href, href.2.1]
  rfl

end PoissonDAG.GRSCC
