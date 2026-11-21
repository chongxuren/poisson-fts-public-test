import PoissonDAG.Constructions.GRSCC.Covering
import PoissonDAG.Constructions.GRSCC.Kernel
import PoissonDAG.Constructions.GRSCC.EdgeGeometry

set_option maxHeartbeats 20000
set_option maxRecDepth 1000

/-!
# Actual protected-closure supplier necessity

This module isolates the bounded geometric classifications and the addressed
route/barrier proofs from the generic finite counting recurrence in `Kernel`.
It exports no scalar covering bound.
-/

namespace PoissonDAG.GRSCC

/-- Relative vertex identities in a layer. The six points need not satisfy a
sum condition for these purely geometric necessity lemmas. -/
def localLayerDisclosure (slot : Slot) (point : CodePosition → Fin 9) : List Nat :=
  (slot.val * 10 + (point guardPosition).val) ::
    (List.finRange 5).map (fun depth => localAuthOpening slot depth (point (depthPosition depth)))

def Route.openingPoint (r : Route) (layer : Layer) (position : CodePosition) : Fin 9 :=
  ⟨8 - ((r.code layer).depth position).val, by omega⟩

theorem Route.layerDisclosure_translate (r : Route) (layer : Layer) :
    r.layerDisclosure layer =
      (localLayerDisclosure (r.slot layer) (r.openingPoint layer)).map (fun i =>
        ownerBase r.bucket.val layer.val (r.owner layer) + i) := by
  simp only [Route.layerDisclosure, localLayerDisclosure, List.map_cons, List.map_map]
  refine congrArg₂ List.cons ?_ ?_
  · simp [Route.openingPoint, guardPosition, Nat.add_assoc]
  · apply List.map_congr_left
    intro depth _
    let level : Depth := ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
    have ht := edgePointVertex_translate (r.ownerAddress layer) level
      (((r.slot layer).val / 2 ^ level.val) ^^^ 1)
      (r.openingPoint layer (depthPosition depth))
    simpa only [Route.ownerAddress, Route.openingPoint, localAuthOpening,
      depthPosition, level, Fin.val_mk, edgePointVertex, Function.comp_apply] using ht

theorem localLayerDisclosure_bound (slot : Slot) (point : CodePosition → Fin 9)
    (i : Nat) (hi : i ∈ localLayerDisclosure slot point) : i < 847 := by
  rcases List.mem_cons.mp hi with rfl | hi
  · have hs := slot.isLt
    have hp := (point guardPosition).isLt
    omega
  · obtain ⟨depth, _, rfl⟩ := List.mem_map.mp hi
    have h := edgePointVertex_in_owner localOwner
      ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
      (((slot.val / 2 ^ (4 - depth.val))) ^^^ 1) (sibling_child_bound slot depth)
      (point (depthPosition depth))
    simpa [localOwner, ownerBase, localAuthOpening] using h.2

theorem Route.layerDisclosure_in_owner (r : Route) (layer : Layer) (i : Nat)
    (hi : i ∈ r.layerDisclosure layer) : InOwner (r.ownerAddress layer) i := by
  rw [r.layerDisclosure_translate] at hi
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hi
  have hbound := localLayerDisclosure_bound (r.slot layer) (r.openingPoint layer) offset hoffset
  dsimp [InOwner, Route.ownerAddress]
  omega

theorem layer_disclosure_hit_local (a : OwnerAddress) (history : Route) (layer : Layer)
    (barrier localBarrier : Nat → Prop)
    (hrange : ∀ i, barrier i → InOwner a i)
    (htranslate : ∀ i, barrier (ownerBase a.bucket.val a.layer.val a.owner.val + i) ↔
      localBarrier i)
    (hhit : ∃ i ∈ history.layerDisclosure layer, barrier i) :
    a.bucket.val = history.bucket.val ∧ a.layer.val = layer.val ∧
      a.owner.val = history.owner layer ∧
      ∃ i ∈ localLayerDisclosure (history.slot layer) (history.openingPoint layer),
        localBarrier i := by
  obtain ⟨i, hmem, hbar⟩ := hhit
  have howners := owner_intervals_disjoint a (history.ownerAddress layer) i
    (hrange i hbar) (history.layerDisclosure_in_owner layer i hmem)
  change a.bucket.val = history.bucket.val ∧ a.layer.val = layer.val ∧
    a.owner.val = history.owner layer at howners
  obtain ⟨hbucket, hlayer, howner⟩ := howners
  rw [history.layerDisclosure_translate] at hmem
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hmem
  refine ⟨hbucket, hlayer, howner, offset, hoffset, ?_⟩
  apply (htranslate offset).mp
  simpa only [hbucket, hlayer, howner] using hbar

private theorem supplier_interval_offset (base i : Nat)
    (hi : base ≤ i ∧ i < base + 847) :
    i - base < 847 ∧ base + (i - base) = i := by omega

private theorem inOwner_private_fields (a : OwnerAddress) (i : Nat) (hi : InOwner a i) :
    i < 2629104 ∧ i % 164319 < 164318 := by
  have hoff := supplier_interval_offset _ i hi
  let offset : Fin 847 := ⟨i - ownerBase a.bucket.val a.layer.val a.owner.val, hoff.1⟩
  have heq : ownerBase a.bucket.val a.layer.val a.owner.val + offset.val = i := hoff.2
  have hf := ownerIndex_fields a offset
  change (ownerBase a.bucket.val a.layer.val a.owner.val + offset.val < 2629104) ∧ _ at hf
  simp only [heq] at hf
  exact ⟨hf.1, hf.2.2.1⟩

theorem childRoot_not_in_owner (a : OwnerAddress) (bucket : Nat) :
    ¬InOwner a (childRoot bucket) := by
  intro hi
  have hlocal := (inOwner_private_fields a (childRoot bucket) hi).2
  simpa [childRoot, Nat.add_mod, Nat.mul_mod] using hlocal

theorem bucketJoin_not_in_owner (a : OwnerAddress) (level : Fin 4) (position : Nat) :
    ¬InOwner a (bucketJoin level.val position) := by
  intro hi
  have hbound := (inOwner_private_fields a (bucketJoin level.val position) hi).1
  fin_cases level <;> norm_num [bucketJoin, bucketLevelBase] at hbound <;> omega

theorem bucketTreeChild_not_in_owner (a : OwnerAddress) (level : Fin 4) (position : Nat) :
    ¬InOwner a (bucketTreeChild level.val position) := by
  unfold bucketTreeChild
  split
  · exact childRoot_not_in_owner a position
  · have hl := level.isLt
    exact bucketJoin_not_in_owner a ⟨level.val - 1, by omega⟩ position

theorem bucketSiblings_not_in_owner (a : OwnerAddress) (history : Route) (i : Nat)
    (hi : i ∈ history.bucketSiblings) : ¬InOwner a i := by
  obtain ⟨level, hlevel, rfl⟩ := List.mem_map.mp hi
  exact bucketTreeChild_not_in_owner a ⟨level, List.mem_range.mp hlevel⟩ _

theorem initial_sibling_bound : ∀ owner : Fin 2, (owner.val ^^^ 1) < 2 := by
  decide +kernel

def Route.initialSiblingOwner (r : Route) : OwnerAddress where
  bucket := r.bucket
  layer := ⟨6, by decide⟩
  owner := ⟨r.initialOwner.val ^^^ 1, by
    simpa [ownerCount] using initial_sibling_bound r.initialOwner⟩

theorem initialSibling_in_owner (history : Route) :
    InOwner history.initialSiblingOwner history.initialSibling := by
  dsimp [InOwner, Route.initialSiblingOwner, Route.initialSibling, ownerRoot]
  omega

theorem route_disclosure_hit_in_layer (a : OwnerAddress) (history : Route)
    (barrier : Nat → Prop) (hrange : ∀ i, barrier i → InOwner a i)
    (hroot : ¬barrier (ownerRoot a.bucket.val a.layer.val a.owner.val))
    (hhit : ∃ i ∈ history.disclosure, barrier i) :
    ∃ layer : Layer, ∃ i ∈ history.layerDisclosure layer, barrier i := by
  obtain ⟨i, hmem, hbar⟩ := hhit
  simp only [Route.disclosure, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with (hbucket | hinitial) | hlayer
  · exact False.elim ((bucketSiblings_not_in_owner a history i hbucket) (hrange i hbar))
  · subst i
    have howners := owner_intervals_disjoint a history.initialSiblingOwner
      history.initialSibling (hrange _ hbar) (initialSibling_in_owner history)
    change a.bucket.val = history.bucket.val ∧ a.layer.val = 6 ∧
      a.owner.val = (history.initialOwner.val ^^^ 1) at howners
    obtain ⟨hbucket, hlayer, howner⟩ := howners
    have heq : history.initialSibling = ownerRoot a.bucket.val a.layer.val a.owner.val := by
      simp only [Route.initialSibling, hbucket, hlayer, howner]
    exact False.elim (hroot (heq ▸ hbar))
  · obtain ⟨layer, _, hi⟩ := List.mem_flatMap.mp hlayer
    exact ⟨layer, i, hi, hbar⟩

theorem local_layer_guard_classification (target history : Slot) (targetPoint : Fin 9)
    (point : CodePosition → Fin 9) :
    (∃ i ∈ localLayerDisclosure history point, guardPrefix localOwner target targetPoint i) ↔
      target = history ∧ (point guardPosition).val ≤ targetPoint.val := by
  constructor
  · rintro ⟨i, hmem, hbar⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact (local_guard_prefix_classification target history targetPoint _).mp hbar
    · obtain ⟨depth, _, rfl⟩ := List.mem_map.mp hmem
      exact False.elim ((local_guard_authentication_disjoint target history targetPoint depth _) hbar)
  · intro h
    refine ⟨_, List.mem_cons_self, ?_⟩
    exact (local_guard_prefix_classification target history targetPoint _).mpr h

/-- Every local barrier hit supplies the corresponding source-law requirement.
This implication is sufficient for a sound upper bound on full pooled closure. -/
theorem local_layer_edge_necessity (target history : Slot) (depth : Depth)
    (targetPoint : Fin 9) (point : CodePosition → Fin 9)
    (hhit : ∃ i ∈ localLayerDisclosure history point,
      localSiblingBarrier target depth targetPoint i) :
    divergesAt target history depth = true ∨
      (history.val / 2 ^ (4 - depth.val) = target.val / 2 ^ (4 - depth.val) ∧
        (point (depthPosition depth)).val ≤ targetPoint.val) := by
  obtain ⟨i, hmem, hbar⟩ := hhit
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact Or.inl ((local_edge_guard_classification target history depth targetPoint _).mp hbar)
  · obtain ⟨historyDepth, _, rfl⟩ := List.mem_map.mp hmem
    rcases local_edge_authentication_classification target history depth historyDepth
        targetPoint _ hbar with hdiv | ⟨heq, hprefix, hpoint⟩
    · exact Or.inl hdiv
    · subst historyDepth
      exact Or.inr ⟨hprefix, hpoint⟩

def Route.guardBarrier (r : Route) (layer : Layer) : Nat → Prop :=
  guardPrefix (r.ownerAddress layer) (r.slot layer) (r.openingPoint layer guardPosition)

def Route.siblingBarrier (r : Route) (layer : Layer) (depth : Depth) : Nat → Prop :=
  let level : Depth := ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
  privateEdgeBarrier (r.ownerAddress layer) level
    (((r.slot layer).val / 2 ^ level.val) ^^^ 1)
    (r.openingPoint layer (depthPosition depth))

theorem Route.guardBarrier_in_owner (r : Route) (layer : Layer) (i : Nat)
    (hi : r.guardBarrier layer i) : InOwner (r.ownerAddress layer) i :=
  guardPrefix_in_owner _ _ _ i hi

theorem Route.siblingBarrier_in_owner (r : Route) (layer : Layer) (depth : Depth) (i : Nat)
    (hi : r.siblingBarrier layer depth i) : InOwner (r.ownerAddress layer) i := by
  exact privateEdgeBarrier_in_owner _ _ _ _ (sibling_child_bound (r.slot layer) depth) i hi

theorem Route.guardBarrier_excludes_ownerRoot (r : Route) (layer : Layer) :
    ¬r.guardBarrier layer (ownerRoot r.bucket.val layer.val (r.owner layer)) := by
  have hs := (r.slot layer).isLt
  have hp := (r.openingPoint layer guardPosition).isLt
  dsimp [Route.guardBarrier, guardPrefix, guardStart, ownerRoot, Route.ownerAddress]
  omega

theorem Route.siblingBarrier_excludes_ownerRoot (r : Route) (layer : Layer) (depth : Depth) :
    ¬r.siblingBarrier layer depth (ownerRoot r.bucket.val layer.val (r.owner layer)) := by
  intro hhit
  have hbound := privateEdgeBarrier_below_ownerRoot (r.ownerAddress layer)
    ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
    (((r.slot layer).val / 2 ^ (4 - depth.val)) ^^^ 1)
    (r.openingPoint layer (depthPosition depth))
    (sibling_child_bound (r.slot layer) depth) _ hhit
  dsimp [Route.ownerAddress, ownerRoot] at hbound
  omega

/-- Classification of a real history's private guard-prefix hit. Outer
authentication values and all other owner/layer disclosures are ruled out. -/
theorem route_guard_disclosure_necessity (target history : Route) (layer : Layer)
    (hhit : ∃ i ∈ history.disclosure, target.guardBarrier layer i) :
    target.bucket.val = history.bucket.val ∧ target.owner layer = history.owner layer ∧
      target.slot layer = history.slot layer ∧
      ((target.code layer).depth guardPosition).val ≤
        ((history.code layer).depth guardPosition).val := by
  obtain ⟨historyLayer, i, hmem, hbar⟩ := route_disclosure_hit_in_layer
    (target.ownerAddress layer) history (target.guardBarrier layer)
    (target.guardBarrier_in_owner layer) (target.guardBarrier_excludes_ownerRoot layer) hhit
  have hlocal := layer_disclosure_hit_local (target.ownerAddress layer) history historyLayer
    (target.guardBarrier layer)
    (guardPrefix localOwner (target.slot layer) (target.openingPoint layer guardPosition))
    (target.guardBarrier_in_owner layer)
    (fun j => guardPrefix_translate (target.ownerAddress layer) _ _ j)
    ⟨i, hmem, hbar⟩
  change target.bucket.val = history.bucket.val ∧ layer.val = historyLayer.val ∧
    target.owner layer = history.owner historyLayer ∧ _ at hlocal
  obtain ⟨hbucket, hlayer, howner, hlocal⟩ := hlocal
  have heq : historyLayer = layer := Fin.ext hlayer.symm
  subst historyLayer
  obtain ⟨hslot, hpoint⟩ := (local_layer_guard_classification _ _ _ _).mp hlocal
  refine ⟨hbucket, howner, hslot, ?_⟩
  have he := ((target.code layer).depth guardPosition).isLt
  have hf := ((history.code layer).depth guardPosition).isLt
  dsimp [Route.openingPoint] at hpoint
  omega

/-- Full addressed history disclosure hits give exactly the owner/slot-depth
supplier alternatives used by the local avoidance upper bound. -/
theorem route_edge_disclosure_necessity (target history : Route) (layer : Layer) (depth : Depth)
    (hhit : ∃ i ∈ history.disclosure, target.siblingBarrier layer depth i) :
    target.bucket.val = history.bucket.val ∧ target.owner layer = history.owner layer ∧
      (divergesAt (target.slot layer) (history.slot layer) depth = true ∨
        ((history.slot layer).val / 2 ^ (4 - depth.val) =
            (target.slot layer).val / 2 ^ (4 - depth.val) ∧
          ((target.code layer).depth (depthPosition depth)).val ≤
            ((history.code layer).depth (depthPosition depth)).val)) := by
  obtain ⟨historyLayer, i, hmem, hbar⟩ := route_disclosure_hit_in_layer
    (target.ownerAddress layer) history (target.siblingBarrier layer depth)
    (target.siblingBarrier_in_owner layer depth)
    (target.siblingBarrier_excludes_ownerRoot layer depth) hhit
  have hlocal := layer_disclosure_hit_local (target.ownerAddress layer) history historyLayer
    (target.siblingBarrier layer depth)
    (localSiblingBarrier (target.slot layer) depth (target.openingPoint layer (depthPosition depth)))
    (target.siblingBarrier_in_owner layer depth)
    (fun j => privateEdgeBarrier_translate (target.ownerAddress layer)
      ⟨4 - depth.val, by have hd := depth.isLt; omega⟩ _ _ j)
    ⟨i, hmem, hbar⟩
  change target.bucket.val = history.bucket.val ∧ layer.val = historyLayer.val ∧
    target.owner layer = history.owner historyLayer ∧ _ at hlocal
  obtain ⟨hbucket, hlayer, howner, hlocal⟩ := hlocal
  have heq : historyLayer = layer := Fin.ext hlayer.symm
  subst historyLayer
  refine ⟨hbucket, howner, ?_⟩
  rcases local_layer_edge_necessity _ _ depth _ _ hlocal with hdiv | ⟨hprefix, hpoint⟩
  · exact Or.inl hdiv
  · refine Or.inr ⟨hprefix, ?_⟩
    have he := ((target.code layer).depth (depthPosition depth)).isLt
    have hf := ((history.code layer).depth (depthPosition depth)).isLt
    dsimp [Route.openingPoint] at hpoint
    omega

theorem route_frontier_get (r : Route) (i : Nat) (hi : i < graphNodes) :
    get r.frontier i = decide (i ∈ r.disclosure) := by
  exact frontier_get r i hi

theorem layer_mem_disclosure (r : Route) (layer : Layer) (i : Nat)
    (hi : i ∈ r.layerDisclosure layer) : i ∈ r.disclosure := by
  simp only [Route.disclosure, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨layer, by simp, hi⟩)

theorem route_guard_mem (r : Route) (layer : Layer) :
    guardVertex (r.ownerAddress layer) (r.slot layer) (r.openingPoint layer guardPosition) ∈
      r.disclosure := by
  apply layer_mem_disclosure r layer
  simp [Route.layerDisclosure, guardVertex, Route.ownerAddress, Route.openingPoint,
    guardPosition]

theorem route_edge_mem (r : Route) (layer : Layer) (depth : Depth) :
    edgePointVertex r.bucket.val layer.val (r.owner layer) (4 - depth.val)
      (((r.slot layer).val / 2 ^ (4 - depth.val)) ^^^ 1)
      (r.openingPoint layer (depthPosition depth)).val ∈ r.disclosure := by
  apply layer_mem_disclosure r layer
  simp only [Route.layerDisclosure, List.mem_cons, List.mem_map]
  refine Or.inr ⟨depth, by simp, ?_⟩
  rfl

/-- Full protected closure to a real route's guard supplier. The hypotheses
are the literal graph/circuit refinement facts, to be discharged for the
constructed Scheme; no covering bound is among the premises. -/
theorem covered_guard_supplier (s : Scheme) (hs : List Nat) (target : Nat)
    (route : Nat → Route) (layer : Layer)
    (hgraph : s.graph = graph)
    (houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (htarget : s.frontier target = (route target).frontier)
    (hhistory : ∀ raw ∈ hs, s.frontier raw = (route raw).frontier)
    (hcovered : s.covered hs target = true) :
    ∃ raw ∈ hs, (route target).bucket.val = (route raw).bucket.val ∧
      (route target).owner layer = (route raw).owner layer ∧
      (route target).slot layer = (route raw).slot layer ∧
      (((route target).code layer).depth guardPosition).val ≤
        (((route raw).code layer).depth guardPosition).val := by
  let r := route target
  let a := r.ownerAddress layer
  let point := r.openingPoint layer guardPosition
  let vertex := guardVertex a (r.slot layer) point
  have hv : vertex < graphNodes := guardVertex_lt a (r.slot layer) point
  have ht : get (s.frontier target) vertex = true := by
    rw [htarget, route_frontier_get _ _ hv]
    exact decide_eq_true (route_guard_mem r layer)
  obtain ⟨raw, hraw, i, hbar, hfront⟩ := covered_guard_requires_private_disclosure
    s hs target a (r.slot layer) point hgraph houtputs ht hcovered
  have hibound : i < graphNodes := by
    have h := (guardPrefix_in_owner a (r.slot layer) point i hbar).lt_graph
    simpa only [graph_length, fixed_geometry.2.2.2.1] using h
  rw [hhistory raw hraw, route_frontier_get _ _ hibound] at hfront
  have hmem : i ∈ (route raw).disclosure := of_decide_eq_true hfront
  refine ⟨raw, hraw, ?_⟩
  exact route_guard_disclosure_necessity r (route raw) layer ⟨i, hmem, hbar⟩

/-- Full protected closure to the actual same-owner supplier alternatives
for an internal authentication requirement, retaining pooled joins. -/
theorem covered_edge_supplier (s : Scheme) (hs : List Nat) (target : Nat)
    (route : Nat → Route) (layer : Layer) (depth : Depth)
    (hgraph : s.graph = graph)
    (houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (htarget : s.frontier target = (route target).frontier)
    (hhistory : ∀ raw ∈ hs, s.frontier raw = (route raw).frontier)
    (hcovered : s.covered hs target = true) :
    ∃ raw ∈ hs, (route target).bucket.val = (route raw).bucket.val ∧
      (route target).owner layer = (route raw).owner layer ∧
      (divergesAt ((route target).slot layer) ((route raw).slot layer) depth = true ∨
        (((route raw).slot layer).val / 2 ^ (4 - depth.val) =
            ((route target).slot layer).val / 2 ^ (4 - depth.val) ∧
          (((route target).code layer).depth (depthPosition depth)).val ≤
            (((route raw).code layer).depth (depthPosition depth)).val)) := by
  let r := route target
  let a := r.ownerAddress layer
  let level : Depth := ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
  let child := ((r.slot layer).val / 2 ^ level.val) ^^^ 1
  let point := r.openingPoint layer (depthPosition depth)
  let vertex := edgePointVertex a.bucket.val a.layer.val a.owner.val level.val child point.val
  have hchild : child < 2 ^ (5 - level.val) := sibling_child_bound (r.slot layer) depth
  have hv : vertex < graphNodes := by
    have h := (edgePointVertex_in_owner a level child hchild point).2
    have hb := a.bucket.isLt
    have hn := a.ownerNumber_lt
    rw [fixed_geometry.2.2.2.1]
    dsimp [ownerBase] at h
    omega
  have ht : get (s.frontier target) vertex = true := by
    rw [htarget, route_frontier_get _ _ hv]
    exact decide_eq_true (route_edge_mem r layer depth)
  obtain ⟨raw, hraw, i, hbar, hfront⟩ := covered_edge_requires_private_disclosure
    s hs target a level child point hchild hgraph houtputs ht hcovered
  have hibound : i < graphNodes := by
    have h := (privateEdgeBarrier_in_owner a level child point hchild i hbar).lt_graph
    simpa only [graph_length, fixed_geometry.2.2.2.1] using h
  rw [hhistory raw hraw, route_frontier_get _ _ hibound] at hfront
  have hmem : i ∈ (route raw).disclosure := of_decide_eq_true hfront
  refine ⟨raw, hraw, ?_⟩
  exact route_edge_disclosure_necessity r (route raw) layer depth ⟨i, hmem, hbar⟩

end PoissonDAG.GRSCC
