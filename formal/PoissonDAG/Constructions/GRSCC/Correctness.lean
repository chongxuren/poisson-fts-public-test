import PoissonDAG.Constructions.GRSCC.Encoding

/-!
# Honest reconstruction obligations

`Route.recovery` explicitly lists the operations to execute.  The length
theorems count operations from that list and the codeword's ordinary sum.
`root_reconstructs` supplies an allowed finite derivation from the actual
disclosures. Restricted-plan completeness connects this derivation to the
protected `PoissonDAG.close`; its executed-call bound can skip disclosed nodes.
-/
namespace PoissonDAG.GRSCC

set_option maxHeartbeats 20000

theorem Codeword.depth_sum_explicit (c : Codeword) :
    (c.depth ⟨0, by decide⟩).val +
      (c.depth ⟨1, by decide⟩).val +
      (c.depth ⟨2, by decide⟩).val +
      (c.depth ⟨3, by decide⟩).val +
      (c.depth ⟨4, by decide⟩).val +
      (c.depth ⟨5, by decide⟩).val = 16 := by
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using c.sum_eq

theorem layerWork_length (r : Route) (layer : Layer) :
    (r.layerWork layer).length = 62 := by
  have h := (r.code layer).depth_sum_explicit
  change ((r.code layer).depth (0 : CodePosition)).val +
    ((r.code layer).depth (1 : CodePosition)).val +
    ((r.code layer).depth (2 : CodePosition)).val +
    ((r.code layer).depth (3 : CodePosition)).val +
    ((r.code layer).depth (4 : CodePosition)).val +
    ((r.code layer).depth (5 : CodePosition)).val = 16 at h
  simp [Route.layerWork, Route.guardWork, Route.levelWork,
    List.finRange_succ, List.length_flatMap]
  omega

theorem recovery_length (r : Route) : r.recovery.length = 439 := by
  simp [Route.recovery, List.length_flatMap, layerWork_length,
    List.finRange_succ]

theorem root_mem_recovery (r : Route) : graphNodes - 1 ∈ r.recovery := by
  have hb := r.bucket.isLt
  have hdiv : r.bucket.val / 16 = 0 := by omega
  have heq : bucketJoin 3 (r.bucket.val / 2 ^ (3 + 1)) = graphNodes - 1 := by
    rw [fixed_geometry.2.2.2.1]
    norm_num [bucketJoin, bucketLevelBase, hdiv]
  have hmem : graphNodes - 1 ∈
      (List.range 4).map (fun level =>
        bucketJoin level (r.bucket.val / 2 ^ (level + 1))) := by
    exact List.mem_map.mpr ⟨3, by decide, heq⟩
  simp only [Route.recovery, List.mem_append]
  tauto

/-- Finite proof trees using precisely the disclosed labels and permitted
operations. Sources have no inference rule. -/
inductive Route.Reconstructs (r : Route) : Nat → Prop
  | disclosed {i} : i ∈ r.disclosure → r.Reconstructs i
  | unary {i p} : i ∈ r.recovery → graphNode i = .unary p →
      r.Reconstructs p → r.Reconstructs i
  | binary {i l right} : i ∈ r.recovery → graphNode i = .binary l right →
      r.Reconstructs l → r.Reconstructs right → r.Reconstructs i

def Route.guardOpeningPoint (r : Route) (layer : Layer) : Fin 9 :=
  ⟨8 - ((r.code layer).depth ⟨5, by decide⟩).val, by omega⟩

theorem guardOpening_mem_disclosure (r : Route) (layer : Layer) :
    guardVertex (r.ownerAddress layer) (r.slot layer) (r.guardOpeningPoint layer) ∈
      r.disclosure := by
  simp only [Route.disclosure, List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨layer, List.mem_finRange _, ?_⟩
  simp [Route.layerDisclosure, guardVertex, Route.ownerAddress,
    Route.guardOpeningPoint]

theorem guardWork_mem_recovery (r : Route) (layer : Layer) (i : Nat)
    (hi : i ∈ r.guardWork layer) : i ∈ r.recovery := by
  simp only [Route.recovery, List.mem_append]
  left
  left
  apply List.mem_flatMap.mpr
  refine ⟨layer, List.mem_finRange _, ?_⟩
  exact List.mem_append_left _ hi

theorem guardStep_mem_recovery (r : Route) (layer : Layer) (point : Fin 9)
    (hpoint : (r.guardOpeningPoint layer).val < point.val) :
    guardVertex (r.ownerAddress layer) (r.slot layer) point ∈ r.recovery := by
  apply guardWork_mem_recovery r layer
  unfold Route.guardWork
  apply List.mem_map.mpr
  let e := ((r.code layer).depth ⟨5, by decide⟩).val
  have he : e < 9 := ((r.code layer).depth ⟨5, by decide⟩).isLt
  have hp := point.isLt
  have hstart : 9 - e ≤ point.val := by
    change 8 - e < point.val at hpoint
    omega
  refine ⟨point.val - (9 - e), List.mem_range.mpr (by omega), ?_⟩
  change ownerBase r.bucket.val layer.val (r.owner layer) + (r.slot layer).val * 10 +
    (9 - e + (point.val - (9 - e))) =
      ownerBase r.bucket.val layer.val (r.owner layer) + (r.slot layer).val * 10 + point.val
  omega

theorem guard_suffix_reconstructs (r : Route) (layer : Layer) (point : Fin 9)
    (hpoint : (r.guardOpeningPoint layer).val ≤ point.val) :
    r.Reconstructs (guardVertex (r.ownerAddress layer) (r.slot layer) point) := by
  revert hpoint
  induction point using Fin.induction with
  | zero =>
      intro hpoint
      have heq : (0 : Fin 9) = r.guardOpeningPoint layer := Fin.ext (by omega)
      rw [heq]
      exact .disclosed (guardOpening_mem_disclosure r layer)
  | succ previous ih =>
      intro hpoint
      by_cases heq : previous.succ = r.guardOpeningPoint layer
      · rw [heq]
        exact .disclosed (guardOpening_mem_disclosure r layer)
      have hneq : previous.succ.val ≠ (r.guardOpeningPoint layer).val := by
        exact fun h => heq (Fin.ext h)
      have hstrict : (r.guardOpeningPoint layer).val < previous.succ.val := by omega
      have hprev : (r.guardOpeningPoint layer).val ≤ previous.castSucc.val := by
        simp only [Fin.val_succ, Fin.val_castSucc] at *
        omega
      have hind := ih hprev
      have hnode := graphNode_guard (r.ownerAddress layer) (r.slot layer) previous.succ
      rw [if_neg (by simp : ¬previous.succ.val = 0)] at hnode
      have hparent : guardVertex (r.ownerAddress layer) (r.slot layer) previous.succ - 1 =
          guardVertex (r.ownerAddress layer) (r.slot layer) previous.castSucc := by
        dsimp [guardVertex] <;> omega
      rw [hparent] at hnode
      exact .unary (guardStep_mem_recovery r layer previous.succ hstrict) hnode hind

theorem edge_suffix_reconstructs (r : Route) (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (hchildPosition : childPosition < 2 ^ (5 - level.val))
    (start finish : Fin 9) (horder : start.val ≤ finish.val)
    (hstart : r.Reconstructs (edgePointVertex a.bucket.val a.layer.val a.owner.val
      level.val childPosition start.val))
    (hwork : ∀ point : Fin 9, start.val < point.val → point.val ≤ finish.val →
      edgePointVertex a.bucket.val a.layer.val a.owner.val level.val
        childPosition point.val ∈ r.recovery) :
    r.Reconstructs (edgePointVertex a.bucket.val a.layer.val a.owner.val
      level.val childPosition finish.val) := by
  revert horder hwork
  induction finish using Fin.induction with
  | zero =>
      intro horder hwork
      have hz : start.val = 0 := by omega
      simpa only [hz, Fin.val_zero] using hstart
  | succ previous ih =>
      intro horder hwork
      by_cases heq : start.val = previous.succ.val
      · simpa only [heq] using hstart
      have hstrict : start.val < previous.succ.val := by omega
      have hprev : start.val ≤ previous.castSucc.val := by
        simp only [Fin.val_succ, Fin.val_castSucc] at *
        omega
      have hind := ih hprev (fun point hs hp => hwork point hs (by
        simp only [Fin.val_succ, Fin.val_castSucc] at *
        omega))
      have hnode := graphNode_edge_suffix a level childPosition hchildPosition
        previous.succ (by simp)
      have hprevious : previous.succ.val - 1 = previous.castSucc.val := by
        simp
      rw [hprevious] at hnode
      exact .unary (hwork _ hstrict le_rfl) hnode hind

theorem levelWork_mem_recovery (r : Route) (layer : Layer) (level : Depth) (i : Nat)
    (hi : i ∈ r.levelWork layer level) : i ∈ r.recovery := by
  simp only [Route.recovery, List.mem_append]
  left
  left
  apply List.mem_flatMap.mpr
  refine ⟨layer, List.mem_finRange _, ?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨level, List.mem_finRange _, hi⟩

theorem selectedEdge_mem_recovery (r : Route) (layer : Layer) (level : Depth)
    (point : Fin 9) (hp : 0 < point.val) :
    edgePointVertex r.bucket.val layer.val (r.owner layer) level.val
      ((r.slot layer).val / 2 ^ level.val) point.val ∈ r.recovery := by
  apply levelWork_mem_recovery r layer level
  unfold Route.levelWork
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨point.val - 1, List.mem_range.mpr (by have := point.isLt; omega), ?_⟩
  congr 1
  omega

theorem siblingEdge_mem_recovery (r : Route) (layer : Layer) (level : Depth)
    (point : Fin 9)
    (hp : 8 - ((r.code layer).depth ⟨4 - level.val, by omega⟩).val < point.val) :
    edgePointVertex r.bucket.val layer.val (r.owner layer) level.val
      (((r.slot layer).val / 2 ^ level.val) ^^^ 1) point.val ∈ r.recovery := by
  apply levelWork_mem_recovery r layer level
  unfold Route.levelWork
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_map.mpr
  let e := ((r.code layer).depth ⟨4 - level.val, by omega⟩).val
  have he : e < 9 := ((r.code layer).depth ⟨4 - level.val, by omega⟩).isLt
  have hpoint := point.isLt
  have hlow : 9 - e ≤ point.val := by dsimp [e]; omega
  refine ⟨point.val - (9 - e), List.mem_range.mpr (by omega), ?_⟩
  congr 1
  dsimp [e] at *
  omega

theorem selectedJoin_mem_recovery (r : Route) (layer : Layer) (level : Depth) :
    treeJoin r.bucket.val layer.val (r.owner layer) level.val
      (((r.slot layer).val / 2 ^ level.val) / 2) ∈ r.recovery := by
  apply levelWork_mem_recovery r layer level
  unfold Route.levelWork
  apply List.mem_append_right
  simp

theorem siblingOpening_mem_disclosure (r : Route) (layer : Layer) (level : Depth) :
    edgePointVertex r.bucket.val layer.val (r.owner layer) level.val
      (((r.slot layer).val / 2 ^ level.val) ^^^ 1)
      (8 - ((r.code layer).depth ⟨4 - level.val, by omega⟩).val) ∈
        r.disclosure := by
  simp only [Route.disclosure, List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨layer, List.mem_finRange _, ?_⟩
  simp only [Route.layerDisclosure, List.mem_cons]
  right
  apply List.mem_map.mpr
  let depth : Depth := ⟨4 - level.val, by omega⟩
  refine ⟨depth, List.mem_finRange _, ?_⟩
  have hlevel : 4 - depth.val = level.val := by dsimp [depth]; omega
  simp only [hlevel]
  rfl

theorem route_child_position_bound (r : Route) (layer : Layer) (level : Depth) :
    (r.slot layer).val / 2 ^ level.val < 2 ^ (5 - level.val) := by
  have hs := (r.slot layer).isLt
  fin_cases level <;> norm_num at * <;> omega

theorem route_sibling_position_bound (r : Route) (layer : Layer) (level : Depth) :
    (((r.slot layer).val / 2 ^ level.val) ^^^ 1) < 2 ^ (5 - level.val) := by
  have h := route_child_position_bound r layer level
  have hhalf := sibling_div_two ((r.slot layer).val / 2 ^ level.val)
  have hmod : ((((r.slot layer).val / 2 ^ level.val) ^^^ 1) % 2) < 2 :=
    Nat.mod_lt _ (by decide)
  fin_cases level <;> norm_num at * <;> omega

theorem selectedEdge_endpoint_reconstructs (r : Route) (layer : Layer) (level : Depth)
    (hchild : r.Reconstructs (treeChild r.bucket.val layer.val (r.owner layer)
      level.val ((r.slot layer).val / 2 ^ level.val))) :
    r.Reconstructs (edgePointVertex r.bucket.val layer.val (r.owner layer)
      level.val ((r.slot layer).val / 2 ^ level.val) 8) := by
  apply edge_suffix_reconstructs r (r.ownerAddress layer) level
    ((r.slot layer).val / 2 ^ level.val) (route_child_position_bound r layer level)
    ⟨0, by decide⟩ ⟨8, by decide⟩ (by decide)
  · simpa [edgePointVertex, Route.ownerAddress] using hchild
  · intro point hp hlast
    exact selectedEdge_mem_recovery r layer level point hp

theorem siblingEdge_endpoint_reconstructs (r : Route) (layer : Layer) (level : Depth) :
    r.Reconstructs (edgePointVertex r.bucket.val layer.val (r.owner layer)
      level.val (((r.slot layer).val / 2 ^ level.val) ^^^ 1) 8) := by
  let opening : Fin 9 :=
    ⟨8 - ((r.code layer).depth ⟨4 - level.val, by omega⟩).val, by omega⟩
  apply edge_suffix_reconstructs r (r.ownerAddress layer) level
    (((r.slot layer).val / 2 ^ level.val) ^^^ 1)
    (route_sibling_position_bound r layer level) opening ⟨8, by decide⟩ (by
      dsimp [opening]; omega)
  · exact .disclosed (siblingOpening_mem_disclosure r layer level)
  · intro point hp hlast
    exact siblingEdge_mem_recovery r layer level point hp

theorem level_join_reconstructs (r : Route) (layer : Layer) (level : Depth)
    (hchild : r.Reconstructs (treeChild r.bucket.val layer.val (r.owner layer)
      level.val ((r.slot layer).val / 2 ^ level.val))) :
    r.Reconstructs (treeJoin r.bucket.val layer.val (r.owner layer) level.val
      (((r.slot layer).val / 2 ^ level.val) / 2)) := by
  let child := (r.slot layer).val / 2 ^ level.val
  have hselected := selectedEdge_endpoint_reconstructs r layer level hchild
  have hsibling := siblingEdge_endpoint_reconstructs r layer level
  have hposition : child / 2 < 2 ^ (4 - level.val) := by
    have hc := route_child_position_bound r layer level
    fin_cases level <;> norm_num at * <;> dsimp [child] at * <;> omega
  have hnode := graphNode_treeJoin_endpoints (r.ownerAddress layer) level
    (child / 2) hposition
  simp only [Route.ownerAddress, Fin.val_mk] at hnode
  have hdiv := sibling_div_two child
  have hmod := sibling_mod_two child
  have hmodlt : child % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsiblingmodlt : (child ^^^ 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  apply Route.Reconstructs.binary (selectedJoin_mem_recovery r layer level) hnode
  · by_cases hside : child % 2 = 0
    · have hleft : 2 * (child / 2) = child := by omega
      simpa only [hleft, child] using hselected
    · have hleft : 2 * (child / 2) = child ^^^ 1 := by omega
      simpa only [hleft, child] using hsibling
  · by_cases hside : child % 2 = 0
    · have hright : 2 * (child / 2) + 1 = child ^^^ 1 := by omega
      simpa only [hright, child] using hsibling
    · have hright : 2 * (child / 2) + 1 = child := by omega
      simpa only [hright, child] using hselected

theorem leaf_mem_recovery (r : Route) (layer : Layer) :
    leafVertex r.bucket.val layer.val (r.owner layer) (r.slot layer).val ∈
      r.recovery := by
  apply guardWork_mem_recovery r layer
  unfold Route.guardWork
  apply List.mem_map.mpr
  let e := ((r.code layer).depth ⟨5, by decide⟩).val
  have he : e < 9 := ((r.code layer).depth ⟨5, by decide⟩).isLt
  refine ⟨e, List.mem_range.mpr (by omega), ?_⟩
  dsimp [e, leafVertex]
  omega

theorem leaf_reconstructs (r : Route) (layer : Layer)
    (hnext : layer.val ≠ 0 → r.Reconstructs
      (ownerRoot r.bucket.val (layer.val - 1) (r.slot layer).val)) :
    r.Reconstructs
      (leafVertex r.bucket.val layer.val (r.owner layer) (r.slot layer).val) := by
  have hguard := guard_suffix_reconstructs r layer ⟨8, by decide⟩ (by
    dsimp [Route.guardOpeningPoint]; omega)
  have hnode := graphNode_leaf (r.ownerAddress layer) (r.slot layer)
  simp only [Route.ownerAddress, Fin.val_mk] at hnode
  have hparent :
      leafVertex r.bucket.val layer.val (r.owner layer) (r.slot layer).val - 1 =
      guardVertex (r.ownerAddress layer) (r.slot layer) ⟨8, by decide⟩ := by
    dsimp [leafVertex, guardVertex, Route.ownerAddress] <;> omega
  change graphNode (leafVertex r.bucket.val layer.val (r.owner layer)
    (r.slot layer).val) = _ at hnode
  rw [hparent] at hnode
  by_cases hz : layer.val = 0
  · rw [if_pos hz] at hnode
    exact .unary (leaf_mem_recovery r layer) hnode hguard
  · rw [if_neg hz] at hnode
    exact .binary (leaf_mem_recovery r layer) hnode hguard (hnext hz)

theorem owner_root_reconstructs_of_leaf (r : Route) (layer : Layer)
    (hleaf : r.Reconstructs
      (leafVertex r.bucket.val layer.val (r.owner layer) (r.slot layer).val)) :
    r.Reconstructs (ownerRoot r.bucket.val layer.val (r.owner layer)) := by
  have hlevels : ∀ level : Depth, r.Reconstructs
      (treeJoin r.bucket.val layer.val (r.owner layer) level.val
        (((r.slot layer).val / 2 ^ level.val) / 2)) := by
    intro level
    induction level using Fin.induction with
    | zero =>
        apply level_join_reconstructs r layer 0
        simpa [treeChild] using hleaf
    | succ previous ih =>
        apply level_join_reconstructs r layer previous.succ
        simpa [treeChild, Nat.div_div_eq_div_mul, pow_succ] using ih
  have hlast := hlevels ⟨4, by decide⟩
  have hs := (r.slot layer).isLt
  have hpos : ((r.slot layer).val / 2 ^ 4) / 2 = 0 := by norm_num; omega
  rw [hpos] at hlast
  simpa [treeJoin, treeLevelBase, ownerRoot, Nat.add_assoc] using hlast

theorem all_route_owner_roots_reconstruct (r : Route) (layer : Layer) :
    r.Reconstructs (ownerRoot r.bucket.val layer.val (r.owner layer)) := by
  induction layer using Fin.induction with
  | zero =>
      apply owner_root_reconstructs_of_leaf
      apply leaf_reconstructs
      intro hzero
      exact False.elim (hzero rfl)
  | succ previous ih =>
      apply owner_root_reconstructs_of_leaf
      apply leaf_reconstructs
      intro hnonzero
      have howner : r.owner previous.castSucc = (r.slot previous.succ).val := by
        have hp := previous.isLt
        simp only [Route.owner, Fin.val_castSucc,
          dif_neg (by omega : ¬previous.val = 6)]
        rfl
      rw [howner] at ih
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel] using ih

theorem childRoot_mem_recovery (r : Route) : childRoot r.bucket.val ∈ r.recovery := by
  simp [Route.recovery]

theorem initialSibling_mem_disclosure (r : Route) : r.initialSibling ∈ r.disclosure := by
  simp [Route.disclosure]

theorem child_root_reconstructs (r : Route) : r.Reconstructs (childRoot r.bucket.val) := by
  have hselected := all_route_owner_roots_reconstruct r ⟨6, by decide⟩
  have hsibling : r.Reconstructs r.initialSibling :=
    .disclosed (initialSibling_mem_disclosure r)
  apply Route.Reconstructs.binary (childRoot_mem_recovery r) (graphNode_childRoot r.bucket)
  · by_cases hz : r.initialOwner.val = 0
    · simpa [Route.owner, hz] using hselected
    · have hone : r.initialOwner.val = 1 := by have := r.initialOwner.isLt; omega
      simpa [Route.initialSibling, hone] using hsibling
  · by_cases hz : r.initialOwner.val = 0
    · simpa [Route.initialSibling, hz] using hsibling
    · have hone : r.initialOwner.val = 1 := by have := r.initialOwner.isLt; omega
      simpa [Route.owner, hone] using hselected

theorem bucketSibling_mem_disclosure (r : Route) (level : Fin 4) :
    bucketTreeChild level.val ((r.bucket.val / 2 ^ level.val) ^^^ 1) ∈
      r.disclosure := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨level.val, List.mem_range.mpr level.isLt, rfl⟩

theorem bucketJoin_mem_recovery (r : Route) (level : Fin 4) :
    bucketJoin level.val (r.bucket.val / 2 ^ (level.val + 1)) ∈
      r.recovery := by
  simp only [Route.recovery, List.mem_append]
  right
  apply List.mem_map.mpr
  exact ⟨level.val, List.mem_range.mpr level.isLt, rfl⟩

theorem bucket_level_reconstructs (r : Route) (level : Fin 4)
    (hchild : r.Reconstructs
      (bucketTreeChild level.val (r.bucket.val / 2 ^ level.val))) :
    r.Reconstructs (bucketJoin level.val (r.bucket.val / 2 ^ (level.val + 1))) := by
  let child := r.bucket.val / 2 ^ level.val
  have hsibling : r.Reconstructs (bucketTreeChild level.val (child ^^^ 1)) :=
    .disclosed (bucketSibling_mem_disclosure r level)
  have hposition : child / 2 < 2 ^ (3 - level.val) := by
    have hb := r.bucket.isLt
    dsimp [child]
    fin_cases level <;> norm_num at * <;> omega
  have hposEq : child / 2 = r.bucket.val / 2 ^ (level.val + 1) := by
    dsimp [child]
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [← hposEq]
  have hmem : bucketJoin level.val (child / 2) ∈ r.recovery := by
    rw [hposEq]
    exact bucketJoin_mem_recovery r level
  have hnode := graphNode_bucketJoin level (child / 2) hposition
  have hdiv := sibling_div_two child
  have hmod := sibling_mod_two child
  have hmodlt : child % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsiblingmodlt : (child ^^^ 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  apply Route.Reconstructs.binary hmem hnode
  · by_cases hside : child % 2 = 0
    · have hleft : 2 * (child / 2) = child := by omega
      simpa only [hleft, child] using hchild
    · have hleft : 2 * (child / 2) = child ^^^ 1 := by omega
      simpa only [hleft] using hsibling
  · by_cases hside : child % 2 = 0
    · have hright : 2 * (child / 2) + 1 = child ^^^ 1 := by omega
      simpa only [hright] using hsibling
    · have hright : 2 * (child / 2) + 1 = child := by omega
      simpa only [hright, child] using hchild

theorem root_reconstructs (r : Route) : r.Reconstructs (graphNodes - 1) := by
  have hlevels : ∀ level : Fin 4, r.Reconstructs
      (bucketJoin level.val (r.bucket.val / 2 ^ (level.val + 1))) := by
    intro level
    induction level using Fin.induction with
    | zero =>
        apply bucket_level_reconstructs
        simpa [bucketTreeChild] using child_root_reconstructs r
    | succ previous ih =>
        apply bucket_level_reconstructs
        simpa [bucketTreeChild] using ih
  have hlast := hlevels ⟨3, by decide⟩
  have hb := r.bucket.isLt
  have hdiv : r.bucket.val / 16 = 0 := by omega
  simpa [bucketJoin, bucketLevelBase, hdiv, fixed_geometry.2.2.2.1] using hlast

theorem ownerVertex_lt (a : OwnerAddress) (vertex : Nat)
    (hvertex : vertex < ownerBase a.bucket.val a.layer.val a.owner.val + 847) :
    vertex < graphNodes := by
  have hb := a.bucket.isLt
  have ho := a.ownerNumber_lt
  rw [fixed_geometry.2.2.2.1]
  unfold ownerBase at hvertex
  omega

theorem layerDisclosure_bounds (r : Route) (layer : Layer) (vertex : Nat)
    (hv : vertex ∈ r.layerDisclosure layer) : vertex < graphNodes := by
  simp only [Route.layerDisclosure, List.mem_cons, List.mem_map] at hv
  rcases hv with hguard | ⟨depth, hd, ha⟩
  · subst vertex
    apply ownerVertex_lt (r.ownerAddress layer)
    have hs := (r.slot layer).isLt
    change ownerBase r.bucket.val layer.val (r.owner layer) + (r.slot layer).val * 10 +
      (8 - ((r.code layer).depth ⟨5, by decide⟩).val) <
        ownerBase r.bucket.val layer.val (r.owner layer) + 847
    omega
  · subst vertex
    let level : Depth := ⟨4 - depth.val, by omega⟩
    let point : Fin 9 := ⟨8 - ((r.code layer).depth ⟨depth.val, by omega⟩).val, by omega⟩
    have hc := route_sibling_position_bound r layer level
    have hp := (edgePointVertex_in_owner (r.ownerAddress layer) level
      (((r.slot layer).val / 2 ^ level.val) ^^^ 1) hc point).2
    exact ownerVertex_lt (r.ownerAddress layer) _ hp

theorem bucketSibling_bound (r : Route) (level : Fin 4) :
    bucketTreeChild level.val ((r.bucket.val / 2 ^ level.val) ^^^ 1) < graphNodes := by
  have hb := r.bucket.isLt
  have hhalf := sibling_div_two (r.bucket.val / 2 ^ level.val)
  have hmod : ((r.bucket.val / 2 ^ level.val) ^^^ 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [fixed_geometry.2.2.2.1]
  fin_cases level <;>
    norm_num [bucketTreeChild, childRoot, bucketJoin, bucketLevelBase] at * <;> omega

theorem disclosure_bounds (r : Route) (vertex : Nat) (hv : vertex ∈ r.disclosure) :
    vertex < graphNodes := by
  simp only [Route.disclosure, List.mem_append, List.mem_singleton, List.mem_flatMap] at hv
  rcases hv with (hbucket | hinitial) | ⟨layer, hl, hlocal⟩
  · obtain ⟨level, hl, rfl⟩ := List.mem_map.mp hbucket
    exact bucketSibling_bound r ⟨level, List.mem_range.mp hl⟩
  · subst vertex
    have hb := r.bucket.isLt
    have ho : r.initialOwner.val ^^^ 1 < 2 := by
      have h := r.initialOwner.isLt
      by_cases hz : r.initialOwner.val = 0
      · simp [hz]
      · have hone : r.initialOwner.val = 1 := by omega
        simp [hone]
    rw [fixed_geometry.2.2.2.1]
    unfold Route.initialSibling ownerRoot ownerBase
    omega
  · exact layerDisclosure_bounds r layer vertex hlocal

theorem guardWork_bounds (r : Route) (layer : Layer) (vertex : Nat)
    (hv : vertex ∈ r.guardWork layer) : vertex < graphNodes := by
  obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hv
  have hstep := List.mem_range.mp hs
  have hdepth := ((r.code layer).depth ⟨5, by decide⟩).isLt
  have hslot := (r.slot layer).isLt
  apply ownerVertex_lt (r.ownerAddress layer)
  change ownerBase r.bucket.val layer.val (r.owner layer) + (r.slot layer).val * 10 +
    (9 - ((r.code layer).depth ⟨5, by decide⟩).val + step) <
      ownerBase r.bucket.val layer.val (r.owner layer) + 847
  omega

theorem levelWork_bounds (r : Route) (layer : Layer) (level : Depth) (vertex : Nat)
    (hv : vertex ∈ r.levelWork layer level) : vertex < graphNodes := by
  simp only [Route.levelWork, List.mem_append, List.mem_singleton] at hv
  rcases hv with (hselected | hsibling) | hjoin
  · obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hselected
    have hstep := List.mem_range.mp hs
    exact ownerVertex_lt (r.ownerAddress layer) _
      (edgePointVertex_in_owner (r.ownerAddress layer) level _
        (route_child_position_bound r layer level) ⟨step + 1, by omega⟩).2
  · obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hsibling
    have hstep := List.mem_range.mp hs
    have hdepth := ((r.code layer).depth ⟨4 - level.val, by omega⟩).isLt
    exact ownerVertex_lt (r.ownerAddress layer) _
      (edgePointVertex_in_owner (r.ownerAddress layer) level _
        (route_sibling_position_bound r layer level)
        ⟨9 - ((r.code layer).depth ⟨4 - level.val, by omega⟩).val + step, by omega⟩).2
  · subst vertex
    have hc := route_child_position_bound r layer level
    have hp : ((r.slot layer).val / 2 ^ level.val) / 2 < 2 ^ (4 - level.val) := by
      fin_cases level <;> norm_num at * <;> omega
    exact ownerVertex_lt (r.ownerAddress layer) _
      (treeJoin_in_owner (r.ownerAddress layer) level _ hp).2

theorem recovery_bounds (r : Route) (vertex : Nat) (hv : vertex ∈ r.recovery) :
    vertex < graphNodes := by
  simp only [Route.recovery, List.mem_append, List.mem_singleton, List.mem_flatMap] at hv
  rcases hv with (⟨layer, hl, hlocal⟩ | hchild) | hbucket
  · simp only [Route.layerWork, List.mem_append, List.mem_flatMap] at hlocal
    rcases hlocal with hguard | ⟨level, hk, he⟩
    · exact guardWork_bounds r layer vertex hguard
    · exact levelWork_bounds r layer level vertex he
  · subst vertex
    have hb := r.bucket.isLt
    rw [fixed_geometry.2.2.2.1]
    unfold childRoot
    omega
  · obtain ⟨level, hl, rfl⟩ := List.mem_map.mp hbucket
    have hb := r.bucket.isLt
    have hlevel := List.mem_range.mp hl
    rw [fixed_geometry.2.2.2.1]
    have hcases : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      norm_num [bucketJoin, bucketLevelBase] <;> omega

end PoissonDAG.GRSCC
