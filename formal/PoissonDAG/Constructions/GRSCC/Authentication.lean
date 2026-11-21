import PoissonDAG.Constructions.GRSCC.AuthGeometryChecks

namespace PoissonDAG.GRSCC
namespace AuthenticationGeometry
theorem local_successor (s : Slot) (g : Lane) (e : Fin 9) (v : Nat)
    (hv : v ∈ (if g.val = 0 then [] else [entryVertex s g]) ++
      opening s g e :: work s g e) (hneq : v ≠ exitVertex s g) :
    ∃ w ∈ work s g e, parentAt v (graphNode w) := by
  have h := all_lanes_connected s g e
  unfold laneConnected at h
  have hstep := (List.all_eq_true.mp h) v hv
  simp only [beq_iff_eq, Bool.or_eq_true, hneq, false_or] at hstep
  obtain ⟨w, hw, hadj⟩ := List.any_eq_true.mp hstep
  refine ⟨w, hw, ?_⟩
  cases hn : graphNode w <;> simpa [parentBool, hn, parentAt] using hadj

theorem local_exclusion (s : Slot) (g h : Lane) (e f : Fin 9)
    (heq : g = h → e = f) : opening s h f ∉ work s g e := by
  have hc := all_lanes_separated s g h e
  by_cases hgh : g = h
  · subst h
    have hf := heq rfl
    subst f
    simpa [separated] using hc
  · simp only [separated, if_neg hgh] at hc
    have hf := List.all_eq_true.mp hc f (List.mem_finRange f)
    simpa using hf

theorem layer_disclosure_view (r : Route) (l : Layer) {v : Nat}
    (hv : v ∈ r.layerDisclosure l) : ∃ g : Lane,
      v = base (r.ownerAddress l) + opening (r.slot l) g (depthFor r l g) := by
  simp only [Route.layerDisclosure, List.mem_cons, List.mem_map] at hv
  rcases hv with h | ⟨d, _, h⟩
  · exact ⟨guardLane, by simpa [guardLane, opening, depthFor, base,
      Route.ownerAddress, Nat.add_assoc] using h⟩
  · let level : Depth := ⟨4 - d.val, by omega⟩
    let g := treeLane level
    have hcode : 5 - g.val = d.val := by
      have hd := d.isLt
      dsimp [g, treeLane, level]
      omega
    let n := ((r.slot l).val / 2 ^ level.val) ^^^ 1
    let step := 8 - ((r.code l).depth ⟨d.val, by omega⟩).val
    have haddr : edgePointVertex r.bucket.val l.val (r.owner l) level.val n step = v := h
    refine ⟨g, haddr.symm.trans ?_⟩
    have he := lift_edge (r.ownerAddress l) level n step
    simpa [Route.ownerAddress, opening, g, treeLane, depthFor, hcode, n, step, level,
      show 5 - (4 - d.val + 1) = d.val by have hd := d.isLt; omega] using he

theorem work_mem_recovery (r : Route) (l : Layer) (g : Lane) {w : Nat}
    (hw : w ∈ work (r.slot l) g (depthFor r l g)) :
    base (r.ownerAddress l) + w ∈ r.recovery := by
  induction g using Fin.cases with
  | zero =>
    apply guardWork_mem_recovery r l
    rw [lift_guard_work]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  | succ d =>
    apply levelWork_mem_recovery r l d
    rw [lift_level_work]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem layer_work_view (r : Route) (l : Layer) {v : Nat}
    (hv : v ∈ r.layerWork l) : ∃ (g : Lane) (w : Nat),
      w ∈ work (r.slot l) g (depthFor r l g) ∧ v = base (r.ownerAddress l) + w := by
  simp only [Route.layerWork, List.mem_append, List.mem_flatMap] at hv
  rcases hv with h | ⟨d, _, h⟩
  · rw [lift_guard_work] at h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    exact ⟨guardLane, w, hw, he.symm⟩
  · rw [lift_level_work] at h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    exact ⟨treeLane d, w, hw, he.symm⟩

private theorem local_work_lt {s : Slot} {g : Lane} {e : Fin 9} {w : Nat}
    (hw : w ∈ work s g e) : w < 847 :=
  of_decide_eq_true (List.all_eq_true.mp (work_bound s g e) w hw)

private theorem outer_disjoint : ∀ (b : Bucket) (d : Fin 4) (l : Layer) (o : Fin 32),
    let base := ownerBase b.val l.val o.val
    let v := bucketTreeChild d.val ((b.val / 2 ^ d.val) ^^^ 1)
    (l.val = 6 → o.val < 2) → (v < base ∨ base + 847 ≤ v) := by decide +kernel

private theorem layer_owner_ne_initial (r : Route) (l : Layer) (w : Nat) (hw : w < 847) :
    base (r.ownerAddress l) + w ≠ r.initialSibling := by
  have ho := (r.ownerAddress l).owner_lt_32
  change r.owner l < 32 at ho
  have hi := r.initialOwner.isLt
  have hx : r.initialOwner.val ^^^ 1 < 2 ∧ r.initialOwner.val ^^^ 1 ≠ r.initialOwner.val := by
    have h : ∀ o : Fin 2, o.val ^^^ 1 < 2 ∧ o.val ^^^ 1 ≠ o.val := by decide
    exact h _
  have hl := l.isLt
  change r.bucket.val * 164319 + (l.val * 32 + r.owner l) * 847 + w ≠
    r.bucket.val * 164319 + (6 * 32 + (r.initialOwner.val ^^^ 1)) * 847 + 846
  by_cases he : l.val = 6
  · have ht : r.owner l = r.initialOwner.val := by simp [Route.owner, he]
    omega
  · omega

theorem work_not_disclosed (r : Route) (l : Layer) (g : Lane) {w : Nat}
    (hw : w ∈ work (r.slot l) g (depthFor r l g)) :
    base (r.ownerAddress l) + w ∉ r.disclosure := by
  have hb := local_work_lt hw
  intro hit
  simp only [Route.disclosure, List.mem_append, List.mem_singleton, List.mem_flatMap] at hit
  rcases hit with (h | h) | ⟨k, _, h⟩
  · obtain ⟨d, hd, he⟩ := List.mem_map.mp h
    let o : Fin 32 := ⟨r.owner l, (r.ownerAddress l).owner_lt_32⟩
    have hh := outer_disjoint r.bucket ⟨d, List.mem_range.mp hd⟩ l o (by
      intro hl
      change r.owner l < 2
      simpa [Route.owner, hl] using r.initialOwner.isLt)
    change _ = ownerBase r.bucket.val l.val (r.owner l) + w at he
    change bucketTreeChild d ((r.bucket.val / 2 ^ d) ^^^ 1) < ownerBase r.bucket.val l.val (r.owner l) ∨
      ownerBase r.bucket.val l.val (r.owner l) + 847 ≤ bucketTreeChild d ((r.bucket.val / 2 ^ d) ^^^ 1) at hh
    omega
  · exact layer_owner_ne_initial r l w hb h
  · obtain ⟨j, hj⟩ := layer_disclosure_view r k h
    have hlt := opening_bound (r.slot k) j (depthFor r k j)
    have hol := (r.ownerAddress l).owner_lt_32
    have hok := (r.ownerAddress k).owner_lt_32
    change r.owner l < 32 at hol
    change r.owner k < 32 at hok
    change r.bucket.val * 164319 + (l.val * 32 + r.owner l) * 847 + w =
      r.bucket.val * 164319 + (k.val * 32 + r.owner k) * 847 + _ at hj
    have hlk : l = k := Fin.ext (by omega)
    subst k
    have hsame : w = opening (r.slot l) j (depthFor r l j) := by omega
    apply local_exclusion (r.slot l) g j (depthFor r l g) (depthFor r l j)
      (fun he => congrArg (depthFor r l) he)
    rwa [← hsame]

def HasSuccessor (r : Route) (v : Nat) : Prop :=
  ∃ w ∈ r.recovery, w ∉ r.disclosure ∧ parentAt v (graphNode w)

theorem local_hasSuccessor (r : Route) (l : Layer) (g : Lane) (v : Nat)
    (hv : v ∈ (if g.val = 0 then [] else [entryVertex (r.slot l) g]) ++
      opening (r.slot l) g (depthFor r l g) :: work (r.slot l) g (depthFor r l g))
    (hne : v ≠ exitVertex (r.slot l) g) : HasSuccessor r (base (r.ownerAddress l) + v) := by
  obtain ⟨w, hw, hparent⟩ := local_successor _ _ _ v hv hne
  exact ⟨_, work_mem_recovery r l g hw, work_not_disclosed r l g hw,
    lift_parent _ v w (local_work_lt hw) hparent⟩

private theorem entry_ne_exit : ∀ (s : Slot) (d : Fin 5),
    entryVertex s d.succ ≠ exitVertex s d.succ := by decide +kernel

private theorem guard_exit_mem : ∀ (s : Slot) (e : Fin 9),
    exitVertex s guardLane ∈ work s guardLane e := by decide +kernel

private theorem actual_leaf_nonopening (r : Route) (l : Layer) :
    leafVertex r.bucket.val l.val (r.owner l) (r.slot l).val ∉ r.disclosure := by
  have h := work_not_disclosed r l guardLane (guard_exit_mem (r.slot l) _)
  simpa [leafVertex, base, exitVertex, guardLane, Route.ownerAddress, ownerBase,
    Nat.add_assoc] using h

private theorem mem_not_of_frontier_false (r : Route) {v : Nat}
    (hv : v ∈ r.recovery) (h : get r.frontier v = false) : v ∉ r.disclosure := by
  rw [frontier_get r _ (recovery_bounds r _ hv)] at h
  exact of_decide_eq_false h

private theorem ownerRoot_hasSuccessor (r : Route) (l : Layer) :
    HasSuccessor r (ownerRoot r.bucket.val l.val (r.owner l)) := by
  by_cases htop : l.val = 6
  · have ho : r.owner l = r.initialOwner.val := by simp [Route.owner, htop]
    refine ⟨_, childRoot_mem_recovery r, mem_not_of_frontier_false r
      (childRoot_mem_recovery r) r.childRoot_not_supplied, ?_⟩
    rw [graphNode_childRoot, htop, ho]
    have hcases : r.initialOwner.val = 0 ∨ r.initialOwner.val = 1 := by
      have := r.initialOwner.isLt
      omega
    rcases hcases with h | h <;> simp [parentAt, h]
  · let k : Layer := ⟨l.val + 1, by have := l.isLt; omega⟩
    have ho : r.owner l = (r.slot k).val := by simp [Route.owner, htop, k]
    have hk : k.val ≠ 0 := by dsimp [k]; omega
    have hn := graphNode_leaf (r.ownerAddress k) (r.slot k)
    change graphNode (leafVertex r.bucket.val k.val (r.owner k) (r.slot k).val) =
      if k.val = 0 then _ else _ at hn
    rw [if_neg hk] at hn
    refine ⟨_, leaf_mem_recovery r k, actual_leaf_nonopening r k, ?_⟩
    rw [hn]
    right
    simp [Route.ownerAddress, k, ho]

theorem all_local_vertices_continue (r : Route) (l : Layer) (g : Lane) (v : Nat)
    (hv : v ∈ opening (r.slot l) g (depthFor r l g) :: work (r.slot l) g (depthFor r l g)) :
    HasSuccessor r (base (r.ownerAddress l) + v) := by
  by_cases hexit : v = exitVertex (r.slot l) g
  · subst v
    by_cases hg : g.val = 5
    · have hg' : g = 5 := Fin.ext hg
      subst g
      rw [terminal_exit]
      exact ownerRoot_hasSuccessor r l
    · let d : Fin 5 := ⟨g.val, by have := g.isLt; omega⟩
      have hd : g = d.castSucc := Fin.ext rfl
      rw [hd, lane_exits_continue]
      apply local_hasSuccessor r l d.succ
      · simp
      · exact entry_ne_exit _ d
  · apply local_hasSuccessor r l g v (List.mem_append_right _ hv) hexit

private theorem outer_hasSuccessor (r : Route) (d : Fin 4) (v : Nat)
    (hv : v = authOuterChild r.bucket d.val ∨ v = authOuterSibling r.bucket d) :
    HasSuccessor r v := by
  refine ⟨_, bucketJoin_mem_recovery r d, mem_not_of_frontier_false r
    (bucketJoin_mem_recovery r d) (r.outerJoin_not_supplied d), ?_⟩
  change parentAt v (graphNode (authOuterJoin r.bucket d))
  rcases authOuter_children r.bucket d with h | h
  · rw [h]; exact hv
  · rw [h]; exact hv.elim Or.inr Or.inl

theorem all_successors (r : Route) (v : Nat)
    (hv : v ∈ r.disclosure ∨ v ∈ r.recovery) (hne : v ≠ graphNodes - 1) : HasSuccessor r v := by
  rcases hv with h | h
  · simp only [Route.disclosure, List.mem_append, List.mem_singleton, List.mem_flatMap] at h
    rcases h with (h | h) | ⟨l, _, hl⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      exact outer_hasSuccessor r ⟨d, List.mem_range.mp hd⟩ _ (Or.inr rfl)
    · subst v
      refine ⟨_, childRoot_mem_recovery r, mem_not_of_frontier_false r
        (childRoot_mem_recovery r) r.childRoot_not_supplied, ?_⟩
      rw [graphNode_childRoot]
      have hc : r.initialOwner.val = 0 ∨ r.initialOwner.val = 1 := by
        have := r.initialOwner.isLt
        omega
      rcases hc with h | h <;> simp [Route.initialSibling, parentAt, h]
    · obtain ⟨g, rfl⟩ := layer_disclosure_view r l hl
      exact all_local_vertices_continue r l g _ (by simp)
  · simp only [Route.recovery, List.mem_append, List.mem_singleton, List.mem_flatMap] at h
    rcases h with (⟨l, _, hl⟩ | h) | h
    · obtain ⟨g, w, hw, rfl⟩ := layer_work_view r l hl
      exact all_local_vertices_continue r l g w (List.mem_cons_of_mem _ hw)
    · subst v
      apply outer_hasSuccessor r 0
      exact Or.inl (by simp [authOuterChild, bucketTreeChild])
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      let k : Fin 4 := ⟨d, List.mem_range.mp hd⟩
      have hlast : d ≠ 3 := by
        intro he
        subst d
        apply hne
        have ht := (authOuter_next r.bucket (3 : Fin 4)).symm.trans (authOuter_last r.bucket)
        rw [fixed_geometry.2.2.2.1]
        change bucketJoin 3 (r.bucket.val / 2 ^ (3 + 1)) = 2629118
        exact ht
      let j : Fin 4 := ⟨d + 1, by have := k.isLt; change d < 4 at this; omega⟩
      exact outer_hasSuccessor r j _ (Or.inl (authOuter_next r.bucket k).symm)

end AuthenticationGeometry

theorem route_authenticated (r : Route) : V2.Authenticated graph r.frontier r.plan :=
  r.authenticated_of_successors (AuthenticationGeometry.all_successors r)

theorem scheme_authenticated (raw : Nat) (hr : raw ∈ scheme.accepted) :
    V2.Authenticated scheme.graph (scheme.frontier raw) (scheme.plan raw) := by
  obtain ⟨r, hf, hp⟩ := scheme_layout_route raw hr
  rw [hf, hp]
  exact route_authenticated r
end PoissonDAG.GRSCC
