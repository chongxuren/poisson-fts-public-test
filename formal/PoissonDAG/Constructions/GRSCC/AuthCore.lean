import PoissonDAG.Constructions.GRSCC.Circuit
import PoissonDAG.V2.Model

namespace PoissonDAG.GRSCC
private theorem Route.layerDisclosure_below_child (r : Route) (layer : Layer)
    (vertex : Nat) (hv : vertex ∈ r.layerDisclosure layer) : vertex < childRoot r.bucket.val := by
  have hb := r.bucket.isLt
  have ho := (r.ownerAddress layer).ownerNumber_lt
  change layer.val * 32 + r.owner layer < 194 at ho
  simp only [Route.layerDisclosure, List.mem_cons, List.mem_map] at hv
  rcases hv with hguard | ⟨depth, _, ha⟩
  · subst vertex
    have hs := (r.slot layer).isLt
    unfold ownerBase childRoot
    omega
  · subst vertex
    let level : Depth := ⟨4 - depth.val, by omega⟩
    let point : Fin 9 := ⟨8 - ((r.code layer).depth ⟨depth.val, by omega⟩).val, by omega⟩
    have h := (edgePointVertex_in_owner (r.ownerAddress layer) level _
      (route_sibling_position_bound r layer level) point).2
    apply Nat.lt_of_lt_of_le h
    change r.bucket.val * 164319 + (layer.val * 32 + r.owner layer) * 847 + 847 ≤ r.bucket.val * 164319 + 164318
    omega

private theorem outerJoin_geometry : ∀ (b : Bucket) (d : Fin 4),
    let i := bucketJoin d.val (b.val / 2 ^ (d.val + 1))
    2629104 ≤ i ∧ ∀ e : Fin 4,
      bucketTreeChild e.val ((b.val / 2 ^ e.val) ^^^ 1) ≠ i := by
  decide +kernel

theorem Route.outerJoin_not_supplied (r : Route) (d : Fin 4) :
    get r.frontier (bucketJoin d.val (r.bucket.val / 2 ^ (d.val + 1))) = false := by
  let i := bucketJoin d.val (r.bucket.val / 2 ^ (d.val + 1))
  have hm := bucketJoin_mem_recovery r d
  rw [frontier_get r _ (recovery_bounds r _ hm)]
  apply decide_eq_false
  intro h
  have hgeom := outerJoin_geometry r.bucket d
  simp only [Route.disclosure, List.mem_append, List.mem_singleton, List.mem_flatMap] at h
  rcases h with (h | h) | ⟨layer, _, hl⟩
  · obtain ⟨level, he, heq⟩ := List.mem_map.mp h
    exact hgeom.2 ⟨level, List.mem_range.mp he⟩ heq
  · have hb := r.bucket.isLt
    have ho : r.initialOwner.val ^^^ 1 < 2 := by
      have hf : ∀ b : Fin 2, b.val ^^^ 1 < 2 := by decide
      exact hf _
    have hlt : r.initialSibling < 2629104 := by
      unfold Route.initialSibling ownerRoot ownerBase
      omega
    exact (Nat.not_lt_of_ge hgeom.1) (h.symm ▸ hlt)
  · have hi := r.layerDisclosure_below_child layer _ hl
    have hb := r.bucket.isLt
    unfold childRoot at hi
    exact (Nat.not_lt_of_ge hgeom.1) (by omega)

theorem Route.root_not_supplied (r : Route) : get r.frontier (graph.length - 1) = false := by
  have hl := r.outerJoin_not_supplied ⟨3, by decide⟩
  have hb := r.bucket.isLt
  have hz : r.bucket.val / 16 = 0 := by omega
  rw [root_index]
  simpa [bucketJoin, bucketLevelBase, hz] using hl

def authOuterChild (b : Bucket) (d : Nat) : Nat :=
  bucketTreeChild d (b.val / 2 ^ d)

def authOuterSibling (b : Bucket) (d : Fin 4) : Nat :=
  bucketTreeChild d.val ((b.val / 2 ^ d.val) ^^^ 1)

def authOuterJoin (b : Bucket) (d : Fin 4) : Nat :=
  bucketJoin d.val (b.val / 2 ^ (d.val + 1))

theorem authOuter_children : ∀ (b : Bucket) (d : Fin 4),
    graphNode (authOuterJoin b d) = .binary (authOuterChild b d.val) (authOuterSibling b d) ∨
    graphNode (authOuterJoin b d) = .binary (authOuterSibling b d) (authOuterChild b d.val) := by
  decide +kernel

theorem authOuter_next : ∀ (b : Bucket) (d : Fin 4),
    authOuterChild b (d.val + 1) = authOuterJoin b d := by decide +kernel

theorem authOuter_last : ∀ b : Bucket, authOuterChild b 4 = 2629118 := by decide +kernel

private theorem childRoot_geometry : ∀ (b : Bucket) (d : Fin 4),
    bucketTreeChild d.val ((b.val / 2 ^ d.val) ^^^ 1) ≠ childRoot b.val := by decide +kernel

private theorem initial_below_child : ∀ (b : Bucket) (o : Fin 2),
    ownerRoot b.val 6 (o.val ^^^ 1) < childRoot b.val := by decide +kernel

theorem Route.childRoot_not_supplied (r : Route) :
    get r.frontier (childRoot r.bucket.val) = false := by
  rw [frontier_get r _ (recovery_bounds r _ (childRoot_mem_recovery r))]
  apply decide_eq_false
  intro h
  simp only [Route.disclosure, List.mem_append, List.mem_singleton, List.mem_flatMap] at h
  rcases h with (h | h) | ⟨layer, _, hl⟩
  · obtain ⟨level, he, heq⟩ := List.mem_map.mp h
    exact childRoot_geometry r.bucket ⟨level, List.mem_range.mp he⟩ heq
  · have hl : r.initialSibling < childRoot r.bucket.val :=
      initial_below_child r.bucket r.initialOwner
    omega
  · exact (Nat.lt_irrefl _) (r.layerDisclosure_below_child layer _ hl)

def parentAt (p : Nat) : Node → Prop
  | .source => False
  | .unary a => p = a
  | .binary a b => p = a ∨ p = b

private theorem Route.reconstructs_parent (r : Route) {p v : Nat} (hv : r.Reconstructs v)
    (hs : v ∉ r.disclosure) (hp : parentAt p (graphNode v)) : r.Reconstructs p := by
  cases hv with
  | disclosed h => exact False.elim (hs h)
  | unary _ hn ha =>
    rw [hn] at hp
    exact hp.symm ▸ ha
  | binary _ hn ha hb =>
    rw [hn] at hp
    rcases hp with h | h
    · exact h.symm ▸ ha
    · exact h.symm ▸ hb

private def AuthSuccessors (r : Route) : Prop :=
  ∀ v, (v ∈ r.disclosure ∨ v ∈ r.recovery) → v ≠ graphNodes - 1 →
    ∃ w ∈ r.recovery, w ∉ r.disclosure ∧ parentAt v (graphNode w)

private def EndsAtRoot (r : Route) (v : Nat) : Prop :=
  r.Reconstructs v ∧ ∀ label, V2.Uses graph r.frontier (close graph r.frontier r.plan).1 label v →
    V2.Uses graph r.frontier (close graph r.frontier r.plan).1 label (graphNodes - 1)

set_option maxRecDepth 12000 in
private theorem walk_to_root (r : Route) (hsucc : AuthSuccessors r) (fuel : Nat) :
    ∀ v, graphNodes - v ≤ fuel → (v ∈ r.disclosure ∨ v ∈ r.recovery) → EndsAtRoot r v := by
  induction fuel with
  | zero =>
    intro v hdist hv
    have hb : v < graphNodes := hv.elim (disclosure_bounds r v) (recovery_bounds r v)
    omega
  | succ fuel ih =>
    intro v hdist hv
    by_cases he : v = graphNodes - 1
    · subst v
      exact ⟨root_reconstructs r, fun _ h => h⟩
    · obtain ⟨w, hw, hcut, hp⟩ := hsucc v hv he
      have hb := recovery_bounds r w hw
      have hg := graph_get ⟨w, hb⟩
      have hvw := graph_valid w _ hg
      have hlt : v < w := by
        cases hnode : graphNode w with
        | source => simp [parentAt, hnode] at hp
        | unary a =>
          simp only [parentAt, hnode] at hp
          simp only [hnode, Node.ValidAt] at hvw
          omega
        | binary a b =>
          simp only [parentAt, hnode] at hp
          simp only [hnode, Node.ValidAt] at hvw
          rcases hp with h | h <;> omega
      have hrec := ih w (by omega) (Or.inr hw)
      refine ⟨r.reconstructs_parent hrec.1 hcut hp, ?_⟩
      intro label huse
      apply hrec.2 label
      apply V2.Uses.hash huse
      · rw [frontier_get r w hb]
        exact decide_eq_false hcut
      · apply close_of_planDerives graph_valid r.frontier r.plan _ _ (r.reconstructs_planDerives _ hrec.1)
        · rw [frontier_length, graph_length']
        · rwa [graph_length']
      · unfold V2.IsParent
        rw [hg]
        cases hn : graphNode w <;> simpa only [hn, parentAt] using hp

/-- The strictly increasing path of computed vertices ends at the root. -/
theorem Route.authenticated_of_successors (r : Route)
    (hsucc : ∀ v, (v ∈ r.disclosure ∨ v ∈ r.recovery) → v ≠ graphNodes - 1 →
      ∃ w ∈ r.recovery, w ∉ r.disclosure ∧ parentAt v (graphNode w)) :
    V2.Authenticated graph r.frontier r.plan := by
  refine ⟨r.root_not_supplied, route_close_root r, ?_⟩
  intro i hi
  have hb : i.val < graphNodes := by rw [← graph_length']; exact i.isLt
  have hm := hi
  rw [frontier_get r _ hb, decide_eq_true_eq] at hm
  have hroot : graph.length - 1 = graphNodes - 1 := congrArg (fun n : Nat => n - 1) graph_length'
  have path := walk_to_root r hsucc (graphNodes - i.val) i.val (Nat.le_refl _) (Or.inl hm)
  have used := path.2 i.val (.input hi)
  exact hroot.symm ▸ used


end PoissonDAG.GRSCC
