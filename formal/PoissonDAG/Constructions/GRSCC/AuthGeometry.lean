import PoissonDAG.Constructions.GRSCC.AuthCore

namespace PoissonDAG.GRSCC
/-! Divide an owner into its guard lane and five tree levels. Each lane
has one opening. The recovery addresses in a lane depend on just one depth,
so all local path and separation facts have small finite domains. Lane zero
ends at the selected leaf. Each subsequent lane ends at its selected join. -/
namespace AuthenticationGeometry

abbrev Lane := Fin 6

def opening (s : Slot) (g : Lane) (e : Fin 9) : Nat :=
  if g.val = 0 then s.val * 10 + (8 - e.val)
  else
    let d := g.val - 1
    edgePointVertex 0 0 0 d ((s.val / 2 ^ d) ^^^ 1) (8 - e.val)

def work (s : Slot) (g : Lane) (e : Fin 9) : List Nat :=
  if g.val = 0 then
    (List.range (e.val + 1)).map (fun k => s.val * 10 + (9 - e.val + k))
  else
    let d := g.val - 1
    let pos := s.val / 2 ^ d
    (List.range 8).map (fun k => edgePointVertex 0 0 0 d pos (k + 1)) ++
      (List.range e.val).map (fun k => edgePointVertex 0 0 0 d (pos ^^^ 1) (9 - e.val + k)) ++
      [treeJoin 0 0 0 d (pos / 2)]

def exitVertex (s : Slot) (g : Lane) : Nat :=
  if g.val = 0 then leafVertex 0 0 0 s.val
  else
    let d := g.val - 1
    treeJoin 0 0 0 d ((s.val / 2 ^ d) / 2)

def entryVertex (s : Slot) (g : Lane) : Nat :=
  let d := g.val - 1
  treeChild 0 0 0 d (s.val / 2 ^ d)

def parentBool (p w : Nat) : Bool :=
  match graphNode w with
  | .source => false
  | .unary a => p == a
  | .binary a b => p == a || p == b

/-- Each nonexit vertex opens directly into a later operation of this lane.
The selected child from the preceding lane is included in each tree lane. -/
def laneConnected (s : Slot) (g : Lane) (e : Fin 9) : Bool :=
  let ws := work s g e
  ((if g.val = 0 then [] else [entryVertex s g]) ++ opening s g e :: ws).all
    (fun v => v == exitVertex s g || ws.any (parentBool v))

/-- For distinct lanes, all possible openings must stay outside the work.
For the same lane, only its actual opening is relevant. -/
def separated (s : Slot) (g h : Lane) (e : Fin 9) : Bool :=
  let ws := work s g e
  if g = h then !(ws.contains (opening s g e))
  else (List.finRange 9).all (fun f => !(ws.contains (opening s h f)))

private def zeroOwner : OwnerAddress := ⟨0, 0, ⟨0, by decide⟩⟩

def base (a : OwnerAddress) : Nat := ownerBase a.bucket.val a.layer.val a.owner.val

theorem lift_join (a : OwnerAddress) (d n : Nat) :
    treeJoin a.bucket.val a.layer.val a.owner.val d n = base a + treeJoin 0 0 0 d n := by
  simp [treeJoin, base, ownerBase, Nat.add_assoc]

theorem lift_child (a : OwnerAddress) (d n : Nat) :
    treeChild a.bucket.val a.layer.val a.owner.val d n = base a + treeChild 0 0 0 d n := by
  unfold treeChild
  split <;> simp [leafVertex, treeJoin, base, ownerBase, Nat.add_assoc]

theorem lift_edge (a : OwnerAddress) (d : Depth) (n step : Nat) :
    edgePointVertex a.bucket.val a.layer.val a.owner.val d.val n step =
      base a + edgePointVertex 0 0 0 d.val n step := by
  by_cases hz : step = 0
  · simp only [edgePointVertex, if_pos hz]
    exact lift_child a d.val n
  · have hd : 0 < treeLevelBase d.val := by fin_cases d <;> decide
    simp only [edgePointVertex, if_neg hz]
    change base a + treeLevelBase d.val + n / 2 * 17 + n % 2 * 8 + step - 1 =
      base a + (0 + treeLevelBase d.val + n / 2 * 17 + n % 2 * 8 + step - 1)
    omega

set_option maxRecDepth 4096 in
theorem lift_parent (a : OwnerAddress) (p w : Nat) (hw : w < 847)
    (hp : parentAt p (graphNode w)) :
    parentAt (base a + p) (graphNode (base a + w)) := by
  have hz := graphNode_owner zeroOwner ⟨w, hw⟩
  simp only [zeroOwner, Fin.val_mk, Fin.val_zero, show ownerBase 0 0 0 = 0 by rfl,
    Nat.zero_add, ↓reduceIte] at hz
  have ha := graphNode_owner a ⟨w, hw⟩
  simp only [Fin.val_mk] at ha
  rw [hz] at hp
  unfold base
  rw [ha]
  split_ifs at hp <;> split_ifs <;> simp_all only [parentAt, Nat.add_left_cancel_iff]
  all_goals first
    | omega
    | rw [lift_child]; simpa [base] using hp
    | left; omega

def depthFor (r : Route) (layer : Layer) (g : Lane) : Fin 9 :=
  (r.code layer).depth ⟨5 - g.val, by omega⟩

def guardLane : Lane := ⟨0, by decide⟩

def treeLane (d : Depth) : Lane := d.succ

theorem lift_guard_work (r : Route) (layer : Layer) :
    r.guardWork layer = (work (r.slot layer) guardLane (depthFor r layer guardLane)).map
      (fun x => base (r.ownerAddress layer) + x) := by
  simp [Route.guardWork, work, guardLane, depthFor, base, Route.ownerAddress,
    List.map_map, Function.comp_def, Nat.add_assoc]

theorem lift_level_work (r : Route) (layer : Layer) (d : Depth) :
    r.levelWork layer d = (work (r.slot layer) (treeLane d) (depthFor r layer (treeLane d))).map
      (fun x => base (r.ownerAddress layer) + x) := by
  let a := r.ownerAddress layer
  have hdep : 5 - (d.val + 1) = 4 - d.val := by omega
  simp only [Route.levelWork, work, treeLane, depthFor, Fin.val_succ, Nat.add_one_ne_zero,
    if_false, Nat.add_sub_cancel, hdep, List.map_append, List.map_map, List.map_cons,
    List.map_nil, Function.comp_def]
  have he := lift_edge a d
  have hj := lift_join a d.val
  change ∀ n step, edgePointVertex r.bucket.val layer.val (r.owner layer) d.val n step =
    base (r.ownerAddress layer) + edgePointVertex 0 0 0 d.val n step at he
  change ∀ n, treeJoin r.bucket.val layer.val (r.owner layer) d.val n =
    base (r.ownerAddress layer) + treeJoin 0 0 0 d.val n at hj
  simp only [he, hj]

end AuthenticationGeometry

end PoissonDAG.GRSCC
