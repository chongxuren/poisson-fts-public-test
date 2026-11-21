import PoissonDAG.Constructions.GRSCC.Parameters

/-!
# An explicit addressed GRS-CC graph

Every address below denotes a *vertex index*, not a hash label. Layer 0 is the
final layer and layer 6 is the initial layer, so the list order is topological.
Each owner occupies 847 consecutive vertices. Its first 320 vertices are 32
blocks of source, eight guard steps, and one leaf; the remaining vertices are
the five tree levels, with two eight-step edges and a binary join per block.
Step-zero edge values alias the child vertex and introduce no extra vertex.
-/
namespace PoissonDAG.GRSCC

abbrev Bucket := Fin 16
abbrev Layer := Fin 7
abbrev Slot := Fin 32
abbrev Depth := Fin 5
abbrev CodePosition := Fin 6

theorem sibling_div_two (position : Nat) :
    (position ^^^ 1) / 2 = position / 2 := by
  simp [Nat.xor_div_two]

theorem sibling_mod_two (position : Nat) :
    (position ^^^ 1) % 2 = 1 - position % 2 := by
  have hmod : position % 2 < 2 := Nat.mod_lt _ (by decide)
  have h : (position ^^^ 1) % 2 = position % 2 ^^^ (1 : Nat) := by
    simpa using (Nat.xor_mod_two_pow (a := position) (b := 1) (n := 1))
  rw [h]
  by_cases hzero : position % 2 = 0
  · simp [hzero]
  · have hone : position % 2 = 1 := by omega
    simp [hone]

def ownerCount (layer : Nat) : Nat := if layer = 6 then 2 else 32

structure OwnerAddress where
  bucket : Bucket
  layer : Layer
  owner : Fin (ownerCount layer.val)
  deriving DecidableEq

def ownerBase (bucket layer owner : Nat) : Nat :=
  bucket * 164319 + (layer * 32 + owner) * 847

def guardVertex (a : OwnerAddress) (slot : Slot) (point : Fin 9) : Nat :=
  ownerBase a.bucket a.layer a.owner + slot.val * 10 + point.val

def leafVertex (bucket layer owner slot : Nat) : Nat :=
  ownerBase bucket layer owner + slot * 10 + 9

def ownerRoot (bucket layer owner : Nat) : Nat :=
  ownerBase bucket layer owner + 846

/-- `level=0` is the lowest tree join, and `level=4` is the root. -/
def treeLevelBase (level : Nat) : Nat :=
  320 + 17 * (32 - 2 ^ (5 - level))

def treeJoin (bucket layer owner level position : Nat) : Nat :=
  ownerBase bucket layer owner + treeLevelBase level + position * 17 + 16

def treeChild (bucket layer owner level position : Nat) : Nat :=
  if level = 0 then leafVertex bucket layer owner position
  else treeJoin bucket layer owner (level - 1) position

/-- An edge's step-zero address is exactly the child vertex. -/
def edgeVertex (a : OwnerAddress) (depth : Depth)
    (childPosition : Nat) (point : Fin 9) : Nat :=
  let level := 4 - depth.val
  if point.val = 0 then
    treeChild a.bucket a.layer a.owner level childPosition
  else
    ownerBase a.bucket a.layer a.owner + treeLevelBase level +
      (childPosition / 2) * 17 + (childPosition % 2) * 8 + point.val - 1

def childRoot (bucket : Nat) : Nat := bucket * 164319 + 164318

def bucketLevelBase (level : Nat) : Nat :=
  2629104 + 16 - 2 ^ (4 - level)

def bucketJoin (level position : Nat) : Nat := bucketLevelBase level + position

def bucketTreeChild (level position : Nat) : Nat :=
  if level = 0 then childRoot position else bucketJoin (level - 1) position

def ownerTreeLevel (offset : Nat) : Nat :=
  if offset < 592 then 0 else if offset < 728 then 1 else
  if offset < 796 then 2 else if offset < 830 then 3 else 4

def outerTreeLevel (offset : Nat) : Nat :=
  if offset < 8 then 0 else if offset < 12 then 1 else
  if offset < 14 then 2 else 3

/-- Complete graph description by its index. No probability or byte count is
an input to this function. All source addresses are disjoint guard starts. -/
def graphNode (index : Nat) : Node :=
  if index < 2629104 then
    let bucket := index / 164319
    let childLocal := index % 164319
    if childLocal < 164318 then
      let ownerNumber := childLocal / 847
      let layer := ownerNumber / 32
      let owner := ownerNumber % 32
      let ownerLocal := childLocal % 847
      if ownerLocal < 320 then
        let slot := ownerLocal / 10
        let point := ownerLocal % 10
        if point = 0 then .source
        else if point < 9 then .unary (index - 1)
        else if layer = 0 then .unary (index - 1)
        else .binary (index - 1) (ownerRoot bucket (layer - 1) slot)
      else
        let level := ownerTreeLevel ownerLocal
        let offset := ownerLocal - treeLevelBase level
        let position := offset / 17
        let point := offset % 17
        if point < 16 then
          if point % 8 = 0 then
            .unary (treeChild bucket layer owner level
              (position * 2 + point / 8))
          else .unary (index - 1)
        else .binary (index - 9) (index - 1)
    else .binary (ownerRoot bucket 6 0) (ownerRoot bucket 6 1)
  else
    let outerLocal := index - 2629104
    let level := outerTreeLevel outerLocal
    let position := index - bucketLevelBase level
    .binary (bucketTreeChild level (2 * position))
      (bucketTreeChild level (2 * position + 1))

/-- The literal list consumed by the protected `PoissonDAG.Scheme` semantics.
It is retained intensionally; proofs should use `graph_get`, not expand it. -/
def graphOf (n : Nat) : List Node := List.ofFn (fun i : Fin n => graphNode i.val)

theorem graphOf_length (n : Nat) : (graphOf n).length = n := by
  simp only [graphOf, List.length_ofFn]

theorem graphOf_get (n : Nat) (i : Fin n) :
    (graphOf n)[i.val]? = some (graphNode i.val) := by simp [graphOf]

@[irreducible] def graph : List Node := graphOf graphNodes

theorem graph_eq : graph = graphOf graphNodes := by unfold graph; rfl

theorem graph_length' : graph.length = graphNodes :=
  (congrArg List.length graph_eq).trans (graphOf_length graphNodes)

theorem graph_length : graph.length = 2629119 := by
  exact graph_length'.trans fixed_geometry.2.2.2.1

theorem graph_get (i : Fin graphNodes) : graph[i.val]? = some (graphNode i.val) := by
  exact (congrArg (fun xs : List Node => xs[i.val]?) graph_eq).trans
    (graphOf_get graphNodes i)

theorem root_index : graph.length - 1 = 2629118 := by
  rw [graph_length]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem graphNode_valid (i : Nat) (hi : i < 2629119) :
    (graphNode i).ValidAt i := by
  simp only [graphNode, ownerTreeLevel, outerTreeLevel, ownerRoot, ownerBase,
    treeChild, leafVertex, treeJoin, treeLevelBase, bucketTreeChild, bucketJoin,
    bucketLevelBase, childRoot]
  split_ifs <;> simp_all [Node.ValidAt]
  all_goals omega

set_option maxRecDepth 10000 in
theorem graph_valid (i : Nat) (node : Node) (h : graph[i]? = some node) :
    node.ValidAt i := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
  have hi' : i < graphNodes := lt_of_lt_of_eq hi graph_length'
  have hnode := graph_get ⟨i, hi'⟩
  have heq : node = graphNode i := Option.some.inj (h.symm.trans hnode)
  have hib : i < 2629119 := by simpa only [graph_length] using hi
  have hv : Node.ValidAt i (graphNode i) := graphNode_valid i hib
  exact Eq.mpr (congrArg (Node.ValidAt i) heq) hv

theorem OwnerAddress.owner_lt_32 (a : OwnerAddress) : a.owner.val < 32 := by
  have h := a.owner.isLt
  simp only [ownerCount] at h
  split_ifs at h <;> omega

theorem OwnerAddress.ownerNumber_lt (a : OwnerAddress) :
    a.layer.val * 32 + a.owner.val < 194 := by
  have hl := a.layer.isLt
  have ho := a.owner.isLt
  simp only [ownerCount] at ho
  split_ifs at ho <;> omega

/-- Index arithmetic is isolated from all graph reasoning. -/
theorem ownerIndex_fields (a : OwnerAddress) (offset : Fin 847) :
    let idx := ownerBase a.bucket.val a.layer.val a.owner.val + offset.val
    idx < 2629104 ∧ idx / 164319 = a.bucket.val ∧
    idx % 164319 < 164318 ∧
    idx % 164319 / 847 = a.layer.val * 32 + a.owner.val ∧
    idx % 164319 % 847 = offset.val ∧
    (idx % 164319 / 847) / 32 = a.layer.val ∧
    (idx % 164319 / 847) % 32 = a.owner.val := by
  have hb := a.bucket.isLt
  have hl := a.layer.isLt
  have ho := a.owner_lt_32
  have hn := a.ownerNumber_lt
  have hx := offset.isLt
  have hlocal : (a.layer.val * 32 + a.owner.val) * 847 + offset.val < 164318 := by omega
  have hdiv : (a.bucket.val * 164319 + (a.layer.val * 32 + a.owner.val) * 847 +
      offset.val) / 164319 = a.bucket.val := by omega
  have hmod : (a.bucket.val * 164319 + (a.layer.val * 32 + a.owner.val) * 847 +
      offset.val) % 164319 = (a.layer.val * 32 + a.owner.val) * 847 + offset.val := by omega
  dsimp [ownerBase]
  rw [hdiv, hmod]
  omega

theorem graphNode_owner (a : OwnerAddress) (offset : Fin 847) :
    let idx := ownerBase a.bucket.val a.layer.val a.owner.val + offset.val
    graphNode idx =
      if offset.val < 320 then
        let slot := offset.val / 10
        let point := offset.val % 10
        if point = 0 then .source
        else if point < 9 then .unary (idx - 1)
        else if a.layer.val = 0 then .unary (idx - 1)
        else .binary (idx - 1) (ownerRoot a.bucket.val (a.layer.val - 1) slot)
      else
        let level := ownerTreeLevel offset.val
        let withinLevel := offset.val - treeLevelBase level
        let position := withinLevel / 17
        let point := withinLevel % 17
        if point < 16 then
          if point % 8 = 0 then
            .unary (treeChild a.bucket.val a.layer.val a.owner.val level
              (position * 2 + point / 8))
          else .unary (idx - 1)
        else .binary (idx - 9) (idx - 1) := by
  obtain ⟨hidx, hb, hchild, howner, hoff, hlayer, howner'⟩ := ownerIndex_fields a offset
  simp only [graphNode, if_pos hidx, hb, if_pos hchild, hoff, hlayer, howner']

theorem guardVertex_lt (a : OwnerAddress) (slot : Slot) (point : Fin 9) :
    guardVertex a slot point < graphNodes := by
  have hb := a.bucket.isLt
  have ho := a.ownerNumber_lt
  have hs := slot.isLt
  have hp := point.isLt
  have hn : graphNodes = 2629119 := fixed_geometry.2.2.2.1
  rw [hn]
  unfold guardVertex ownerBase
  omega

set_option maxHeartbeats 1000000 in
theorem graphNode_guard (a : OwnerAddress) (slot : Slot) (point : Fin 9) :
    graphNode (guardVertex a slot point) =
      if point.val = 0 then .source else .unary (guardVertex a slot point - 1) := by
  have hb := a.bucket.isLt
  have hl := a.layer.isLt
  have ho := a.owner_lt_32
  have hn := a.ownerNumber_lt
  have hs := slot.isLt
  have hp := point.isLt
  let idx := guardVertex a slot point
  have hidx : idx < 2629104 := by dsimp [idx, guardVertex, ownerBase]; omega
  have hdiv : idx / 164319 = a.bucket.val := by
    dsimp [idx, guardVertex, ownerBase]; omega
  have hmod : idx % 164319 =
      (a.layer.val * 32 + a.owner.val) * 847 + slot.val * 10 + point.val := by
    dsimp [idx, guardVertex, ownerBase]; omega
  have hchild : idx % 164319 < 164318 := by rw [hmod]; omega
  have howner : idx % 164319 / 847 = a.layer.val * 32 + a.owner.val := by
    rw [hmod]; omega
  have hlocal : idx % 164319 % 847 = slot.val * 10 + point.val := by
    rw [hmod]; omega
  have hguard : idx % 164319 % 847 < 320 := by rw [hlocal]; omega
  have hpoint : idx % 164319 % 847 % 10 = point.val := by rw [hlocal]; omega
  change graphNode idx = if point.val = 0 then .source else .unary (idx - 1)
  simp only [graphNode, if_pos hidx, if_pos hchild, if_pos hguard,
    hpoint, if_pos hp]

set_option maxHeartbeats 1000000 in
theorem graphNode_leaf (a : OwnerAddress) (slot : Slot) :
    graphNode (leafVertex a.bucket.val a.layer.val a.owner.val slot.val) =
      if a.layer.val = 0 then
        .unary (leafVertex a.bucket.val a.layer.val a.owner.val slot.val - 1)
      else
        .binary (leafVertex a.bucket.val a.layer.val a.owner.val slot.val - 1)
          (ownerRoot a.bucket.val (a.layer.val - 1) slot.val) := by
  have hb := a.bucket.isLt
  have hl := a.layer.isLt
  have ho := a.owner_lt_32
  have hn := a.ownerNumber_lt
  have hs := slot.isLt
  let idx := leafVertex a.bucket.val a.layer.val a.owner.val slot.val
  have hidx : idx < 2629104 := by dsimp [idx, leafVertex, ownerBase]; omega
  have hdiv : idx / 164319 = a.bucket.val := by
    dsimp [idx, leafVertex, ownerBase]; omega
  have hmod : idx % 164319 =
      (a.layer.val * 32 + a.owner.val) * 847 + slot.val * 10 + 9 := by
    dsimp [idx, leafVertex, ownerBase]; omega
  have hchild : idx % 164319 < 164318 := by rw [hmod]; omega
  have howner : idx % 164319 / 847 = a.layer.val * 32 + a.owner.val := by
    rw [hmod]; omega
  have hlocal : idx % 164319 % 847 = slot.val * 10 + 9 := by
    rw [hmod]; omega
  have hguard : idx % 164319 % 847 < 320 := by rw [hlocal]; omega
  have hpoint : idx % 164319 % 847 % 10 = 9 := by rw [hlocal]; omega
  have hlayer : (idx % 164319 / 847) / 32 = a.layer.val := by
    rw [howner]; omega
  have hslot : idx % 164319 % 847 / 10 = slot.val := by rw [hlocal]; omega
  change graphNode idx = if a.layer.val = 0 then .unary (idx - 1)
    else .binary (idx - 1) (ownerRoot a.bucket.val (a.layer.val - 1) slot.val)
  simp only [graphNode, if_pos hidx, hdiv, if_pos hchild, if_pos hguard,
    hpoint, hlayer, hslot]
  norm_num

/-- Six per-layer depth choices with the fixed ordinary sum of sixteen. -/
structure Codeword where
  depth : CodePosition → Fin 9
  sum_eq : (Finset.univ.sum (fun j => (depth j).val)) = 16

@[ext] theorem Codeword.ext {left right : Codeword}
    (h : ∀ i, left.depth i = right.depth i) : left = right := by
  cases left with
  | mk leftDepth leftSum =>
      cases right with
      | mk rightDepth rightSum =>
          have hd : leftDepth = rightDepth := funext h
          subst rightDepth
          rfl

structure Route where
  bucket : Bucket
  initialOwner : Fin 2
  slot : Layer → Slot
  code : Layer → Codeword

def Route.owner (r : Route) (layer : Layer) : Nat :=
  if h : layer.val = 6 then r.initialOwner.val
  else (r.slot ⟨layer.val + 1, by omega⟩).val

def Route.ownerAddress (r : Route) (layer : Layer) : OwnerAddress where
  bucket := r.bucket
  layer := layer
  owner := ⟨r.owner layer, by
    by_cases h : layer.val = 6
    · simpa [Route.owner, ownerCount, h] using r.initialOwner.isLt
    · simpa [Route.owner, ownerCount, h] using
        (r.slot ⟨layer.val + 1, by omega⟩).isLt⟩

/-- One guard and five sibling-edge openings in each layer. -/
def Route.layerDisclosure (r : Route) (layer : Layer) : List Nat :=
  let bucket := r.bucket.val
  let owner := r.owner layer
  let slot := (r.slot layer).val
  let code := r.code layer
  let guard := ownerBase bucket layer.val owner + slot * 10 +
    (8 - (code.depth ⟨5, by decide⟩).val)
  guard :: (List.finRange 5).map (fun depth =>
    let level := 4 - depth.val
    let childPosition := (slot / 2 ^ level) ^^^ 1
    let point := 8 - (code.depth ⟨depth.val, by omega⟩).val
    if point = 0 then treeChild bucket layer.val owner level childPosition
    else ownerBase bucket layer.val owner + treeLevelBase level +
      (childPosition / 2) * 17 + (childPosition % 2) * 8 + point - 1)

def Route.initialSibling (r : Route) : Nat :=
  ownerRoot r.bucket.val 6 (r.initialOwner.val ^^^ 1)

def Route.bucketSiblings (r : Route) : List Nat :=
  (List.range 4).map (fun level =>
    bucketTreeChild level ((r.bucket.val / 2 ^ level) ^^^ 1))

/-- The serialized labels are sorted into vertex order by the model's mask.
The route-format order is irrelevant to size, correctness, and covering. -/
def Route.disclosure (r : Route) : List Nat :=
  r.bucketSiblings ++ [r.initialSibling] ++
    ((List.finRange 7).flatMap r.layerDisclosure)

def addressMask (n : Nat) (addresses : List Nat) : List Bool :=
  (List.range n).map (fun v => decide (v ∈ addresses))

theorem addressMask_length (n : Nat) (addresses : List Nat) :
    (addressMask n addresses).length = n := by simp [addressMask]

theorem addressMask_get (n : Nat) (addresses : List Nat) (i : Nat) (hi : i < n) :
    get (addressMask n addresses) i = decide (i ∈ addresses) := by
  simp [get, addressMask, hi]

@[irreducible] def Route.frontier (r : Route) : List Bool := addressMask graphNodes r.disclosure

theorem frontier_eq (r : Route) : r.frontier = addressMask graphNodes r.disclosure := by
  unfold Route.frontier
  rfl

def edgePointVertex (bucket layer owner level childPosition point : Nat) : Nat :=
  if point = 0 then treeChild bucket layer owner level childPosition
  else ownerBase bucket layer owner + treeLevelBase level +
    (childPosition / 2) * 17 + (childPosition % 2) * 8 + point - 1

set_option maxHeartbeats 1000000 in
theorem edgePointVertex_in_owner (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (hchild : childPosition < 2 ^ (5 - level.val)) (point : Fin 9) :
    ownerBase a.bucket.val a.layer.val a.owner.val ≤
      edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition point.val ∧
    edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition point.val <
      ownerBase a.bucket.val a.layer.val a.owner.val + 847 := by
  have hp := point.isLt
  have hmod : childPosition % 2 < 2 := Nat.mod_lt _ (by decide)
  fin_cases level <;>
    norm_num [edgePointVertex, treeChild, leafVertex, treeJoin, treeLevelBase] at * <;>
    split_ifs <;> omega

theorem treeJoin_in_owner (a : OwnerAddress) (level : Depth) (position : Nat)
    (hposition : position < 2 ^ (4 - level.val)) :
    ownerBase a.bucket.val a.layer.val a.owner.val ≤
      treeJoin a.bucket.val a.layer.val a.owner.val level.val position ∧
    treeJoin a.bucket.val a.layer.val a.owner.val level.val position <
      ownerBase a.bucket.val a.layer.val a.owner.val + 847 := by
  fin_cases level <;> norm_num [treeJoin, treeLevelBase] at * <;> omega

set_option maxHeartbeats 1000000 in
theorem graphNode_treeJoin (a : OwnerAddress) (level : Depth) (position : Nat)
    (hposition : position < 2 ^ (4 - level.val)) :
    let idx := treeJoin a.bucket.val a.layer.val a.owner.val level.val position
    graphNode idx = .binary (idx - 9) (idx - 1) := by
  let offset := treeLevelBase level.val + position * 17 + 16
  have hoffset : offset < 847 := by
    dsimp [offset]
    fin_cases level <;> norm_num [treeLevelBase] at * <;> omega
  have houtside : ¬offset < 320 := by
    dsimp [offset]
    fin_cases level <;> norm_num [treeLevelBase] <;> omega
  have hlevel : ownerTreeLevel offset = level.val := by
    dsimp [offset]
    fin_cases level <;> norm_num [treeLevelBase, ownerTreeLevel] at * <;>
      split_ifs <;> omega
  have hwithin : offset - treeLevelBase level.val = position * 17 + 16 := by
    dsimp [offset]
    omega
  have h := graphNode_owner a ⟨offset, hoffset⟩
  simp only [Fin.val_mk, if_neg houtside, hlevel, hwithin] at h
  have hpoint : (position * 17 + 16) % 17 = 16 := by omega
  simp only [hpoint] at h
  norm_num at h
  simpa only [treeJoin, offset, Nat.add_assoc] using h

set_option maxHeartbeats 2000000 in
theorem graphNode_edge (a : OwnerAddress) (level : Depth) (childPosition : Nat)
    (hchildPosition : childPosition < 2 ^ (5 - level.val)) (step : Fin 8) :
    let idx := edgePointVertex a.bucket.val a.layer.val a.owner.val level.val
      childPosition (step.val + 1)
    graphNode idx = .unary (if step.val = 0 then
      treeChild a.bucket.val a.layer.val a.owner.val level.val childPosition
      else idx - 1) := by
  have hs := step.isLt
  have hside : childPosition % 2 < 2 := Nat.mod_lt _ (by decide)
  have hhalf : childPosition / 2 < 2 ^ (4 - level.val) := by
    fin_cases level <;> norm_num at * <;> omega
  let offset := treeLevelBase level.val + (childPosition / 2) * 17 +
    (childPosition % 2) * 8 + step.val
  have hoffset : offset < 847 := by
    dsimp [offset]
    fin_cases level <;> norm_num [treeLevelBase] at * <;> omega
  have houtside : ¬offset < 320 := by
    dsimp [offset]
    fin_cases level <;> norm_num [treeLevelBase] <;> omega
  have hlevel : ownerTreeLevel offset = level.val := by
    dsimp [offset]
    fin_cases level <;> norm_num [treeLevelBase, ownerTreeLevel] at * <;>
      split_ifs <;> omega
  have hwithin : offset - treeLevelBase level.val =
      (childPosition / 2) * 17 + (childPosition % 2) * 8 + step.val := by
    dsimp [offset]
    omega
  have hpoint : (offset - treeLevelBase level.val) % 17 =
      (childPosition % 2) * 8 + step.val := by rw [hwithin]; omega
  have hposition : (offset - treeLevelBase level.val) / 17 = childPosition / 2 := by
    rw [hwithin]; omega
  have hpointlt : (childPosition % 2) * 8 + step.val < 16 := by omega
  have hstep : ((childPosition % 2) * 8 + step.val) % 8 = step.val := by omega
  have hchild : (childPosition / 2) * 2 +
      ((childPosition % 2) * 8 + step.val) / 8 = childPosition := by omega
  have hidx : edgePointVertex a.bucket.val a.layer.val a.owner.val level.val
      childPosition (step.val + 1) =
        ownerBase a.bucket.val a.layer.val a.owner.val + offset := by
    simp only [edgePointVertex, Nat.succ_ne_zero, ↓reduceIte]
    dsimp [offset]
    omega
  have h := graphNode_owner a ⟨offset, hoffset⟩
  simp only [Fin.val_mk, if_neg houtside, hlevel, hpoint, hposition,
    if_pos hpointlt, hstep, hchild] at h
  rw [hidx]
  split_ifs <;> simp_all

theorem graphNode_edge_suffix (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (hchildPosition : childPosition < 2 ^ (5 - level.val))
    (point : Fin 9) (hpositive : 0 < point.val) :
    graphNode (edgePointVertex a.bucket.val a.layer.val a.owner.val level.val
      childPosition point.val) =
      .unary (edgePointVertex a.bucket.val a.layer.val a.owner.val level.val
        childPosition (point.val - 1)) := by
  let step : Fin 8 := ⟨point.val - 1, by have := point.isLt; omega⟩
  have hstep : step.val + 1 = point.val := by dsimp [step]; omega
  have h := graphNode_edge a level childPosition hchildPosition step
  rw [hstep] at h
  by_cases hz : step.val = 0
  · have hp : point.val = 1 := by omega
    simpa [hz, hp, edgePointVertex] using h
  · simp only [if_neg hz] at h
    have hp : ¬point.val - 1 = 0 := by dsimp [step] at hz; omega
    have hparent :
        edgePointVertex a.bucket.val a.layer.val a.owner.val level.val
          childPosition point.val - 1 =
        edgePointVertex a.bucket.val a.layer.val a.owner.val level.val
          childPosition (point.val - 1) := by
      simp only [edgePointVertex, if_neg (by omega : ¬point.val = 0), if_neg hp]
      omega
    simpa only [hparent] using h

theorem graphNode_treeJoin_endpoints (a : OwnerAddress) (level : Depth)
    (position : Nat) (hposition : position < 2 ^ (4 - level.val)) :
    graphNode (treeJoin a.bucket.val a.layer.val a.owner.val level.val position) =
      .binary
        (edgePointVertex a.bucket.val a.layer.val a.owner.val level.val (2 * position) 8)
        (edgePointVertex a.bucket.val a.layer.val a.owner.val level.val (2 * position + 1) 8) := by
  have h := graphNode_treeJoin a level position hposition
  have hleft : treeJoin a.bucket.val a.layer.val a.owner.val level.val position - 9 =
      edgePointVertex a.bucket.val a.layer.val a.owner.val level.val (2 * position) 8 := by
    simp only [treeJoin, edgePointVertex]
    norm_num
    omega
  have hright : treeJoin a.bucket.val a.layer.val a.owner.val level.val position - 1 =
      edgePointVertex a.bucket.val a.layer.val a.owner.val level.val (2 * position + 1) 8 := by
    simp only [treeJoin, edgePointVertex]
    norm_num
    omega
  simpa only [hleft, hright] using h

theorem graphNode_childRoot (bucket : Bucket) :
    graphNode (childRoot bucket.val) =
      .binary (ownerRoot bucket.val 6 0) (ownerRoot bucket.val 6 1) := by
  have hb := bucket.isLt
  have hi : childRoot bucket.val < 2629104 := by unfold childRoot; omega
  have hdiv : childRoot bucket.val / 164319 = bucket.val := by
    unfold childRoot; omega
  have hmod : childRoot bucket.val % 164319 = 164318 := by
    unfold childRoot; omega
  simp only [graphNode, if_pos hi, hdiv, hmod]
  norm_num

set_option maxHeartbeats 1000000 in
theorem graphNode_bucketJoin (level : Fin 4) (position : Nat)
    (hposition : position < 2 ^ (3 - level.val)) :
    graphNode (bucketJoin level.val position) =
      .binary (bucketTreeChild level.val (2 * position))
        (bucketTreeChild level.val (2 * position + 1)) := by
  have hi : ¬bucketJoin level.val position < 2629104 := by
    fin_cases level <;> norm_num [bucketJoin, bucketLevelBase] <;> omega
  have hlevel : outerTreeLevel (bucketJoin level.val position - 2629104) =
      level.val := by
    fin_cases level <;>
      norm_num [bucketJoin, bucketLevelBase, outerTreeLevel] at * <;>
      split_ifs <;> omega
  have hpos : bucketJoin level.val position - bucketLevelBase level.val =
      position := by unfold bucketJoin; omega
  simp only [graphNode, if_neg hi, hlevel, hpos]

/-- The unary guard suffix followed by the guarded leaf operation. -/
def Route.guardWork (r : Route) (layer : Layer) : List Nat :=
  let e := ((r.code layer).depth ⟨5, by decide⟩).val
  (List.range (e + 1)).map (fun step =>
    ownerBase r.bucket.val layer.val (r.owner layer) +
      (r.slot layer).val * 10 + (9 - e + step))

/-- Hashes for both child edges and their join at one selected tree level.
The selected edge always requires all eight steps; only the sibling edge has
a code-selected suffix. -/
def Route.levelWork (r : Route) (layer : Layer) (level : Depth) : List Nat :=
  let childPosition := (r.slot layer).val / 2 ^ level.val
  let depth : CodePosition := ⟨4 - level.val, by omega⟩
  let e := ((r.code layer).depth depth).val
  ((List.range 8).map (fun step =>
    edgePointVertex r.bucket.val layer.val (r.owner layer)
      level.val childPosition (step + 1))) ++
  ((List.range e).map (fun step =>
    edgePointVertex r.bucket.val layer.val (r.owner layer)
      level.val (childPosition ^^^ 1) (9 - e + step))) ++
  [treeJoin r.bucket.val layer.val (r.owner layer)
    level.val (childPosition / 2)]

def Route.layerWork (r : Route) (layer : Layer) : List Nat :=
  r.guardWork layer ++ ((List.finRange 5).flatMap (r.levelWork layer))

/-- An explicit honest reconstruction schedule. The protected verifier scans
the same vertices in global topological order, selected by `Route.plan`. -/
def Route.recovery (r : Route) : List Nat :=
  ((List.finRange 7).flatMap r.layerWork) ++ [childRoot r.bucket.val] ++
    ((List.range 4).map (fun level =>
      bucketJoin level (r.bucket.val / 2 ^ (level + 1))))

@[irreducible] def Route.plan (r : Route) : List Bool := addressMask graphNodes r.recovery

theorem plan_eq (r : Route) : r.plan = addressMask graphNodes r.recovery := by
  unfold Route.plan
  rfl

theorem frontier_length (r : Route) : r.frontier.length = graphNodes := by
  exact (congrArg List.length (frontier_eq r)).trans (addressMask_length _ _)

theorem plan_length (r : Route) : r.plan.length = graphNodes := by
  exact (congrArg List.length (plan_eq r)).trans (addressMask_length _ _)

theorem frontier_get (r : Route) (i : Nat) (hi : i < graphNodes) :
    get r.frontier i = decide (i ∈ r.disclosure) :=
  (congrArg (fun xs => get xs i) (frontier_eq r)).trans (addressMask_get _ _ _ hi)

theorem plan_get (r : Route) (i : Nat) (hi : i < graphNodes) :
    get r.plan i = decide (i ∈ r.recovery) :=
  (congrArg (fun xs => get xs i) (plan_eq r)).trans (addressMask_get _ _ _ hi)

theorem guardWork_length (r : Route) (layer : Layer) :
    (r.guardWork layer).length =
      ((r.code layer).depth ⟨5, by decide⟩).val + 1 := by
  simp [Route.guardWork]

theorem levelWork_length (r : Route) (layer : Layer) (level : Depth) :
    (r.levelWork layer level).length =
      9 + ((r.code layer).depth ⟨4 - level.val, by omega⟩).val := by
  simp [Route.levelWork]
  omega

theorem layerDisclosure_length (r : Route) (layer : Layer) :
    (r.layerDisclosure layer).length = 6 := by
  simp [Route.layerDisclosure]

theorem disclosure_length (r : Route) : r.disclosure.length = 47 := by
  simp [Route.disclosure, Route.bucketSiblings, List.length_flatMap,
    layerDisclosure_length, Route.initialSibling, List.finRange_succ]

/-- Turning a list of addressed disclosures into the model mask cannot add
words; repeated addresses would reduce the number of transmitted vertices. -/
theorem mask_weight_le (n : Nat) (addresses : List Nat) :
    weight ((List.range n).map (fun v => decide (v ∈ addresses))) ≤
      addresses.length := by
  let selected := (List.range n).filter (fun v => decide (v ∈ addresses))
  have hnodup : selected.Nodup := List.Nodup.filter _ List.nodup_range
  have hsubset : selected.toFinset ⊆ addresses.toFinset := by
    intro v hv
    have hmem : v ∈ selected := List.mem_toFinset.mp hv
    have hvaddr := (List.mem_filter.mp hmem).2
    exact List.mem_toFinset.mpr (of_decide_eq_true hvaddr)
  have hweight :
      weight ((List.range n).map (fun v => decide (v ∈ addresses))) =
        selected.length := by
    unfold weight
    rw [List.count_eq_countP, List.countP_map]
    simp only [Function.comp_def]
    have heq : (fun x => decide (x ∈ addresses) == true) =
        (fun x => decide (x ∈ addresses)) := by
      funext x
      cases decide (x ∈ addresses) <;> rfl
    rw [heq]
    rw [List.countP_eq_length_filter]
  rw [hweight, ← List.toFinset_card_of_nodup hnodup]
  exact (Finset.card_le_card hsubset).trans addresses.toFinset_card_le

theorem frontier_weight_le (r : Route) : weight r.frontier ≤ 47 := by
  have hgeneric (n : Nat) (addresses : List Nat) : weight (addressMask n addresses) ≤ addresses.length :=
    mask_weight_le n addresses
  calc
    weight r.frontier = weight (addressMask graphNodes r.disclosure) := congrArg weight (frontier_eq r)
    _ ≤ r.disclosure.length := hgeneric _ _
    _ = 47 := disclosure_length r

theorem plan_weight_le (r : Route) : weight r.plan ≤ r.recovery.length := by
  have hgeneric (n : Nat) (addresses : List Nat) : weight (addressMask n addresses) ≤ addresses.length :=
    mask_weight_le n addresses
  calc
    weight r.plan = weight (addressMask graphNodes r.recovery) := congrArg weight (plan_eq r)
    _ ≤ r.recovery.length := hgeneric _ _

end PoissonDAG.GRSCC
