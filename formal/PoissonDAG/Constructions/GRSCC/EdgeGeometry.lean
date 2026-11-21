import PoissonDAG.Constructions.GRSCC.Covering
import PoissonDAG.Constructions.GRSCC.Kernel
import Mathlib.Data.Nat.Bitwise

set_option maxHeartbeats 50000
set_option maxRecDepth 100000

/-!
# Local addressed geometry and supplier classifications

This module owns literal private barrier membership and scalar divergence
classification. No covering bound or caller-supplied security predicate is used.
-/

namespace PoissonDAG.GRSCC

/-- Relative owner coordinates used for bounded geometry replay. Translation
to arbitrary addressed owners remains an explicit algebraic bridge. -/
def localOwner : OwnerAddress where
  bucket := 0
  layer := 0
  owner := ⟨0, by decide⟩

@[simp] theorem localOwner_bucket_val : localOwner.bucket.val = 0 := rfl
@[simp] theorem localOwner_layer_val : localOwner.layer.val = 0 := rfl
@[simp] theorem localOwner_owner_val : localOwner.owner.val = 0 := rfl

@[simp] theorem localOwner_base :
    ownerBase localOwner.bucket.val localOwner.layer.val localOwner.owner.val = 0 := rfl

theorem xor_one_eq_mod (n : Nat) : n ^^^ 1 = n + 1 - 2 * (n % 2) := by
  by_cases he : n % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr he), he]
    omega
  · have ho : n % 2 = 1 := by omega
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr ho), ho]
    omega

private theorem xor_one_iff_div_ne (a b : Nat) :
    b = a ^^^ 1 ↔ b / 2 = a / 2 ∧ b ≠ a := by
  rw [xor_one_eq_mod]
  constructor <;> intro h <;> omega

def localAuthOpening (slot : Slot) (depth : Depth) (point : Fin 9) : Nat :=
  let level := 4 - depth.val
  edgePointVertex 0 0 0 level ((slot.val / 2 ^ level) ^^^ 1) point.val

def localSiblingBarrier (slot : Slot) (depth : Depth) (point : Fin 9) : Nat → Prop :=
  let level : Depth := ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
  privateEdgeBarrier localOwner level ((slot.val / 2 ^ level.val) ^^^ 1) point

instance localSiblingBarrier_decidable (slot : Slot) (depth : Depth) (point : Fin 9)
    (i : Nat) : Decidable (localSiblingBarrier slot depth point i) := by
  unfold localSiblingBarrier
  infer_instance

theorem guardPrefix_translate (a : OwnerAddress) (slot : Slot) (point : Fin 9) (i : Nat) :
    guardPrefix a slot point
      (ownerBase a.bucket.val a.layer.val a.owner.val + i) ↔
      guardPrefix localOwner slot point i := by
  dsimp [guardPrefix, guardStart, localOwner, ownerBase]
  omega

theorem treeJoin_translate (a : OwnerAddress) (level position : Nat) :
    treeJoin a.bucket.val a.layer.val a.owner.val level position =
      ownerBase a.bucket.val a.layer.val a.owner.val + treeJoin 0 0 0 level position := by
  simp [treeJoin, ownerBase, Nat.add_assoc]

theorem treeChild_translate (a : OwnerAddress) (level position : Nat) :
    treeChild a.bucket.val a.layer.val a.owner.val level position =
      ownerBase a.bucket.val a.layer.val a.owner.val + treeChild 0 0 0 level position := by
  unfold treeChild
  split <;> simp [leafVertex, treeJoin, ownerBase, Nat.add_assoc]

theorem edgePointVertex_translate (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) :
    edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition point.val =
      ownerBase a.bucket.val a.layer.val a.owner.val +
        edgePointVertex 0 0 0 level.val childPosition point.val := by
  by_cases hp : point.val = 0
  · simp only [edgePointVertex, hp, ↓reduceIte]
    exact treeChild_translate a level.val childPosition
  · have ht : 0 < treeLevelBase level.val := by fin_cases level <;> decide
    simp only [edgePointVertex, if_neg hp]
    have hz : ownerBase 0 0 0 = 0 := rfl
    rw [hz]
    omega

theorem leafBarrier_translate (a : OwnerAddress) (slot : Slot) (i : Nat) :
    leafBarrier a slot (ownerBase a.bucket.val a.layer.val a.owner.val + i) ↔
      leafBarrier localOwner slot i := by
  unfold leafBarrier
  rw [guardPrefix_translate]
  simp [leafVertex, localOwner, ownerBase, Nat.add_assoc]

theorem edgePrefixBarrier_translate (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) (left right : Nat → Prop)
    (hbase : ∀ i, left (ownerBase a.bucket.val a.layer.val a.owner.val + i) ↔ right i)
    (i : Nat) :
    edgePrefixBarrier a level childPosition point left
      (ownerBase a.bucket.val a.layer.val a.owner.val + i) ↔
      edgePrefixBarrier localOwner level childPosition point right i := by
  simp only [edgePrefixBarrier, hbase]
  apply or_congr Iff.rfl
  apply exists_congr
  intro k
  rw [edgePointVertex_translate a level childPosition k]
  simp [localOwner, Nat.add_left_cancel_iff]

theorem privateSubtreeBarrier_translate (a : OwnerAddress) (height position i : Nat) :
    privateSubtreeBarrier a height position
      (ownerBase a.bucket.val a.layer.val a.owner.val + i) ↔
      privateSubtreeBarrier localOwner height position i := by
  induction height generalizing position i with
  | zero =>
      unfold privateSubtreeBarrier
      split
      · exact leafBarrier_translate a _ i
      · rfl
  | succ height ih =>
      unfold privateSubtreeBarrier
      split
      · rename_i hh
        dsimp only
        rw [treeJoin_translate a height position]
        simp only [localOwner, Fin.val_mk, Nat.add_left_cancel_iff]
        apply or_congr Iff.rfl
        apply or_congr
        · exact edgePrefixBarrier_translate a ⟨height, hh⟩ (2 * position) ⟨8, by decide⟩
            _ _ (fun i => ih (2 * position) i) i
        · exact edgePrefixBarrier_translate a ⟨height, hh⟩ (2 * position + 1) ⟨8, by decide⟩
            _ _ (fun i => ih (2 * position + 1) i) i
      · rfl

theorem privateEdgeBarrier_translate (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) (i : Nat) :
    privateEdgeBarrier a level childPosition point
      (ownerBase a.bucket.val a.layer.val a.owner.val + i) ↔
      privateEdgeBarrier localOwner level childPosition point i := by
  exact edgePrefixBarrier_translate a level childPosition point _ _
    (fun i => privateSubtreeBarrier_translate a level.val childPosition i) i

private theorem interval_offset (base i : Nat) (h : base ≤ i ∧ i < base + 847) :
    i - base < 847 ∧ base + (i - base) = i := by omega

private theorem owner_fields_at (a : OwnerAddress) (i : Nat)
    (hi : ownerBase a.bucket.val a.layer.val a.owner.val ≤ i ∧
      i < ownerBase a.bucket.val a.layer.val a.owner.val + 847) :
    i / 164319 = a.bucket.val ∧ (i % 164319 / 847) / 32 = a.layer.val ∧
      (i % 164319 / 847) % 32 = a.owner.val := by
  have hoff := interval_offset _ i hi
  let offset : Fin 847 := ⟨i - ownerBase a.bucket.val a.layer.val a.owner.val, hoff.1⟩
  have heq : ownerBase a.bucket.val a.layer.val a.owner.val + offset.val = i := hoff.2
  have h := ownerIndex_fields a offset
  simp only [heq] at h
  exact ⟨h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem owner_intervals_disjoint (a b : OwnerAddress) (i : Nat)
    (ha : ownerBase a.bucket.val a.layer.val a.owner.val ≤ i ∧
      i < ownerBase a.bucket.val a.layer.val a.owner.val + 847)
    (hb : ownerBase b.bucket.val b.layer.val b.owner.val ≤ i ∧
      i < ownerBase b.bucket.val b.layer.val b.owner.val + 847) :
    a.bucket.val = b.bucket.val ∧ a.layer.val = b.layer.val ∧
      a.owner.val = b.owner.val := by
  have hfa := owner_fields_at a i ha
  have hfb := owner_fields_at b i hb
  exact ⟨hfa.1.symm.trans hfb.1, hfa.2.1.symm.trans hfb.2.1,
    hfa.2.2.symm.trans hfb.2.2⟩

theorem edgePoint_below_ownerRoot (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (hchild : childPosition < 2 ^ (5 - level.val)) (point : Fin 9) :
    edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition point.val <
      ownerBase a.bucket.val a.layer.val a.owner.val + 846 := by
  have hp := point.isLt
  by_cases hz : point.val = 0
  · simp only [edgePointVertex, if_pos hz]
    fin_cases level <;>
      norm_num [treeChild, leafVertex, treeJoin, treeLevelBase] at * <;> omega
  · simp only [edgePointVertex, if_neg hz]
    fin_cases level <;> norm_num [treeLevelBase] at * <;> omega

theorem treeJoin_below_ownerRoot (a : OwnerAddress) (level : Depth)
    (hlevel : level.val < 4) (position : Nat) (hposition : position < 2 ^ (4 - level.val)) :
    treeJoin a.bucket.val a.layer.val a.owner.val level.val position <
      ownerBase a.bucket.val a.layer.val a.owner.val + 846 := by
  fin_cases level <;> norm_num [treeJoin, treeLevelBase] at * <;> omega

theorem edgePrefixBarrier_below_ownerRoot (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) (base : Nat → Prop)
    (hchild : childPosition < 2 ^ (5 - level.val))
    (hbase : ∀ i, base i → i < ownerBase a.bucket.val a.layer.val a.owner.val + 846)
    (i : Nat) (hi : edgePrefixBarrier a level childPosition point base i) :
    i < ownerBase a.bucket.val a.layer.val a.owner.val + 846 := by
  rcases hi with hb | ⟨k, _, _, rfl⟩
  · exact hbase i hb
  · exact edgePoint_below_ownerRoot a level childPosition hchild k

set_option maxHeartbeats 3000000 in
theorem privateSubtreeBarrier_below_ownerRoot (a : OwnerAddress) (height position : Nat)
    (hh : height ≤ 4) (hp : position < 2 ^ (5 - height)) (i : Nat)
    (hi : privateSubtreeBarrier a height position i) :
    i < ownerBase a.bucket.val a.layer.val a.owner.val + 846 := by
  induction height generalizing position i with
  | zero =>
      have hpos : position < 32 := by simpa using hp
      simp only [privateSubtreeBarrier, dif_pos hpos, leafBarrier] at hi
      rcases hi with rfl | hguard
      · dsimp [leafVertex]
        omega
      · dsimp [guardPrefix, guardStart] at hguard
        omega
  | succ height ih =>
      have hheight : height < 5 := by omega
      let level : Depth := ⟨height, hheight⟩
      have hpos : position < 2 ^ (4 - height) := by
        have hexp : 5 - (height + 1) = 4 - height := by omega
        simpa only [hexp] using hp
      have hleft : 2 * position < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hright : 2 * position + 1 < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      simp only [privateSubtreeBarrier, dif_pos hheight] at hi
      rcases hi with rfl | hleftHit | hrightHit
      · exact treeJoin_below_ownerRoot a level (by dsimp [level]; omega) position hpos
      · exact edgePrefixBarrier_below_ownerRoot a level (2 * position) ⟨8, by decide⟩ _ hleft
          (fun j hj => ih (2 * position) (by omega) hleft j hj) i hleftHit
      · exact edgePrefixBarrier_below_ownerRoot a level (2 * position + 1) ⟨8, by decide⟩ _ hright
          (fun j hj => ih (2 * position + 1) (by omega) hright j hj) i hrightHit

theorem privateEdgeBarrier_below_ownerRoot (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9)
    (hchild : childPosition < 2 ^ (5 - level.val)) (i : Nat)
    (hi : privateEdgeBarrier a level childPosition point i) :
    i < ownerBase a.bucket.val a.layer.val a.owner.val + 846 := by
  exact edgePrefixBarrier_below_ownerRoot a level childPosition point _ hchild
    (fun j hj => privateSubtreeBarrier_below_ownerRoot a level.val childPosition
      (by have hl := level.isLt; omega) hchild j hj) i hi

theorem sibling_child_bound : ∀ (slot : Slot) (depth : Depth),
    ((slot.val / 2 ^ (4 - depth.val)) ^^^ 1) < 2 ^ (5 - (4 - depth.val)) := by
  intro slot depth
  let level := 4 - depth.val
  have hl : level ≤ 4 := by dsimp [level]; omega
  have hexp : (5 - level) + level = 5 := by omega
  have hprefix : slot.val / 2 ^ level < 2 ^ (5 - level) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level)).mpr
    rw [← pow_add, hexp]
    simpa using slot.isLt
  exact Nat.xor_lt_two_pow hprefix (Nat.one_lt_two_pow (by omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000 in
theorem local_guard_prefix_classification : ∀ (target history : Slot)
    (targetPoint historyPoint : Fin 9),
    guardPrefix localOwner target targetPoint (history.val * 10 + historyPoint.val) ↔
      target = history ∧ historyPoint.val ≤ targetPoint.val := by
  intro target history targetPoint historyPoint
  have ht := target.isLt
  have hh := history.isLt
  have hp := targetPoint.isLt
  have hq := historyPoint.isLt
  simp only [guardPrefix, guardStart, localOwner, ownerBase, Fin.val_zero,
    Nat.zero_mul, Nat.zero_add]
  constructor
  · intro h
    have heq : target.val = history.val := by omega
    exact ⟨Fin.ext heq, by omega⟩
  · rintro ⟨rfl, hpoint⟩
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000 in
theorem local_guard_authentication_disjoint : ∀ (target history : Slot)
    (targetPoint : Fin 9) (historyDepth : Depth) (historyPoint : Fin 9),
    ¬guardPrefix localOwner target targetPoint
      (localAuthOpening history historyDepth historyPoint) := by
  intro target history targetPoint historyDepth historyPoint
  have ht := target.isLt
  have hh := history.isLt
  have hp := targetPoint.isLt
  have hq := historyPoint.isLt
  by_cases hz : historyPoint.val = 0 <;> fin_cases historyDepth <;>
    simp [guardPrefix, guardStart, localOwner, ownerBase, localAuthOpening,
      edgePointVertex, treeChild, treeJoin, treeLevelBase, leafVertex, hz] <;>
    omega

theorem edgePoint_positive_lower (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) (hpoint : 0 < point.val) :
    ownerBase a.bucket.val a.layer.val a.owner.val + 320 ≤
      edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition point.val := by
  have hn : point.val ≠ 0 := by omega
  simp only [edgePointVertex, if_neg hn]
  fin_cases level <;> norm_num [treeLevelBase] <;> omega

theorem treeJoin_lower (a : OwnerAddress) (level : Depth) (position : Nat) :
    ownerBase a.bucket.val a.layer.val a.owner.val + 320 ≤
      treeJoin a.bucket.val a.layer.val a.owner.val level.val position := by
  fin_cases level <;> norm_num [treeJoin, treeLevelBase] <;> omega

theorem edgePrefixBarrier_at_guard (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) (base : Nat → Prop) (history : Slot)
    (historyPoint : Fin 9) :
    edgePrefixBarrier a level childPosition point base (guardVertex a history historyPoint) ↔
      base (guardVertex a history historyPoint) := by
  have hs := history.isLt
  have hp := historyPoint.isLt
  constructor
  · rintro (hb | ⟨k, hk, _, heq⟩)
    · exact hb
    · have hlower := edgePoint_positive_lower a level childPosition k (by omega)
      dsimp [guardVertex] at heq
      omega
  · exact Or.inl

set_option maxHeartbeats 3000000 in
theorem privateSubtreeBarrier_at_guard (a : OwnerAddress) (height position : Nat)
    (hh : height ≤ 5) (hp : position < 2 ^ (5 - height)) (history : Slot)
    (historyPoint : Fin 9) :
    privateSubtreeBarrier a height position (guardVertex a history historyPoint) ↔
      history.val / 2 ^ height = position := by
  have hs := history.isLt
  have hpoint := historyPoint.isLt
  induction height generalizing position with
  | zero =>
      have hpos : position < 32 := by simpa using hp
      simp only [privateSubtreeBarrier, dif_pos hpos, leafBarrier, guardPrefix,
        guardStart, guardVertex, leafVertex, pow_zero, Nat.div_one]
      constructor
      · rintro (h | h) <;> omega
      · intro h
        exact Or.inr ⟨by omega, by omega⟩
  | succ height ih =>
      have hheight : height < 5 := by omega
      let level : Depth := ⟨height, hheight⟩
      have hleft : 2 * position < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hright : 2 * position + 1 < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hjoin : guardVertex a history historyPoint ≠
          treeJoin a.bucket.val a.layer.val a.owner.val height position := by
        have hlower := treeJoin_lower a level position
        dsimp [guardVertex, level] at *
        omega
      simp only [privateSubtreeBarrier, dif_pos hheight, hjoin, false_or]
      rw [edgePrefixBarrier_at_guard, edgePrefixBarrier_at_guard]
      have hlaw := ih (2 * position) (by omega) hleft
      have hraw := ih (2 * position + 1) (by omega) hright
      apply (or_congr hlaw hraw).trans
      interval_cases height <;> norm_num <;> omega

theorem sibling_prefix_iff_diverges : ∀ (target history : Slot) (depth : Depth),
    history.val / 2 ^ (4 - depth.val) = ((target.val / 2 ^ (4 - depth.val)) ^^^ 1) ↔
      divergesAt target history depth = true := by
  intro target history depth
  have hd := depth.isLt
  have hexp : 5 - depth.val = (4 - depth.val) + 1 := by omega
  have hdiv (n : Nat) : n / 2 ^ (5 - depth.val) = (n / 2 ^ (4 - depth.val)) / 2 := by
    rw [hexp, pow_succ, Nat.div_div_eq_div_mul]
  simpa only [divergesAt, decide_eq_true_eq, hdiv] using
    xor_one_iff_div_ne (target.val / 2 ^ (4 - depth.val)) (history.val / 2 ^ (4 - depth.val))

theorem local_edge_guard_classification : ∀ (target history : Slot)
    (depth : Depth) (targetPoint historyPoint : Fin 9),
    localSiblingBarrier target depth targetPoint (history.val * 10 + historyPoint.val) ↔
      divergesAt target history depth = true := by
  intro target history depth targetPoint historyPoint
  let level : Depth := ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
  change privateEdgeBarrier localOwner level ((target.val / 2 ^ level.val) ^^^ 1)
    targetPoint (history.val * 10 + historyPoint.val) ↔ _
  have hguard : guardVertex localOwner history historyPoint =
      history.val * 10 + historyPoint.val := by simp [guardVertex, localOwner, ownerBase]
  rw [← hguard]
  rw [privateEdgeBarrier, edgePrefixBarrier_at_guard,
    privateSubtreeBarrier_at_guard localOwner level.val _
      (by have hl := level.isLt; omega) (sibling_child_bound target depth)]
  exact sibling_prefix_iff_diverges target history depth

set_option maxHeartbeats 500000 in
private theorem edgePoint_eq_positive (level otherLevel : Depth) (child otherChild : Nat)
    (hc : child < 2 ^ (5 - level.val)) (hd : otherChild < 2 ^ (5 - otherLevel.val))
    (point otherPoint : Fin 9) (hpositive : 0 < otherPoint.val)
    (heq : edgePointVertex 0 0 0 level.val child point.val =
      edgePointVertex 0 0 0 otherLevel.val otherChild otherPoint.val) :
    level.val = otherLevel.val ∧ child = otherChild ∧ point.val = otherPoint.val := by
  have hp := point.isLt
  have hq := otherPoint.isLt
  have hn : otherPoint.val ≠ 0 := by omega
  have hcm : child % 2 = 0 ∨ child % 2 = 1 := by omega
  have hdm : otherChild % 2 = 0 ∨ otherChild % 2 = 1 := by omega
  by_cases hz : point.val = 0 <;> fin_cases level <;> fin_cases otherLevel <;>
    norm_num [edgePointVertex, treeChild, treeJoin, treeLevelBase, leafVertex,
      ownerBase, hz, hn] at hc hd heq ⊢ <;>
    first | omega | (rcases hcm with hcm | hcm <;> rcases hdm with hdm | hdm <;>
      simp only [hcm, hdm] at heq <;> omega)

set_option maxHeartbeats 500000 in
private theorem edgePoint_eq_join (level joinLevel : Depth) (child position : Nat)
    (hc : child < 2 ^ (5 - level.val)) (hp : position < 2 ^ (4 - joinLevel.val))
    (point : Fin 9)
    (heq : edgePointVertex 0 0 0 level.val child point.val = treeJoin 0 0 0 joinLevel.val position) :
    level.val = joinLevel.val + 1 ∧ point.val = 0 ∧ child = position := by
  have hpoint := point.isLt
  have hcm : child % 2 = 0 ∨ child % 2 = 1 := by omega
  by_cases hz : point.val = 0 <;> fin_cases level <;> fin_cases joinLevel <;>
    norm_num [edgePointVertex, treeChild, treeJoin, treeLevelBase, leafVertex,
      ownerBase, hz] at hc hp heq ⊢ <;>
    first | omega | (rcases hcm with hcm | hcm <;> simp only [hcm] at heq <;> omega)

private theorem edgePoint_in_leaf (level : Depth) (child : Nat)
    (hc : child < 2 ^ (5 - level.val)) (point : Fin 9) (slot : Slot)
    (hhit : leafBarrier localOwner slot (edgePointVertex 0 0 0 level.val child point.val)) :
    level.val = 0 ∧ point.val = 0 ∧ child = slot.val := by
  have hp := point.isLt
  have hs := slot.isLt
  by_cases hz : point.val = 0 <;> fin_cases level <;>
    norm_num [leafBarrier, guardPrefix, guardStart, localOwner, ownerBase,
      edgePointVertex, treeChild, treeJoin, treeLevelBase, leafVertex, hz] at hc hhit ⊢ <;>
    omega

private theorem quotient_parent (value height lower position side : Nat)
    (hle : lower ≤ height) (hside : side ≤ 1)
    (h : value / 2 ^ (height - lower) = 2 * position + side) :
    value / 2 ^ (height + 1 - lower) = position := by
  have he : height + 1 - lower = (height - lower) + 1 := by omega
  rw [he, pow_succ, ← Nat.div_div_eq_div_mul, h]
  omega

set_option maxHeartbeats 500000 in
/-- A private subtree contains exactly lower authentication edges, together
with its own point-zero root. The implication suffices for supplier necessity. -/
private theorem privateSubtree_at_edge (height position : Nat)
    (hh : height ≤ 5) (hp : position < 2 ^ (5 - height))
    (level : Depth) (child : Nat) (hc : child < 2 ^ (5 - level.val)) (point : Fin 9)
    (hhit : privateSubtreeBarrier localOwner height position
      (edgePointVertex 0 0 0 level.val child point.val)) :
    (level.val < height ∧ child / 2 ^ (height - level.val) = position) ∨
      (level.val = height ∧ point.val = 0 ∧ child = position) := by
  induction height generalizing position with
  | zero =>
      have hpos : position < 32 := by simpa using hp
      simp only [privateSubtreeBarrier, dif_pos hpos] at hhit
      exact Or.inr (edgePoint_in_leaf level child hc point ⟨position, hpos⟩ hhit)
  | succ height ih =>
      have hheight : height < 5 := by omega
      let joinLevel : Depth := ⟨height, hheight⟩
      have hpos : position < 2 ^ (4 - height) := by
        have he : 5 - (height + 1) = 4 - height := by omega
        simpa only [he] using hp
      have hleft : 2 * position < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hright : 2 * position + 1 < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hedge (branch : Nat) (hb : branch < 2 ^ (5 - height))
          (hbranch : branch = 2 * position ∨ branch = 2 * position + 1)
          (hit : edgePrefixBarrier localOwner joinLevel branch ⟨8, by decide⟩
            (privateSubtreeBarrier localOwner height branch)
            (edgePointVertex 0 0 0 level.val child point.val)) :
          level.val < height + 1 ∧ child / 2 ^ (height + 1 - level.val) = position := by
        have hbelow : level.val ≤ height ∧ child / 2 ^ (height - level.val) = branch := by
          rcases hit with hbase | ⟨k, hk, _, heq⟩
          · rcases ih branch (by omega) hb hbase with hlow | hroot
            · exact ⟨Nat.le_of_lt hlow.1, hlow.2⟩
            · exact ⟨hroot.1.le, by simpa [hroot.1] using hroot.2.2⟩
          · have h := edgePoint_eq_positive level joinLevel child branch hc hb point k
              (by omega) heq
            exact ⟨by simpa [joinLevel] using h.1.le,
              by simpa [joinLevel, h.1] using h.2.1⟩
        refine ⟨by omega, ?_⟩
        rcases hbranch with rfl | rfl
        · exact quotient_parent child height level.val position 0 hbelow.1 (by omega)
            (by simpa using hbelow.2)
        · exact quotient_parent child height level.val position 1 hbelow.1 (by omega) hbelow.2
      unfold privateSubtreeBarrier at hhit
      simp only [dif_pos hheight] at hhit
      rcases hhit with hjoin | hleftHit | hrightHit
      · have h := edgePoint_eq_join level joinLevel child position hc hpos point hjoin
        exact Or.inr ⟨by simpa [joinLevel] using h.1, h.2⟩
      · exact Or.inl (hedge (2 * position) hleft (Or.inl rfl) hleftHit)
      · exact Or.inl (hedge (2 * position + 1) hright (Or.inr rfl) hrightHit)

private theorem xor_one_prefix_div (value lower upper : Nat) (h : lower < upper) :
    ((value / 2 ^ lower) ^^^ 1) / 2 ^ (upper - lower) = value / 2 ^ upper := by
  rw [Nat.xor_div_two_pow]
  have hone : (1 : Nat) / 2 ^ (upper - lower) = 0 :=
    Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))
  rw [hone, Nat.xor_zero, Nat.div_div_eq_div_mul, ← pow_add]
  rw [show lower + (upper - lower) = upper by omega]

set_option maxHeartbeats 500000 in
theorem local_edge_authentication_classification : ∀ (target history : Slot)
    (depth historyDepth : Depth) (targetPoint historyPoint : Fin 9),
    localSiblingBarrier target depth targetPoint
      (localAuthOpening history historyDepth historyPoint) →
      divergesAt target history depth = true ∨
        (historyDepth = depth ∧
          history.val / 2 ^ (4 - depth.val) = target.val / 2 ^ (4 - depth.val) ∧
          historyPoint.val ≤ targetPoint.val) := by
  intro target history depth historyDepth targetPoint historyPoint hhit
  let level : Depth := ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
  let historyLevel : Depth := ⟨4 - historyDepth.val, by have hd := historyDepth.isLt; omega⟩
  let child := (target.val / 2 ^ level.val) ^^^ 1
  let historyChild := (history.val / 2 ^ historyLevel.val) ^^^ 1
  have hc : child < 2 ^ (5 - level.val) := sibling_child_bound target depth
  have hh : historyChild < 2 ^ (5 - historyLevel.val) := sibling_child_bound history historyDepth
  have matching (hle : historyLevel.val = level.val) (hchild : historyChild = child)
      (hpoint : historyPoint.val ≤ targetPoint.val) :
      historyDepth = depth ∧
        history.val / 2 ^ (4 - depth.val) = target.val / 2 ^ (4 - depth.val) ∧
        historyPoint.val ≤ targetPoint.val := by
    have hd : historyDepth = depth := by
      apply Fin.ext
      have ha := historyDepth.isLt
      have hb := depth.isLt
      dsimp [historyLevel, level] at hle
      omega
    refine ⟨hd, ?_, hpoint⟩
    have hpref : (history.val / 2 ^ (4 - depth.val)) ^^^ 1 =
        (target.val / 2 ^ (4 - depth.val)) ^^^ 1 := by
      simpa only [historyChild, child, historyLevel, level, Fin.val_mk, hd] using hchild
    exact Nat.xor_left_injective (x := 1) hpref
  change edgePrefixBarrier localOwner level child targetPoint
    (privateSubtreeBarrier localOwner level.val child)
    (edgePointVertex 0 0 0 historyLevel.val historyChild historyPoint.val) at hhit
  rcases hhit with hbase | ⟨k, hk, hkt, heq⟩
  · rcases privateSubtree_at_edge level.val child (by have h := level.isLt; omega)
      hc historyLevel historyChild hh historyPoint hbase with hbelow | hroot
    · left
      apply (sibling_prefix_iff_diverges target history depth).mp
      exact (xor_one_prefix_div history.val historyLevel.val level.val hbelow.1).symm.trans hbelow.2
    · right
      exact matching hroot.1 hroot.2.2 (by omega)
  · have hinj := edgePoint_eq_positive historyLevel level historyChild child hh hc
      historyPoint k (by omega) heq
    right
    exact matching hinj.1 hinj.2.1 (by omega)

theorem local_edge_excludes_ownerRoot : ∀ (slot : Slot) (depth : Depth) (point : Fin 9),
    ¬localSiblingBarrier slot depth point 846 := by
  intro slot depth point hhit
  have hbound := privateEdgeBarrier_below_ownerRoot localOwner
    ⟨4 - depth.val, by have hd := depth.isLt; omega⟩
    ((slot.val / 2 ^ (4 - depth.val)) ^^^ 1) point
    (sibling_child_bound slot depth) 846 hhit
  change (846 : Nat) < 846 at hbound
  omega

end PoissonDAG.GRSCC
