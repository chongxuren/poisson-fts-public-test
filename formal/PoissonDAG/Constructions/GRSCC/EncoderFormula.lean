import PoissonDAG.Constructions.GRSCC.Encoding
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Pred

/-!
# Bounded bitvector formula for the literal Boolean encoder

Arithmetic is 256-bit unsigned arithmetic; actual node addresses fit in 22
bits. The sole input is a 170-bit vector. Code-depth predicates are explicit
15,597-entry parameter-table lookups, never a truth table on the 138-bit rank.
Each output mask is a disjunction of enabled addressed entries. Std's verified
bitblaster handles division, modulo, comparison and the Boolean structure.
-/
namespace PoissonDAG.GRSCC.EncoderFormula

set_option maxHeartbeats 20000

open Std.Tactic.BVDecide

abbrev Word := BVExpr 256
abbrev Formula := BVLogicalExpr

def literal (n : Nat) : Word := .const (BitVec.ofNat 256 n)
def add (a b : Word) : Word := .bin a .add b
def mul (a b : Word) : Word := .bin a .mul b
def divide (a : Word) (n : Nat) : Word := .bin a .udiv (literal n)
def modulo (a : Word) (n : Nat) : Word := .bin a .umod (literal n)
def sibling (a : Word) : Word := .bin a .xor (literal 1)
def equal (a b : Word) : Formula := .literal (.bin a .eq b)
def conjoin (a b : Formula) : Formula := .gate .and a b
def disjoin (a b : Formula) : Formula := .gate .or a b
def any (formulas : List Formula) : Formula :=
  formulas.foldr disjoin (.const false)

def raw : BVExpr 170 := .var 0
def rank : Word :=
  .append (.const (BitVec.ofNat 118 0)) (.extract 32 138 raw) (by decide)
def digit (layer : Nat) : Word := modulo (divide rank (coordinateRadix ^ layer)) coordinateRadix
def slot (layer : Nat) : Word := divide (digit layer) codeCardinality
def codeRank (layer : Nat) : Word := modulo (digit layer) codeCardinality
def initialOwner : Word := modulo (divide rank (coordinateRadix ^ 7)) 2
def bucket : Word := modulo (divide rank (2 * coordinateRadix ^ 7)) 16
def owner (layer : Nat) : Word := if layer = 6 then initialOwner else slot (layer + 1)

def accept : Formula :=
  conjoin (.literal (.bin (.extract 0 32 raw) .ult
    (.const (BitVec.ofNat 32 threshold))))
    (.literal (.bin rank .ult (literal encodingCardinality)))

/-- The linear-size parameter table is traversed once when forming a lookup.
Entries are tagged by their canonical lexicographic rank. -/
def depthLookup (layer position : Nat) (predicate : Nat → Bool) : Formula :=
  any ((canonicalBook.zipIdx).map (fun (digits, index) =>
    if predicate (digits[position]?.getD 0) then equal (codeRank layer) (literal index)
    else .const false))

def depthEqual (layer position depth : Nat) : Formula :=
  depthLookup layer position (fun d => decide (d = depth))
def depthAtLeast (layer position depth : Nat) : Formula :=
  depthLookup layer position (fun d => decide (depth ≤ d))

def ownerBase (layer : Nat) : Word :=
  add (mul bucket (literal 164319))
    (mul (add (literal (layer * 32)) (owner layer)) (literal 847))
def leaf (layer : Nat) (position : Word) : Word :=
  add (add (ownerBase layer) (mul position (literal 10))) (literal 9)
def treeJoin (layer level : Nat) (position : Word) : Word :=
  add (add (add (ownerBase layer) (literal (GRSCC.treeLevelBase level)))
    (mul position (literal 17))) (literal 16)
def treeChild (layer level : Nat) (position : Word) : Word :=
  if level = 0 then leaf layer position else treeJoin layer (level - 1) position
def edgePoint (layer level : Nat) (position : Word) (point : Nat) : Word :=
  if point = 0 then treeChild layer level position else
    add (add (add (add (ownerBase layer) (literal (GRSCC.treeLevelBase level)))
      (mul (divide position 2) (literal 17)))
      (mul (modulo position 2) (literal 8))) (literal (point - 1))
def guardPoint (layer point : Nat) : Word :=
  add (add (ownerBase layer) (mul (slot layer) (literal 10))) (literal point)
def initialSibling : Word :=
  add (add (mul bucket (literal 164319))
    (mul (add (literal 192) (sibling initialOwner)) (literal 847))) (literal 846)
def childRoot : Word := add (mul bucket (literal 164319)) (literal 164318)
def bucketJoin (level : Nat) (position : Word) : Word :=
  add (literal (GRSCC.bucketLevelBase level)) position
def bucketChild (level : Nat) (position : Word) : Word :=
  if level = 0 then add (mul position (literal 164319)) (literal 164318)
  else bucketJoin (level - 1) position

abbrev Entry := Formula × Word

def authenticationDisclosures (layer depth : Nat) : List Entry :=
  let level := 4 - depth
  let position := sibling (divide (slot layer) (2 ^ level))
  (List.range 9).map (fun e =>
    (depthEqual layer depth e, edgePoint layer level position (8 - e)))

def layerDisclosures (layer : Nat) : List Entry :=
  ((List.range 9).map (fun e =>
    (depthEqual layer 5 e, guardPoint layer (8 - e)))) ++
  ((List.range 5).flatMap (authenticationDisclosures layer))

def disclosures : List Entry :=
  ((List.range 4).map (fun level =>
    (.const true, bucketChild level (sibling (divide bucket (2 ^ level)))))) ++
  [(.const true, initialSibling)] ++
  ((List.range 7).flatMap layerDisclosures)

def selectedEdgeRecovery (layer level : Nat) : List Entry :=
  let position := divide (slot layer) (2 ^ level)
  (List.range 8).map (fun step =>
    (.const true, edgePoint layer level position (step + 1)))

def siblingEdgeRecovery (layer level : Nat) : List Entry :=
  let position := sibling (divide (slot layer) (2 ^ level))
  (List.range 8).map (fun step =>
    (depthAtLeast layer (4 - level) (8 - step),
      edgePoint layer level position (step + 1)))

def joinRecovery (layer level : Nat) : List Entry :=
  [(.const true, treeJoin layer level (divide (divide (slot layer) (2 ^ level)) 2))]

def levelRecovery (layer level : Nat) : List Entry :=
  selectedEdgeRecovery layer level ++ siblingEdgeRecovery layer level ++ joinRecovery layer level

def layerRecovery (layer : Nat) : List Entry :=
  ((List.range 9).map (fun step =>
    (depthAtLeast layer 5 (8 - step), guardPoint layer (step + 1)))) ++
  ((List.range 5).flatMap (levelRecovery layer))

def recovery : List Entry :=
  ((List.range 7).flatMap layerRecovery) ++ [(.const true, childRoot)] ++
  ((List.range 4).map (fun level =>
    (.const true, bucketJoin level (divide bucket (2 ^ (level + 1))))))

def membership (entries : List Entry) (vertex : Nat) : Formula :=
  any (entries.map (fun (enabled, address) =>
    conjoin enabled (equal address (literal vertex))))

def outputsFor (n : Nat) : List Formula :=
  accept ::
    (((List.range n).map (fun vertex => conjoin accept (membership disclosures vertex))) ++
    ((List.range n).map (fun vertex => conjoin accept (membership recovery vertex))))

@[irreducible] def outputs : List Formula := outputsFor graphNodes

theorem outputs_eq : outputs = outputsFor graphNodes := by unfold outputs; rfl

def assignment (value : Nat) : BVExpr.Assignment :=
  .leaf { w := 170, bv := BitVec.ofNat 170 value }

theorem outputsFor_length (n : Nat) : (outputsFor n).length = 1 + 2 * n := by
  simp [outputsFor]
  omega

theorem outputs_length : outputs.length = 1 + 2 * graphNodes :=
  (congrArg List.length outputs_eq).trans (outputsFor_length graphNodes)

theorem guarded_entry_counts : disclosures.length = 383 ∧ recovery.length = 663 := by
  decide +kernel

theorem eval_any_true (value : Nat) (formulas : List Formula) :
    BVLogicalExpr.eval (assignment value) (any formulas) = true ↔
      ∃ f ∈ formulas, BVLogicalExpr.eval (assignment value) f = true := by
  induction formulas with
  | nil => simp [any, BVLogicalExpr.eval, BoolExpr.eval]
  | cons f fs ih =>
      simp only [any, List.foldr_cons, disjoin, BVLogicalExpr.eval_gate,
        Std.Tactic.BVDecide.Gate.eval, Bool.or_eq_true, List.mem_cons]
      change (_ ∨ BVLogicalExpr.eval (assignment value) (any fs) = true) ↔ _
      rw [ih]
      simp only [or_and_right, exists_or, exists_eq_left]

def wordValue (value : Nat) (expression : Word) : Nat :=
  (expression.eval (assignment value)).toNat

@[simp] theorem literal_value_mod (value n : Nat) :
    wordValue value (literal n) = n % 2 ^ 256 := by rfl

@[simp] theorem add_value_mod (value : Nat) (left right : Word) :
    wordValue value (add left right) =
      (wordValue value left + wordValue value right) % 2 ^ 256 := by rfl

@[simp] theorem mul_value_mod (value : Nat) (left right : Word) :
    wordValue value (mul left right) =
      (wordValue value left * wordValue value right) % 2 ^ 256 := by rfl

theorem sibling_value (value : Nat) (expression : Word) :
    wordValue value (sibling expression) = wordValue value expression ^^^ 1 := by
  simp [wordValue, sibling, literal, BVExpr.eval, BVBinOp.eval]

theorem eval_raw (value : Nat) : raw.eval (assignment value) = BitVec.ofNat 170 value := by
  rfl

theorem rank_value (value : Nat) (hvalue : value < 2 ^ rawBits) :
    wordValue value rank = rawRank value := by
  have hraw : value < 2 ^ 170 := by
    simpa only [rawBits, thresholdBits, rankBits] using hvalue
  have hrank : rawRank value < 2 ^ 138 := by
    unfold rawRank
    norm_num at hraw ⊢
    omega
  change ((BitVec.ofNat 118 0) ++
    BitVec.extractLsb' 32 138 (BitVec.ofNat 170 value)).toNat = rawRank value
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hraw]
  exact Nat.mod_eq_of_lt hrank

theorem literal_value (value n : Nat) (hn : n < 2 ^ 256) :
    wordValue value (literal n) = n := by
  rw [literal_value_mod]
  exact Nat.mod_eq_of_lt hn

theorem divide_value (value : Nat) (expression : Word) (n : Nat)
    (hn : n < 2 ^ 256) :
    wordValue value (divide expression n) = wordValue value expression / n := by
  unfold wordValue divide literal
  simp only [BVExpr.eval, BVBinOp.eval, BitVec.toNat_udiv, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hn]

theorem modulo_value (value : Nat) (expression : Word) (n : Nat)
    (hn : n < 2 ^ 256) :
    wordValue value (modulo expression n) = wordValue value expression % n := by
  unfold wordValue modulo literal
  simp only [BVExpr.eval, BVBinOp.eval, BitVec.toNat_umod, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hn]

theorem add_value (value : Nat) (left right : Word)
    (h : wordValue value left + wordValue value right < 2 ^ 256) :
    wordValue value (add left right) = wordValue value left + wordValue value right := by
  rw [add_value_mod]
  exact Nat.mod_eq_of_lt h

theorem mul_value (value : Nat) (left right : Word)
    (h : wordValue value left * wordValue value right < 2 ^ 256) :
    wordValue value (mul left right) = wordValue value left * wordValue value right := by
  rw [mul_value_mod]
  exact Nat.mod_eq_of_lt h

theorem radix_power_fits (layer : Fin 8) : coordinateRadix ^ layer.val < 2 ^ 256 := by
  fin_cases layer <;>
    norm_num [coordinateRadix, codeCardinality_eq, slotCount, treeHeight]

theorem radix_fits : coordinateRadix < 2 ^ 256 := by
  norm_num [coordinateRadix, codeCardinality_eq, slotCount, treeHeight]

theorem codeCardinality_fits : codeCardinality < 2 ^ 256 := by
  rw [codeCardinality_eq]
  norm_num

theorem digit_value (value : Nat) (hvalue : value < 2 ^ rawBits) (layer : Layer) :
    wordValue value (digit layer.val) =
      rawRank value / coordinateRadix ^ layer.val % coordinateRadix := by
  unfold digit
  rw [modulo_value value _ _ radix_fits,
    divide_value value _ _ (radix_power_fits ⟨layer.val, by have := layer.isLt; omega⟩),
    rank_value value hvalue]

theorem slot_value (value : Nat) (hvalue : value < 2 ^ rawBits) (layer : Layer) :
    wordValue value (slot layer.val) =
      (rawRank value / coordinateRadix ^ layer.val % coordinateRadix) / codeCardinality := by
  unfold slot
  rw [divide_value value _ _ codeCardinality_fits, digit_value value hvalue layer]

theorem codeRank_value (value : Nat) (hvalue : value < 2 ^ rawBits) (layer : Layer) :
    wordValue value (codeRank layer.val) =
      (rawRank value / coordinateRadix ^ layer.val % coordinateRadix) % codeCardinality := by
  unfold codeRank
  rw [modulo_value value _ _ codeCardinality_fits, digit_value value hvalue layer]

theorem initialOwner_value (value : Nat) (hvalue : value < 2 ^ rawBits) :
    wordValue value initialOwner = rawRank value / coordinateRadix ^ 7 % 2 := by
  unfold initialOwner
  rw [modulo_value value _ _ (by norm_num),
    divide_value value _ _ (radix_power_fits ⟨7, by decide⟩), rank_value value hvalue]

theorem bucket_value (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) :
    wordValue value bucket = rawRank value / (2 * coordinateRadix ^ 7) := by
  have hdenom : 2 * coordinateRadix ^ 7 < 2 ^ 256 := by
    norm_num [coordinateRadix, codeCardinality_eq, slotCount, treeHeight]
  unfold bucket
  rw [modulo_value value _ _ (by norm_num), divide_value value _ _ hdenom,
    rank_value value hvalue]
  apply Nat.mod_eq_of_lt
  apply Nat.div_lt_of_lt_mul
  change rawRank value < 32 * coordinateRadix ^ 7 at haccepted
  omega

theorem slot_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) :
    wordValue value (slot layer.val) =
      ((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val := by
  rw [slot_value value hvalue layer]
  rfl

theorem codeRank_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) :
    wordValue value (codeRank layer.val) =
      (decodedCodeRank (routeDigit (rawRank value) layer)).val := by
  rw [codeRank_value value hvalue layer]
  rfl

theorem bucket_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) :
    wordValue value bucket = (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val := by
  rw [bucket_value value hvalue haccepted]
  rfl

theorem initialOwner_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) :
    wordValue value initialOwner =
      (decodedRoute ⟨rawRank value, haccepted⟩).initialOwner.val := by
  rw [initialOwner_value value hvalue]
  rfl

theorem owner_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) :
    wordValue value (owner layer.val) =
      (decodedRoute ⟨rawRank value, haccepted⟩).owner layer := by
  by_cases h : layer.val = 6
  · simp only [owner, if_pos h, Route.owner, dif_pos h]
    exact initialOwner_refines value hvalue haccepted
  · simp only [owner, if_neg h, Route.owner, dif_neg h]
    exact slot_refines value hvalue haccepted ⟨layer.val + 1, by have := layer.isLt; omega⟩

theorem ownerBase_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) :
    wordValue value (ownerBase layer.val) =
      GRSCC.ownerBase (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hb := bucket_refines value hvalue haccepted
  have ho := owner_refines value hvalue haccepted layer
  have hbase : GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) < 2 ^ 256 := by
    have hbf := route.bucket.isLt
    have hof := (route.ownerAddress layer).owner_lt_32
    have hlf := layer.isLt
    dsimp [Route.ownerAddress] at hof
    unfold GRSCC.ownerBase
    norm_num
    omega
  simpa [ownerBase, hb, ho, GRSCC.ownerBase, route] using
    Nat.mod_eq_of_lt hbase

theorem nat_ownerBase_bound (route : Route) (layer : Layer) :
    GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) < 2629104 := by
  have h := (ownerIndex_fields (route.ownerAddress layer) ⟨0, by decide⟩).1
  simpa only [Route.ownerAddress, Nat.add_zero, Fin.val_mk] using h

theorem leaf_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer)
    (position : Word) (n : Nat) (hposition : wordValue value position = n) (hn : n < 32) :
    wordValue value (leaf layer.val position) =
      GRSCC.leafVertex (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) n := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hb := ownerBase_refines value hvalue haccepted layer
  have hbase := nat_ownerBase_bound route layer
  have hfinal : GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) +
      n * 10 + 9 < 2 ^ 256 := by norm_num; omega
  simpa [leaf, hb, hposition, GRSCC.leafVertex, route] using
    Nat.mod_eq_of_lt hfinal

theorem treeJoin_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth)
    (position : Word) (n : Nat) (hposition : wordValue value position = n) (hn : n < 32) :
    wordValue value (treeJoin layer.val level.val position) =
      GRSCC.treeJoin (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) level.val n := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hb := ownerBase_refines value hvalue haccepted layer
  have hbase := nat_ownerBase_bound route layer
  have hlevel : GRSCC.treeLevelBase level.val ≤ 830 := by
    fin_cases level <;> norm_num [GRSCC.treeLevelBase]
  have hfinal : GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) +
      GRSCC.treeLevelBase level.val + n * 17 + 16 < 2 ^ 256 := by norm_num; omega
  simpa [treeJoin, hb, hposition, GRSCC.treeJoin, route] using
    Nat.mod_eq_of_lt hfinal

theorem guardPoint_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer)
    (point : Nat) (hp : point ≤ 9) :
    wordValue value (guardPoint layer.val point) =
      GRSCC.ownerBase (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) +
          ((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val * 10 + point := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hb := ownerBase_refines value hvalue haccepted layer
  have hs := slot_refines value hvalue haccepted layer
  have hbase := nat_ownerBase_bound route layer
  have hslot := (route.slot layer).isLt
  have hfinal : GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) +
      (route.slot layer).val * 10 + point < 2 ^ 256 := by norm_num; omega
  simpa [guardPoint, hb, hs, route] using
    Nat.mod_eq_of_lt hfinal

theorem treeChild_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth)
    (position : Word) (n : Nat) (hposition : wordValue value position = n) (hn : n < 32) :
    wordValue value (treeChild layer.val level.val position) =
      GRSCC.treeChild (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) level.val n := by
  by_cases hz : level.val = 0
  · simpa [treeChild, GRSCC.treeChild, hz] using
      leaf_refines value hvalue haccepted layer position n hposition hn
  · simpa [treeChild, GRSCC.treeChild, hz] using
      treeJoin_refines value hvalue haccepted layer
        ⟨level.val - 1, by have := level.isLt; omega⟩ position n hposition hn

theorem edgePoint_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth)
    (position : Word) (n : Nat) (hposition : wordValue value position = n) (hn : n < 32)
    (point : Fin 9) :
    wordValue value (edgePoint layer.val level.val position point.val) =
      GRSCC.edgePointVertex (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) level.val n point.val := by
  by_cases hz : point.val = 0
  · simpa [edgePoint, GRSCC.edgePointVertex, hz] using
      treeChild_refines value hvalue haccepted layer level position n hposition hn
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hb := ownerBase_refines value hvalue haccepted layer
  have hd := divide_value value position 2 (by norm_num)
  have hm := modulo_value value position 2 (by norm_num)
  rw [hposition] at hd hm
  have hbase := nat_ownerBase_bound route layer
  have hpoint := point.isLt
  have hmod : n % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlevel : GRSCC.treeLevelBase level.val ≤ 830 := by
    fin_cases level <;> norm_num [GRSCC.treeLevelBase]
  have hfinal : GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) +
      GRSCC.treeLevelBase level.val + (n / 2) * 17 + (n % 2) * 8 + (point.val - 1) <
        2 ^ 256 := by norm_num; omega
  have hmodel : GRSCC.edgePointVertex route.bucket.val layer.val (route.owner layer)
      level.val n point.val =
        GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) +
        GRSCC.treeLevelBase level.val + (n / 2) * 17 + (n % 2) * 8 + (point.val - 1) := by
    simp only [GRSCC.edgePointVertex, if_neg hz]
    omega
  rw [show GRSCC.edgePointVertex (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val
    layer.val ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) level.val n point.val =
      _ from hmodel]
  simpa [edgePoint, hz, hb, hd, hm, route] using
    Nat.mod_eq_of_lt hfinal

theorem initialSibling_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) :
    wordValue value initialSibling =
      (decodedRoute ⟨rawRank value, haccepted⟩).initialSibling := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hb := bucket_refines value hvalue haccepted
  have ho := initialOwner_refines value hvalue haccepted
  have hs : route.initialOwner.val ^^^ 1 < 2 := by
    have h := route.initialOwner.isLt
    by_cases hz : route.initialOwner.val = 0
    · simp [hz]
    · have hone : route.initialOwner.val = 1 := by omega
      simp [hone]
  have hbf := route.bucket.isLt
  have hfinal : route.bucket.val * 164319 +
      (192 + (route.initialOwner.val ^^^ 1)) * 847 + 846 < 2 ^ 256 := by
    norm_num
    omega
  simpa [initialSibling, sibling_value, hb, ho, Route.initialSibling,
    GRSCC.ownerRoot, GRSCC.ownerBase, route] using
    Nat.mod_eq_of_lt hfinal

theorem childRoot_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) :
    wordValue value childRoot = GRSCC.childRoot
      (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hb := bucket_refines value hvalue haccepted
  have hbf := route.bucket.isLt
  have hfinal : route.bucket.val * 164319 + 164318 < 2 ^ 256 := by norm_num; omega
  simpa [childRoot, hb, GRSCC.childRoot, route] using
    Nat.mod_eq_of_lt hfinal

theorem bucketJoin_refines (value : Nat) (level : Fin 4) (position : Word)
    (n : Nat) (hposition : wordValue value position = n) (hn : n < 16) :
    wordValue value (bucketJoin level.val position) = GRSCC.bucketJoin level.val n := by
  have hbase : GRSCC.bucketLevelBase level.val ≤ 2629118 := by
    fin_cases level <;> norm_num [GRSCC.bucketLevelBase]
  have hfinal : GRSCC.bucketLevelBase level.val + n < 2 ^ 256 := by norm_num; omega
  simpa [bucketJoin, hposition, GRSCC.bucketJoin] using
    Nat.mod_eq_of_lt hfinal

theorem bucketChild_refines (value : Nat) (level : Fin 4) (position : Word)
    (n : Nat) (hposition : wordValue value position = n) (hn : n < 16) :
    wordValue value (bucketChild level.val position) = GRSCC.bucketTreeChild level.val n := by
  by_cases hz : level.val = 0
  · have hfinal : n * 164319 + 164318 < 2 ^ 256 := by norm_num; omega
    simpa [bucketChild, hz, hposition, GRSCC.bucketTreeChild, GRSCC.childRoot] using
      Nat.mod_eq_of_lt hfinal
  · simpa [bucketChild, GRSCC.bucketTreeChild, hz] using
      bucketJoin_refines value ⟨level.val - 1, by have := level.isLt; omega⟩
        position n hposition hn

theorem accept_refines (value : Nat) (hvalue : value < 2 ^ rawBits) :
    BVLogicalExpr.eval (assignment value) accept = rawAccept value := by
  have hraw : value < 2 ^ 170 := by
    simpa only [rawBits, thresholdBits, rankBits] using hvalue
  have hy : ((BVExpr.extract 0 32 raw).eval (assignment value)).toNat =
      rawThreshold value := by
    simp [eval_raw, rawThreshold, Nat.mod_eq_of_lt hraw]
  have hz := rank_value value hvalue
  change (rank.eval (assignment value)).toNat = rawRank value at hz
  have hU : encodingCardinality < 2 ^ 256 :=
    lt_of_le_of_lt fixed_encoder.2.2.2 (by norm_num [rankBits])
  have hdelta : threshold < 2 ^ 32 := by decide
  change (decide (((BVExpr.extract 0 32 raw).eval (assignment value)).toNat <
      threshold % 2 ^ 32) &&
    decide (wordValue value rank < encodingCardinality % 2 ^ 256)) =
      decide (rawThreshold value < threshold ∧ rawRank value < encodingCardinality)
  rw [hy, rank_value value hvalue, Nat.mod_eq_of_lt hdelta, Nat.mod_eq_of_lt hU]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem eval_equal_literal_true (value : Nat) (expression : Word)
    (n : Nat) (hn : n < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value) (equal expression (literal n)) = true ↔
      wordValue value expression = n := by
  change ((expression.eval (assignment value)) == BitVec.ofNat 256 n) = true ↔
    wordValue value expression = n
  simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hn]
  rfl

theorem eval_depthLookup (value layer position : Nat) (predicate : Nat → Bool)
    (q : Fin codeCardinality) (hq : wordValue value (codeRank layer) = q.val) :
    BVLogicalExpr.eval (assignment value) (depthLookup layer position predicate) =
      predicate ((decodedDigits q)[position]?.getD 0) := by
  apply Bool.eq_iff_iff.mpr
  change (_ = true) ↔ (_ = true)
  rw [depthLookup, eval_any_true]
  constructor
  · intro h
    obtain ⟨formula, hformula, htrue⟩ := h
    obtain ⟨⟨digits, index⟩, hentry, rfl⟩ := List.mem_map.mp hformula
    have hindex : index < canonicalBook.length := by
      have hg := List.mk_mem_zipIdx_iff_getElem?.mp hentry
      exact (List.getElem?_eq_some_iff.mp hg).choose
    have hn : index < 2 ^ 256 := by
      rw [canonicalBook_length, codeCardinality_eq] at hindex
      norm_num at hindex ⊢
      omega
    change BVLogicalExpr.eval (assignment value)
      (if predicate (digits[position]?.getD 0) then equal (codeRank layer) (literal index)
        else .const false) = true at htrue
    split_ifs at htrue with hp
    · have hi := (eval_equal_literal_true value (codeRank layer) index hn).mp htrue
      have hieq : index = q.val := by omega
      have hdigits : digits = decodedDigits q := by
        have hg := List.mk_mem_zipIdx_iff_getElem?.mp hentry
        rw [hieq] at hg
        obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hg
        exact hget.symm
      simpa only [hdigits] using hp
    · simp [BVLogicalExpr.eval, BoolExpr.eval] at htrue
  · intro hp
    let digits := decodedDigits q
    have hentry : (digits, q.val) ∈ canonicalBook.zipIdx := by
      apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simp [digits, decodedDigits, canonicalBook_length, q.isLt]
    refine ⟨_, List.mem_map.mpr ⟨(digits, q.val), hentry, rfl⟩, ?_⟩
    have hn : q.val < 2 ^ 256 := q.isLt.trans codeCardinality_fits
    simp only [show predicate (digits[position]?.getD 0) = true from hp, ↓reduceIte]
    exact (eval_equal_literal_true value (codeRank layer) q.val hn).mpr hq

theorem depthLookup_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer)
    (position : CodePosition) (predicate : Nat → Bool) :
    BVLogicalExpr.eval (assignment value)
      (depthLookup layer.val position.val predicate) =
      predicate ((((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth position).val) := by
  let q := decodedCodeRank (routeDigit (rawRank value) layer)
  have hq : wordValue value (codeRank layer.val) = q.val :=
    codeRank_refines value hvalue haccepted layer
  have h := eval_depthLookup value layer.val position.val predicate q hq
  simpa [decodedRoute, decodedCodeword, decodedDepth,
    (decodedDigits_sound q).1, position.isLt, q] using h

def enabledAddresses (value : Nat) (entries : List Entry) : List Nat :=
  entries.filterMap (fun (enabled, address) =>
    if BVLogicalExpr.eval (assignment value) enabled then
      some (wordValue value address) else none)

theorem mem_enabledAddresses (value : Nat) (entries : List Entry) (vertex : Nat) :
    vertex ∈ enabledAddresses value entries ↔
      ∃ enabled address, (enabled, address) ∈ entries ∧
        BVLogicalExpr.eval (assignment value) enabled = true ∧
          wordValue value address = vertex := by
  simp only [enabledAddresses, List.mem_filterMap]
  constructor
  · rintro ⟨⟨enabled, address⟩, hentry, hsome⟩
    cases he : BVLogicalExpr.eval (assignment value) enabled <;>
      simp [he] at hsome
    exact ⟨enabled, address, hentry, he, hsome⟩
  · rintro ⟨enabled, address, hentry, he, hword⟩
    exact ⟨(enabled, address), hentry, by simp [he, hword]⟩


theorem eval_membership (value : Nat) (entries : List Entry) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value) (membership entries vertex) = true ↔
      vertex ∈ enabledAddresses value entries := by
  rw [membership, eval_any_true, mem_enabledAddresses]
  constructor
  · rintro ⟨formula, hformula, htrue⟩
    obtain ⟨⟨enabled, address⟩, hentry, rfl⟩ := List.mem_map.mp hformula
    have hboth : BVLogicalExpr.eval (assignment value) enabled = true ∧
        BVLogicalExpr.eval (assignment value) (equal address (literal vertex)) = true := by
      simpa only [conjoin, BVLogicalExpr.eval_gate,
        Std.Tactic.BVDecide.Gate.eval, Bool.and_eq_true] using htrue
    exact ⟨enabled, address, hentry, hboth.1,
      (eval_equal_literal_true value address vertex hvertex).mp hboth.2⟩
  · rintro ⟨enabled, address, hentry, he, ha⟩
    refine ⟨conjoin enabled (equal address (literal vertex)),
      List.mem_map.mpr ⟨(enabled, address), hentry, rfl⟩, ?_⟩
    simpa only [conjoin, BVLogicalExpr.eval_gate,
      Std.Tactic.BVDecide.Gate.eval, Bool.and_eq_true] using
      And.intro he ((eval_equal_literal_true value address vertex hvertex).mpr ha)

theorem eval_membership_map {α : Type} (value : Nat) (indices : List α)
    (enabled : α → Formula) (address : α → Word) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (indices.map (fun i => (enabled i, address i))) vertex) = true ↔
      ∃ i ∈ indices, BVLogicalExpr.eval (assignment value) (enabled i) = true ∧
        wordValue value (address i) = vertex := by
  rw [eval_membership value _ vertex hvertex, mem_enabledAddresses]
  constructor
  · rintro ⟨enable, addr, hentry, he, ha⟩
    obtain ⟨i, hi, hpair⟩ := List.mem_map.mp hentry
    cases hpair
    exact ⟨i, hi, he, ha⟩
  · rintro ⟨i, hi, he, ha⟩
    exact ⟨enabled i, address i, List.mem_map.mpr ⟨i, hi, rfl⟩, he, ha⟩

theorem guard_disclosure_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership ((List.range 9).map (fun e =>
        (depthEqual layer.val 5 e, guardPoint layer.val (8 - e)))) vertex) = true ↔
      GRSCC.ownerBase (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) +
          ((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val * 10 +
          (8 - (((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth
            ⟨5, by decide⟩).val) = vertex := by
  rw [eval_membership_map value (List.range 9)
    (fun e => depthEqual layer.val 5 e) (fun e => guardPoint layer.val (8 - e)) vertex hvertex]
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  let depth := ((route.code layer).depth ⟨5, by decide⟩).val
  have hdepth : depth < 9 := ((route.code layer).depth ⟨5, by decide⟩).isLt
  constructor
  · rintro ⟨e, he, henabled, haddress⟩
    have hlookup := depthLookup_refines value hvalue haccepted layer ⟨5, by decide⟩
      (fun d => decide (d = e))
    have hde : depth = e := by
      change BVLogicalExpr.eval (assignment value)
        (depthLookup layer.val 5 (fun d => decide (d = e))) = true at henabled
      rw [hlookup] at henabled
      exact of_decide_eq_true henabled
    rw [guardPoint_refines value hvalue haccepted layer (8 - e) (by omega)] at haddress
    simpa only [route, depth, hde] using haddress
  · intro haddress
    refine ⟨depth, List.mem_range.mpr hdepth, ?_, ?_⟩
    · have hlookup := depthLookup_refines value hvalue haccepted layer ⟨5, by decide⟩
        (fun d => decide (d = depth))
      change BVLogicalExpr.eval (assignment value)
        (depthLookup layer.val 5 (fun d => decide (d = depth))) = true
      rw [hlookup]
      simp [depth, route]
    · rw [guardPoint_refines value hvalue haccepted layer (8 - depth) (by omega)]
      exact haddress

theorem guard_suffix_indices (e : Fin 9) (point : Nat) :
    (∃ step < 9, 8 - step ≤ e.val ∧ step + 1 = point) ↔
      ∃ step < e.val + 1, 9 - e.val + step = point := by
  have he := e.isLt
  constructor
  · rintro ⟨step, hs, hdepth, rfl⟩
    refine ⟨step + 1 - (9 - e.val), by omega, by omega⟩
  · rintro ⟨step, hs, rfl⟩
    refine ⟨9 - e.val + step - 1, by omega, by omega, by omega⟩

theorem edge_suffix_indices (e : Fin 9) (point : Nat) :
    (∃ step < 8, 8 - step ≤ e.val ∧ step + 1 = point) ↔
      ∃ step < e.val, 9 - e.val + step = point := by
  have he := e.isLt
  constructor
  · rintro ⟨step, hs, hdepth, rfl⟩
    refine ⟨step + 1 - (9 - e.val), by omega, by omega⟩
  · rintro ⟨step, hs, rfl⟩
    refine ⟨9 - e.val + step - 1, by omega, by omega, by omega⟩

theorem guard_recovery_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership ((List.range 9).map (fun step =>
        (depthAtLeast layer.val 5 (8 - step), guardPoint layer.val (step + 1)))) vertex) = true ↔
      vertex ∈ (decodedRoute ⟨rawRank value, haccepted⟩).guardWork layer := by
  rw [eval_membership_map value (List.range 9)
    (fun step => depthAtLeast layer.val 5 (8 - step))
    (fun step => guardPoint layer.val (step + 1)) vertex hvertex]
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  let depth := (route.code layer).depth ⟨5, by decide⟩
  constructor
  · rintro ⟨step, hstep, henabled, haddress⟩
    have hs := List.mem_range.mp hstep
    have hlookup := depthLookup_refines value hvalue haccepted layer ⟨5, by decide⟩
      (fun d => decide (8 - step ≤ d))
    change BVLogicalExpr.eval (assignment value)
      (depthLookup layer.val 5 (fun d => decide (8 - step ≤ d))) = true at henabled
    rw [hlookup] at henabled
    have hd : 8 - step ≤ depth.val := of_decide_eq_true henabled
    obtain ⟨j, hj, hpoint⟩ :=
      (guard_suffix_indices depth (step + 1)).mp ⟨step, hs, hd, rfl⟩
    rw [guardPoint_refines value hvalue haccepted layer (step + 1) (by omega)] at haddress
    apply List.mem_map.mpr
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    change GRSCC.ownerBase route.bucket.val layer.val (route.owner layer) +
      (route.slot layer).val * 10 + (9 - depth.val + j) = vertex
    rw [hpoint]
    exact haddress
  · intro haddress
    obtain ⟨j, hj, haddress⟩ := List.mem_map.mp haddress
    have hj' := List.mem_range.mp hj
    obtain ⟨step, hs, hd, hpoint⟩ :=
      (guard_suffix_indices depth (9 - depth.val + j)).mpr ⟨j, hj', rfl⟩
    refine ⟨step, List.mem_range.mpr hs, ?_, ?_⟩
    · have hlookup := depthLookup_refines value hvalue haccepted layer ⟨5, by decide⟩
        (fun d => decide (8 - step ≤ d))
      change BVLogicalExpr.eval (assignment value)
        (depthLookup layer.val 5 (fun d => decide (8 - step ≤ d))) = true
      rw [hlookup]
      exact decide_eq_true hd
    · rw [guardPoint_refines value hvalue haccepted layer (step + 1) (by omega)]
      rw [hpoint]
      exact haddress

theorem selected_depth_address_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer)
    (position : CodePosition) (expression : Nat → Word) (actual : Nat → Nat)
    (hrefines : ∀ e < 9, wordValue value (expression e) = actual e)
    (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership ((List.range 9).map (fun e =>
        (depthEqual layer.val position.val e, expression e))) vertex) = true ↔
      actual ((((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth position).val) =
        vertex := by
  rw [eval_membership_map value (List.range 9)
    (fun e => depthEqual layer.val position.val e) expression vertex hvertex]
  let depth := (((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth position).val
  have hd : depth < 9 :=
    (((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth position).isLt
  constructor
  · rintro ⟨e, he, henabled, haddress⟩
    have hlookup := depthLookup_refines value hvalue haccepted layer position
      (fun d => decide (d = e))
    change BVLogicalExpr.eval (assignment value)
      (depthLookup layer.val position.val (fun d => decide (d = e))) = true at henabled
    rw [hlookup] at henabled
    have hde : depth = e := of_decide_eq_true henabled
    rw [hrefines e (List.mem_range.mp he)] at haddress
    change actual depth = vertex
    rw [hde]
    exact haddress
  · intro haddress
    refine ⟨depth, List.mem_range.mpr hd, ?_, ?_⟩
    · have hlookup := depthLookup_refines value hvalue haccepted layer position
        (fun d => decide (d = depth))
      change BVLogicalExpr.eval (assignment value)
        (depthLookup layer.val position.val (fun d => decide (d = depth))) = true
      rw [hlookup]
      simp [depth]
    · rw [hrefines depth hd]
      exact haddress

theorem pathPosition_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth) :
    wordValue value (divide (slot layer.val) (2 ^ level.val)) =
      ((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val / 2 ^ level.val := by
  rw [divide_value value _ _ (by fin_cases level <;> norm_num),
    slot_refines value hvalue haccepted layer]

theorem sibling_path_lt (route : Route) (layer : Layer) (level : Depth) :
    (((route.slot layer).val / 2 ^ level.val) ^^^ 1) < 32 := by
  have hslot := (route.slot layer).isLt
  have hhalf := sibling_div_two ((route.slot layer).val / 2 ^ level.val)
  have hmod : ((((route.slot layer).val / 2 ^ level.val) ^^^ 1) % 2) < 2 :=
    Nat.mod_lt _ (by decide)
  have hdiv : (route.slot layer).val / 2 ^ level.val ≤ (route.slot layer).val :=
    Nat.div_le_self _ _
  omega

theorem authentication_disclosure_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (depth : Depth)
    (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (authenticationDisclosures layer.val depth.val) vertex) = true ↔
      GRSCC.edgePointVertex (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) (4 - depth.val)
        ((((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val /
          2 ^ (4 - depth.val)) ^^^ 1)
        (8 - (((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth
          ⟨depth.val, by have := depth.isLt; omega⟩).val) = vertex := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  let level : Depth := ⟨4 - depth.val, by omega⟩
  let position := sibling (divide (slot layer.val) (2 ^ level.val))
  let n := ((route.slot layer).val / 2 ^ level.val) ^^^ 1
  have hp : wordValue value position = n := by
    rw [sibling_value, pathPosition_refines value hvalue haccepted layer level]
  have hn : n < 32 := sibling_path_lt route layer level
  apply selected_depth_address_refines value hvalue haccepted layer
    ⟨depth.val, by have := depth.isLt; omega⟩
    (fun e => edgePoint layer.val level.val position (8 - e))
    (fun e => GRSCC.edgePointVertex route.bucket.val layer.val (route.owner layer)
      level.val n (8 - e)) _ vertex hvertex
  intro e he
  exact edgePoint_refines value hvalue haccepted layer level position n hp hn
    ⟨8 - e, by omega⟩

theorem eval_membership_append (value : Nat) (left right : List Entry) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value) (membership (left ++ right) vertex) = true ↔
      BVLogicalExpr.eval (assignment value) (membership left vertex) = true ∨
      BVLogicalExpr.eval (assignment value) (membership right vertex) = true := by
  rw [eval_membership value _ _ hvertex, eval_membership value left _ hvertex,
    eval_membership value right _ hvertex]
  simp [enabledAddresses, List.filterMap_append]

theorem eval_membership_flatMap {α : Type} (value : Nat) (indices : List α)
    (family : α → List Entry) (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value) (membership (indices.flatMap family) vertex) = true ↔
      ∃ i ∈ indices,
        BVLogicalExpr.eval (assignment value) (membership (family i) vertex) = true := by
  induction indices with
  | nil => simp [membership, any, BVLogicalExpr.eval, BoolExpr.eval]
  | cons i indices ih =>
      rw [List.flatMap_cons, eval_membership_append value _ _ vertex hvertex, ih]
      simp only [List.mem_cons]
      simp only [or_and_right, exists_or, exists_eq_left]

theorem layer_disclosures_refine (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (layerDisclosures layer.val) vertex) = true ↔
      vertex ∈ (decodedRoute ⟨rawRank value, haccepted⟩).layerDisclosure layer := by
  rw [layerDisclosures, eval_membership_append value _ _ vertex hvertex,
    guard_disclosure_refines value hvalue haccepted layer vertex hvertex,
    eval_membership_flatMap value _ _ vertex hvertex]
  simp only [Route.layerDisclosure, List.mem_cons, List.mem_map]
  constructor
  · rintro (hguard | ⟨d, hd, hauth⟩)
    · exact Or.inl hguard.symm
    · right
      let depth : Depth := ⟨d, List.mem_range.mp hd⟩
      have h := (authentication_disclosure_refines value hvalue haccepted layer
        depth vertex hvertex).mp hauth
      refine ⟨depth, List.mem_finRange _, ?_⟩
      exact h
  · rintro (hguard | ⟨depth, hd, hauth⟩)
    · exact Or.inl hguard.symm
    · right
      refine ⟨depth.val, List.mem_range.mpr depth.isLt, ?_⟩
      apply (authentication_disclosure_refines value hvalue haccepted layer
        depth vertex hvertex).mpr
      exact hauth

theorem eval_membership_map_true {α : Type} (value : Nat) (indices : List α)
    (address : α → Word) (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (indices.map (fun i => (.const true, address i))) vertex) = true ↔
      ∃ i ∈ indices, wordValue value (address i) = vertex := by
  rw [eval_membership_map value indices (fun _ => .const true) address vertex hvertex]
  simp [BVLogicalExpr.eval, BoolExpr.eval]

theorem eval_membership_single_true (value : Nat) (address : Word) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership [(.const true, address)] vertex) = true ↔
      wordValue value address = vertex := by
  simpa using eval_membership_map_true value [address] id vertex hvertex

theorem bucketSibling_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (level : Fin 4) :
    wordValue value (bucketChild level.val (sibling (divide bucket (2 ^ level.val)))) =
      GRSCC.bucketTreeChild level.val
        (((decodedRoute ⟨rawRank value, haccepted⟩).bucket.val / 2 ^ level.val) ^^^ 1) := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  let n := (route.bucket.val / 2 ^ level.val) ^^^ 1
  have hp : wordValue value (sibling (divide bucket (2 ^ level.val))) = n := by
    rw [sibling_value, divide_value value _ _ (by fin_cases level <;> norm_num),
      bucket_refines value hvalue haccepted]
  have hn : n < 16 := by
    have hb := route.bucket.isLt
    have hdiv : route.bucket.val / 2 ^ level.val ≤ route.bucket.val := Nat.div_le_self _ _
    have hhalf := sibling_div_two (route.bucket.val / 2 ^ level.val)
    have hmod : n % 2 < 2 := Nat.mod_lt _ (by decide)
    dsimp [n] at hmod ⊢
    omega
  exact bucketChild_refines value level _ n hp hn

theorem disclosures_refine (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value) (membership disclosures vertex) = true ↔
      vertex ∈ (decodedRoute ⟨rawRank value, haccepted⟩).disclosure := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hbuckets : BVLogicalExpr.eval (assignment value)
      (membership ((List.range 4).map (fun level =>
        (.const true, bucketChild level (sibling (divide bucket (2 ^ level)))))) vertex) = true ↔
      vertex ∈ route.bucketSiblings := by
    rw [eval_membership_map_true value _ _ vertex hvertex]
    simp only [Route.bucketSiblings, List.mem_map]
    constructor
    · rintro ⟨level, hl, he⟩
      rw [bucketSibling_refines value hvalue haccepted ⟨level, List.mem_range.mp hl⟩] at he
      exact ⟨level, hl, he⟩
    · rintro ⟨level, hl, he⟩
      refine ⟨level, hl, ?_⟩
      rw [bucketSibling_refines value hvalue haccepted ⟨level, List.mem_range.mp hl⟩]
      exact he
  have hinitial : BVLogicalExpr.eval (assignment value)
      (membership [(.const true, initialSibling)] vertex) = true ↔
      vertex ∈ [route.initialSibling] := by
    rw [eval_membership_single_true value _ vertex hvertex,
      initialSibling_refines value hvalue haccepted]
    simp [route, eq_comm]
  have hlayers : BVLogicalExpr.eval (assignment value)
      (membership ((List.range 7).flatMap layerDisclosures) vertex) = true ↔
      vertex ∈ (List.finRange 7).flatMap route.layerDisclosure := by
    rw [eval_membership_flatMap value _ _ vertex hvertex]
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨layer, hl, he⟩
      let l : Layer := ⟨layer, List.mem_range.mp hl⟩
      exact ⟨l, List.mem_finRange _,
        (layer_disclosures_refine value hvalue haccepted l vertex hvertex).mp he⟩
    · rintro ⟨layer, hl, he⟩
      exact ⟨layer.val, List.mem_range.mpr layer.isLt,
        (layer_disclosures_refine value hvalue haccepted layer vertex hvertex).mpr he⟩
  rw [disclosures, eval_membership_append value _ _ vertex hvertex,
    eval_membership_append value _ _ vertex hvertex, hbuckets, hinitial, hlayers]
  simp only [Route.disclosure, List.mem_append]
  rfl

theorem selected_edge_recovery_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth)
    (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (selectedEdgeRecovery layer.val level.val) vertex) = true ↔
      vertex ∈ (List.range 8).map (fun step =>
        GRSCC.edgePointVertex (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
          ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) level.val
          (((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val / 2 ^ level.val)
          (step + 1)) := by
  rw [selectedEdgeRecovery, eval_membership_map_true value _ _ vertex hvertex]
  simp only [List.mem_map]
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  let n := (route.slot layer).val / 2 ^ level.val
  have hp := pathPosition_refines value hvalue haccepted layer level
  have hn : n < 32 := lt_of_le_of_lt (Nat.div_le_self _ _) (route.slot layer).isLt
  constructor
  · rintro ⟨step, hs, he⟩
    have hstep := List.mem_range.mp hs
    rw [edgePoint_refines value hvalue haccepted layer level _ n hp hn
      ⟨step + 1, by omega⟩] at he
    exact ⟨step, hs, he⟩
  · rintro ⟨step, hs, he⟩
    have hstep := List.mem_range.mp hs
    refine ⟨step, hs, ?_⟩
    rw [edgePoint_refines value hvalue haccepted layer level _ n hp hn
      ⟨step + 1, by omega⟩]
    exact he

theorem sibling_edge_recovery_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth)
    (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (siblingEdgeRecovery layer.val level.val) vertex) = true ↔
      vertex ∈ (List.range ((((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth
        ⟨4 - level.val, by omega⟩).val)).map (fun step =>
        GRSCC.edgePointVertex (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
          ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) level.val
          ((((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val / 2 ^ level.val) ^^^ 1)
          (9 - (((decodedRoute ⟨rawRank value, haccepted⟩).code layer).depth
            ⟨4 - level.val, by omega⟩).val + step)) := by
  rw [siblingEdgeRecovery, eval_membership_map value (List.range 8)
    (fun step => depthAtLeast layer.val (4 - level.val) (8 - step)) _ vertex hvertex]
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  let depth := (route.code layer).depth ⟨4 - level.val, by omega⟩
  let n := ((route.slot layer).val / 2 ^ level.val) ^^^ 1
  let position := sibling (divide (slot layer.val) (2 ^ level.val))
  have hp : wordValue value position = n := by
    rw [sibling_value, pathPosition_refines value hvalue haccepted layer level]
  have hn : n < 32 := sibling_path_lt route layer level
  constructor
  · rintro ⟨step, hstep, henabled, haddress⟩
    have hs := List.mem_range.mp hstep
    have hlookup := depthLookup_refines value hvalue haccepted layer
      ⟨4 - level.val, by omega⟩ (fun d => decide (8 - step ≤ d))
    change BVLogicalExpr.eval (assignment value)
      (depthLookup layer.val (4 - level.val) (fun d => decide (8 - step ≤ d))) = true at henabled
    rw [hlookup] at henabled
    have hd : 8 - step ≤ depth.val := of_decide_eq_true henabled
    obtain ⟨j, hj, hpoint⟩ :=
      (edge_suffix_indices depth (step + 1)).mp ⟨step, hs, hd, rfl⟩
    rw [edgePoint_refines value hvalue haccepted layer level position n hp hn
      ⟨step + 1, by omega⟩] at haddress
    apply List.mem_map.mpr
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [hpoint]
    exact haddress
  · intro haddress
    obtain ⟨j, hj, haddress⟩ := List.mem_map.mp haddress
    have hj' := List.mem_range.mp hj
    obtain ⟨step, hs, hd, hpoint⟩ :=
      (edge_suffix_indices depth (9 - depth.val + j)).mpr ⟨j, hj', rfl⟩
    refine ⟨step, List.mem_range.mpr hs, ?_, ?_⟩
    · have hlookup := depthLookup_refines value hvalue haccepted layer
        ⟨4 - level.val, by omega⟩ (fun d => decide (8 - step ≤ d))
      change BVLogicalExpr.eval (assignment value)
        (depthLookup layer.val (4 - level.val) (fun d => decide (8 - step ≤ d))) = true
      rw [hlookup]
      exact decide_eq_true hd
    · rw [edgePoint_refines value hvalue haccepted layer level position n hp hn
        ⟨step + 1, by omega⟩]
      change GRSCC.edgePointVertex route.bucket.val layer.val (route.owner layer)
        level.val n (step + 1) = vertex
      rw [hpoint]
      exact haddress

theorem join_recovery_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth)
    (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (joinRecovery layer.val level.val) vertex) = true ↔
      vertex ∈ [GRSCC.treeJoin (decodedRoute ⟨rawRank value, haccepted⟩).bucket.val layer.val
        ((decodedRoute ⟨rawRank value, haccepted⟩).owner layer) level.val
        ((((decodedRoute ⟨rawRank value, haccepted⟩).slot layer).val / 2 ^ level.val) / 2)] := by
  rw [joinRecovery, eval_membership_single_true value _ vertex hvertex]
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  let n := ((route.slot layer).val / 2 ^ level.val) / 2
  have hp : wordValue value (divide (divide (slot layer.val) (2 ^ level.val)) 2) = n := by
    rw [divide_value value _ _ (by norm_num), pathPosition_refines value hvalue haccepted layer level]
  have hn : n < 32 := by
    have h1 := Nat.div_le_self (route.slot layer).val (2 ^ level.val)
    have h2 := Nat.div_le_self ((route.slot layer).val / 2 ^ level.val) 2
    have hs := (route.slot layer).isLt
    dsimp [n]
    omega
  rw [treeJoin_refines value hvalue haccepted layer level _ n hp hn]
  simp [n, route, eq_comm]

theorem level_recovery_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (level : Depth)
    (vertex : Nat) (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (levelRecovery layer.val level.val) vertex) = true ↔
      vertex ∈ (decodedRoute ⟨rawRank value, haccepted⟩).levelWork layer level := by
  rw [levelRecovery, eval_membership_append value _ _ vertex hvertex,
    eval_membership_append value _ _ vertex hvertex,
    selected_edge_recovery_refines value hvalue haccepted layer level vertex hvertex,
    sibling_edge_recovery_refines value hvalue haccepted layer level vertex hvertex,
    join_recovery_refines value hvalue haccepted layer level vertex hvertex]
  simp only [Route.levelWork, List.mem_append]

theorem layer_recovery_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (layer : Layer) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value)
      (membership (layerRecovery layer.val) vertex) = true ↔
      vertex ∈ (decodedRoute ⟨rawRank value, haccepted⟩).layerWork layer := by
  rw [layerRecovery, eval_membership_append value _ _ vertex hvertex,
    guard_recovery_refines value hvalue haccepted layer vertex hvertex,
    eval_membership_flatMap value _ _ vertex hvertex]
  simp only [Route.layerWork, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (hguard | ⟨level, hl, he⟩)
    · exact Or.inl hguard
    · exact Or.inr ⟨⟨level, List.mem_range.mp hl⟩, List.mem_finRange _,
        (level_recovery_refines value hvalue haccepted layer
          ⟨level, List.mem_range.mp hl⟩ vertex hvertex).mp he⟩
  · rintro (hguard | ⟨level, hl, he⟩)
    · exact Or.inl hguard
    · exact Or.inr ⟨level.val, List.mem_range.mpr level.isLt,
        (level_recovery_refines value hvalue haccepted layer level vertex hvertex).mpr he⟩

theorem recovery_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccepted : rawRank value < encodingCardinality) (vertex : Nat)
    (hvertex : vertex < 2 ^ 256) :
    BVLogicalExpr.eval (assignment value) (membership recovery vertex) = true ↔
      vertex ∈ (decodedRoute ⟨rawRank value, haccepted⟩).recovery := by
  let route := decodedRoute ⟨rawRank value, haccepted⟩
  have hlayers : BVLogicalExpr.eval (assignment value)
      (membership ((List.range 7).flatMap layerRecovery) vertex) = true ↔
      vertex ∈ (List.finRange 7).flatMap route.layerWork := by
    rw [eval_membership_flatMap value _ _ vertex hvertex]
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨layer, hl, he⟩
      let l : Layer := ⟨layer, List.mem_range.mp hl⟩
      exact ⟨l, List.mem_finRange _,
        (layer_recovery_refines value hvalue haccepted l vertex hvertex).mp he⟩
    · rintro ⟨layer, hl, he⟩
      exact ⟨layer.val, List.mem_range.mpr layer.isLt,
        (layer_recovery_refines value hvalue haccepted layer vertex hvertex).mpr he⟩
  have hchild : BVLogicalExpr.eval (assignment value)
      (membership [(.const true, childRoot)] vertex) = true ↔
      vertex ∈ [GRSCC.childRoot route.bucket.val] := by
    rw [eval_membership_single_true value _ vertex hvertex,
      childRoot_refines value hvalue haccepted]
    simp [route, eq_comm]
  have hbuckets : BVLogicalExpr.eval (assignment value)
      (membership ((List.range 4).map (fun level =>
        (.const true, bucketJoin level (divide bucket (2 ^ (level + 1)))))) vertex) = true ↔
      vertex ∈ (List.range 4).map (fun level =>
        GRSCC.bucketJoin level (route.bucket.val / 2 ^ (level + 1))) := by
    rw [eval_membership_map_true value _ _ vertex hvertex]
    simp only [List.mem_map]
    have hword (level : Fin 4) :
        wordValue value (bucketJoin level.val (divide bucket (2 ^ (level.val + 1)))) =
          GRSCC.bucketJoin level.val (route.bucket.val / 2 ^ (level.val + 1)) := by
      have hp : wordValue value (divide bucket (2 ^ (level.val + 1))) =
          route.bucket.val / 2 ^ (level.val + 1) := by
        rw [divide_value value _ _ (by fin_cases level <;> norm_num),
          bucket_refines value hvalue haccepted]
      have hn : route.bucket.val / 2 ^ (level.val + 1) < 16 :=
        lt_of_le_of_lt (Nat.div_le_self _ _) route.bucket.isLt
      exact bucketJoin_refines value level _ _ hp hn
    constructor
    · rintro ⟨level, hl, he⟩
      rw [hword ⟨level, List.mem_range.mp hl⟩] at he
      exact ⟨level, hl, he⟩
    · rintro ⟨level, hl, he⟩
      exact ⟨level, hl, by rw [hword ⟨level, List.mem_range.mp hl⟩]; exact he⟩
  rw [recovery, eval_membership_append value _ _ vertex hvertex,
    eval_membership_append value _ _ vertex hvertex, hlayers, hchild, hbuckets]
  simp only [Route.recovery, List.mem_append]
  rfl

theorem vertex_fits (vertex : Nat) (hvertex : vertex < graphNodes) : vertex < 2 ^ 256 := by
  rw [fixed_geometry.2.2.2.1] at hvertex
  norm_num
  omega

theorem eval_mask_refines_for (n : Nat) (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccept : rawAccept value = true) (entries : List Entry) (addresses : List Nat)
    (hmembership : ∀ vertex < n,
      BVLogicalExpr.eval (assignment value) (membership entries vertex) = true ↔
        vertex ∈ addresses) :
    ((List.range n).map (fun vertex =>
      BVLogicalExpr.eval (assignment value) (conjoin accept (membership entries vertex)))) =
      addressMask n addresses := by
  unfold addressMask
  apply List.map_congr_left
  intro vertex hvertex
  apply Bool.eq_iff_iff.mpr
  change (_ = true) ↔ (_ = true)
  simp only [conjoin, BVLogicalExpr.eval_gate, Std.Tactic.BVDecide.Gate.eval,
    Bool.and_eq_true, accept_refines value hvalue, haccept,
    true_and, decide_eq_true_eq]
  exact hmembership vertex (List.mem_range.mp hvertex)

theorem eval_mask_refines (value : Nat) (hvalue : value < 2 ^ rawBits)
    (haccept : rawAccept value = true) (entries : List Entry) (addresses : List Nat)
    (hmembership : ∀ vertex < graphNodes,
      BVLogicalExpr.eval (assignment value) (membership entries vertex) = true ↔
        vertex ∈ addresses) :
    ((List.range graphNodes).map (fun vertex =>
      BVLogicalExpr.eval (assignment value) (conjoin accept (membership entries vertex)))) =
      addressMask graphNodes addresses :=
  eval_mask_refines_for graphNodes value hvalue haccept entries addresses hmembership

theorem outputsFor_eval (n value : Nat) :
    (outputsFor n).map (BVLogicalExpr.eval (assignment value)) =
      BVLogicalExpr.eval (assignment value) accept ::
        (((List.range n).map (fun vertex => BVLogicalExpr.eval (assignment value)
          (conjoin accept (membership disclosures vertex)))) ++
        ((List.range n).map (fun vertex => BVLogicalExpr.eval (assignment value)
          (conjoin accept (membership recovery vertex))))) := by
  simp only [outputsFor, List.map_cons, List.map_append, List.map_map, Function.comp_def]

theorem outputs_eval (value : Nat) :
    outputs.map (BVLogicalExpr.eval (assignment value)) =
      BVLogicalExpr.eval (assignment value) accept ::
        (((List.range graphNodes).map (fun vertex => BVLogicalExpr.eval (assignment value)
          (conjoin accept (membership disclosures vertex)))) ++
        ((List.range graphNodes).map (fun vertex => BVLogicalExpr.eval (assignment value)
          (conjoin accept (membership recovery vertex))))) :=
  (congrArg (List.map (BVLogicalExpr.eval (assignment value))) outputs_eq).trans
    (outputsFor_eval graphNodes value)

theorem outputsFor_eval_rejected (n value : Nat) (hvalue : value < 2 ^ rawBits)
    (hfalse : rawAccept value = false) :
    (outputsFor n).map (BVLogicalExpr.eval (assignment value)) =
      false :: List.replicate (2 * n) false := by
  rw [outputsFor_eval]
  simp [conjoin, BVLogicalExpr.eval_gate, Std.Tactic.BVDecide.Gate.eval,
    accept_refines value hvalue, hfalse, List.map_const, ← List.replicate_add,
    two_mul, Nat.add_comm]

theorem outputs_refine (value : Nat) (hvalue : value < 2 ^ rawBits) :
    outputs.map (BVLogicalExpr.eval (assignment value)) = rawOutput value := by
  by_cases haccept : rawAccept value = true
  · have hfields : rawThreshold value < threshold ∧ rawRank value < encodingCardinality := by
      simpa only [rawAccept, decide_eq_true_eq] using haccept
    let route := decodedRoute ⟨rawRank value, hfields.2⟩
    have hdecode : decodeRaw value = some route := by simp [decodeRaw, hfields, route]
    have hfrontier := eval_mask_refines value hvalue haccept disclosures route.disclosure
      (fun vertex hv => disclosures_refine value hvalue hfields.2 vertex (vertex_fits vertex hv))
    have hplan := eval_mask_refines value hvalue haccept recovery route.recovery
      (fun vertex hv => recovery_refines value hvalue hfields.2 vertex (vertex_fits vertex hv))
    have hfrontier' : ((List.range graphNodes).map (fun vertex =>
        BVLogicalExpr.eval (assignment value) (conjoin accept (membership disclosures vertex)))) =
        route.frontier := hfrontier.trans (frontier_eq route).symm
    have hplan' : ((List.range graphNodes).map (fun vertex =>
        BVLogicalExpr.eval (assignment value) (conjoin accept (membership recovery vertex)))) =
        route.plan := hplan.trans (plan_eq route).symm
    rw [outputs_eval, accept_refines value hvalue, haccept]
    rw [rawOutput_some value route hdecode]
    rw [hfrontier', hplan']
  · have hfalse : rawAccept value = false := by cases h : rawAccept value <;> simp_all
    have hfields : ¬(rawThreshold value < threshold ∧ rawRank value < encodingCardinality) := by
      simpa only [rawAccept, decide_eq_true_eq] using haccept
    have hdecode : decodeRaw value = none := by simp [decodeRaw, hfields]
    have h := (congrArg (List.map (BVLogicalExpr.eval (assignment value))) outputs_eq).trans
      (outputsFor_eval_rejected graphNodes value hvalue hfalse)
    exact h.trans (rawOutput_none value hdecode).symm

end PoissonDAG.GRSCC.EncoderFormula
