import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import PoissonDAG.Model

/-!
# Fixed GRS-CC parameters

The bottom-key address in the historical encoder is absent: this construction
has one fixed per-key graph.  Consequently the raw encoder has 170 bits, rather
than 234. Both 128-bit digest blocks are charged on every model trial.

The constants below are arithmetic consequences of the displayed parameters;
they are not fields that a construction certificate may set independently.
-/
namespace PoissonDAG.GRSCC

def bucketBits : Nat := 4
def bucketCount : Nat := 2 ^ bucketBits
def initialOwnerBits : Nat := 1
def initialOwnerCount : Nat := 2 ^ initialOwnerBits
def treeHeight : Nat := 5
def slotCount : Nat := 2 ^ treeHeight
def layerCount : Nat := 7
def positionCount : Nat := treeHeight + 1
def capacity : Nat := 8
def depthSum : Nat := 16
def thresholdBits : Nat := 32
def threshold : Nat := 1340
def counterWidth : Nat := 32

/-- Number of bounded constant-sum words, calculated by coefficient recurrence.
The recursion is on the number of positions and needs no enumeration of ranks.
-/
def codeCount : Nat → Nat → Nat
  | 0, e => if e = 0 then 1 else 0
  | k + 1, e => ((List.range (min (capacity + 1) (e + 1))).map
      (fun d => codeCount k (e - d))).sum

/-- A cached numeral, justified by `codeCount_fixed_eq`. Keeping the proof
separate prevents definitional equality from rerunning the coefficient
recurrence whenever a finite index type is checked. -/
def codeCardinality : Nat := 15597
def coordinateRadix : Nat := slotCount * codeCardinality
def encodingCardinality : Nat :=
  bucketCount * initialOwnerCount * coordinateRadix ^ layerCount
def rankBits : Nat := 138
def rawBits : Nat := thresholdBits + rankBits
def digestBlockCount : Nat := (rawBits + 127) / 128

/-- Sources are charged once each, just like unary and binary nodes. -/
def ownerNodes : Nat :=
  slotCount * (capacity + 3) +
    ((List.range treeHeight).map (fun d => 2 ^ (d + 1) * capacity)).sum - 1
def ownersPerChild : Nat := initialOwnerCount + (layerCount - 1) * slotCount
def childNodes : Nat := ownersPerChild * ownerNodes + initialOwnerCount - 1
def graphNodes : Nat := bucketCount * (childNodes + 1) - 1
def signatureWords : Nat := bucketBits + initialOwnerBits + layerCount * positionCount
def signatureBytes : Nat := (counterWidth + 7) / 8 + 16 * signatureWords
def routeHashCalls : Nat :=
  bucketBits + initialOwnerBits +
    layerCount * (depthSum + treeHeight * capacity + treeHeight + 1)
def verifierHashCalls : Nat := digestBlockCount + routeHashCalls

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem codeCount_fixed_eq : codeCount positionCount depthSum = codeCardinality := by
  decide +kernel

theorem codeCardinality_eq : codeCardinality = 15597 := rfl

theorem fixed_geometry :
    ownerNodes = 847 ∧ ownersPerChild = 194 ∧ childNodes = 164319 ∧
    graphNodes = 2629119 ∧ signatureWords = 47 ∧ signatureBytes = 756 ∧
    routeHashCalls = 439 ∧ verifierHashCalls = 441 := by
  decide +kernel

theorem fixed_encoder :
    rawBits = 170 ∧ digestBlockCount = 2 ∧
    2 ^ (rankBits - 1) < encodingCardinality ∧
    encodingCardinality ≤ 2 ^ rankBits := by
  simp only [encodingCardinality, coordinateRadix, codeCardinality_eq]
  decide +kernel

/-- Acceptance probability of the specified independent threshold/rank tests.
This becomes the Scheme probability only after the circuit/counting refinement.
-/
def acceptanceRatio : ℚ :=
  ((threshold * encodingCardinality : Nat) : ℚ) / (2 ^ rawBits : Nat)

theorem acceptanceRatio_pos : 0 < acceptanceRatio := by
  norm_num [acceptanceRatio, encodingCardinality, coordinateRadix,
    codeCardinality_eq, threshold, bucketCount, bucketBits, initialOwnerCount,
    initialOwnerBits, slotCount, treeHeight, layerCount, rawBits, thresholdBits,
    rankBits]

theorem acceptanceRatio_lower : (1 : ℚ) / 2 ^ 23 ≤ acceptanceRatio := by
  norm_num [acceptanceRatio, encodingCardinality, coordinateRadix,
    codeCardinality_eq, threshold, bucketCount, bucketBits, initialOwnerCount,
    initialOwnerBits, slotCount, treeHeight, layerCount, rawBits, thresholdBits,
    rankBits]

theorem acceptanceRatio_le_one : acceptanceRatio ≤ 1 := by
  norm_num [acceptanceRatio, encodingCardinality, coordinateRadix,
    codeCardinality_eq, threshold, bucketCount, bucketBits, initialOwnerCount,
    initialOwnerBits, slotCount, treeHeight, layerCount, rawBits, thresholdBits,
    rankBits]

/-- Conservative fixed-trial model cost. This is deliberately different from
the historical early-rejection estimate of 7,152,960 calls. -/
theorem fixed_trial_signing_budget :
    (graphNodes : ℚ) + digestBlockCount / acceptanceRatio < 2 ^ 24 := by
  rw [fixed_geometry.2.2.2.1, fixed_encoder.2.1]
  norm_num [acceptanceRatio, encodingCardinality, coordinateRadix,
    codeCardinality_eq, threshold, bucketCount, bucketBits, initialOwnerCount,
    initialOwnerBits, slotCount, treeHeight, layerCount, rawBits, thresholdBits,
    rankBits]

end PoissonDAG.GRSCC
