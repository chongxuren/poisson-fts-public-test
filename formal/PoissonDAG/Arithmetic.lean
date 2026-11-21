import PoissonDAG.Model

namespace PoissonDAG

def referenceRationalBound : Rat :=
  ((List.range 65).map (fun q =>
    (q^40 : Nat) / ((factorial q * 2^280 : Nat) : Rat))).foldl (· + ·) 0 +
    (66 : Rat) / (65 * factorial 65 : Nat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem reference_finite_arithmetic :
    referenceRationalBound ≤ (1 : Rat) / 2^128 := by decide +kernel

-- Only finite arithmetic is certified here. The coefficient/tail bridge and
-- correspondence to a literal Scheme still require proofs.
example : 40 * (2^9 - 1) + 39 + 3 = (20482 : Nat) := by decide
example : 40 * 8 + 39 + 3 = (362 : Nat) := by decide
example : 40 * 9 * 16 = (5760 : Nat) := by decide

end PoissonDAG
