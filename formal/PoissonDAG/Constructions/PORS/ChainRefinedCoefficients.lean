import PoissonDAG.Constructions.PORS.ChainRefinedRow

namespace PoissonDAG.PORS.ChainRefined

private def radix : Nat := 2^256
private def atom (i : Nat) : Nat := ((List.range 33).map fun d =>
  simplexAtom 4 32 i d * radix^d).sum
private def digit (v : Nat) : Nat := (v / radix^32) % radix
private def mass : Nat := ((List.range 4).map fun j =>
  ((List.range 33).map fun d => simplexAtom 4 32 (j+1) d).sum).sum

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- All coefficients of products through fourth power fit a digit. The four
entries expand the positive-degree partitions of x-degree four. -/
theorem supplier_replay :
    mass^4 < radix ∧ p.depthCount = Nat.fast_choose 35 3 ∧
    [digit (atom 4), digit (2*atom 1*atom 3 + atom 2^2),
      digit (3*atom 1^2*atom 2), digit (atom 1^4)] = coefs := by
  decide +kernel

end PoissonDAG.PORS.ChainRefined
