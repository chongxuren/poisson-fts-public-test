import PoissonDAG.Constructions.PORS.RowModel

/-! Packed generating functions for exact forced-pruning counts. A digit of
the polynomial counts supports at a given authentication size. Each coefficient
of a completed subtree or coordinate product is bounded by its total number
of possible supports. The radix is two bits wider than the raw rank domain. -/
namespace PoissonDAG.PORS

private def next (k radix : Nat) (prev : List Nat) : List Nat :=
  (List.range (k+1)).map fun j =>
    if j = 0 then 1 else
    ((List.range (j+1)).map (fun i =>
      prev[i]?.getD 0 * prev[j-i]?.getD 0 *
        (if i = 0 ∨ i = j then radix else 1))).sum

def packedLevels (k radix : Nat) : Nat → List Nat
  | 0 => [1,1]
  | h+1 => next k radix (packedLevels k radix h)

/-- For t=2^height and one block. Local subset sets and global Cartesian
products are counted with multiplicity one in the coefficient recurrence. -/
def Row.replayedWords (p : Row) (height : Nat) : Nat :=
  let radix := 2^(p.r+2)
  let poly := (packedLevels p.k radix height)[p.k]?.getD 0
  let low := (poly^p.K) % (radix^(p.M+1))
  let count := low % (radix-1)
  count * (p.buckets*p.depthCount)^p.K

end PoissonDAG.PORS
