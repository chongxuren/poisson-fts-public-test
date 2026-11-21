import PoissonDAG.Constructions.PORS.SupportCount

namespace PoissonDAG.PORS

private def joinCounts (k radix : Nat) (left right : List Nat) : List Nat :=
  (List.range (k+1)).map fun j =>
    if j = 0 then 1 else
    ((List.range (j+1)).map (fun i =>
      left[i]?.getD 0 * right[j-i]?.getD 0 *
        (if i = 0 ∨ i = j then radix else 1))).sum

/-- Start with 2^h leaves, then split the first extra leaves. A fully split or
untouched subtree reuses the complete-tree recurrence. -/
def leftFilled (k radix : Nat) : Nat → Nat → List Nat
  | 0, extra => packedLevels k radix (if extra=0 then 0 else 1)
  | h+1, extra =>
    if extra = 0 then packedLevels k radix (h+1)
    else if extra = 2^(h+1) then packedLevels k radix (h+2)
    else joinCounts k radix
      (leftFilled k radix h (min (2^h) extra))
      (leftFilled k radix h (extra-2^h))

def Row.leftFilledWords (p : Row) (height extra : Nat) : Nat :=
  let radix := 2^(p.r+2)
  let poly := (leftFilled p.k radix height extra)[p.k]?.getD 0
  let low := (poly^p.K) % (radix^(p.M+1))
  low % (radix-1) * (p.buckets*p.depthCount)^p.K

end PoissonDAG.PORS
