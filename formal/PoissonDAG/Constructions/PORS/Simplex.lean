import PoissonDAG.Constructions.PORS.RowModel

/-! Exact positive supplier-count polynomial for the sum-simplex c=E. -/
namespace PoissonDAG.PORS

def simplexAtom (k E i d : Nat) : Nat :=
  Nat.fast_choose k i * Nat.fast_choose (d+i-1) (i-1) *
    Nat.fast_choose (E-d+k-1) (k-1)

private def polyStep (k E : Nat) (atoms : List (List Nat))
    (old : List (List Nat)) : List (List Nat) :=
  (List.range (k+1)).map fun h =>
    (List.range (E+1)).map fun d =>
      ((List.range h).map fun ii =>
        let i := ii+1
        ((List.range (d+1)).map fun f =>
          (old[h-i]?.getD [])[d-f]?.getD 0 *
            (atoms[i]?.getD [])[f]?.getD 0).sum).sum

def simplexCoefficient (k E j : Nat) : Nat :=
  let atoms := (List.range (k+1)).map fun i =>
    (List.range (E+1)).map fun d => simplexAtom k E i d
  let initial := [[1]]
  let powers := (List.range j).foldl (fun state _ => polyStep k E atoms state) initial
  (powers[k]?.getD [])[E]?.getD 0

def Row.simplexChild (p : Row) (coefs : List Nat) (m : Nat) : ℚ :=
  let num := ((List.range p.k).map fun idx =>
    let j := idx+1
    Nat.fast_choose m j * coefs[idx]?.getD 0 * p.depthCount^(p.k-j)).sum
  min 1 ((num : ℚ) / ((p.supports * p.depthCount^(p.k+1) : Nat) : ℚ))

def Row.simplexBucket (p : Row) (coefs : List Nat) (q : Nat) : ℚ :=
  ((List.range (q+1)).map (fun m =>
    ((Nat.fast_choose q m * (p.buckets-1)^(q-m) : Nat) : ℚ) *
      p.simplexChild coefs m)).sum / ((p.buckets^q : Nat) : ℚ)

def Row.simplexEnvelope (p : Row) (coefs : List Nat) (q : Nat) : ℚ :=
  min ((p.acceptedWords : ℚ) / 2^p.r)
    (((p.domain : ℚ) / 2^p.r) * (p.simplexBucket coefs q)^p.K)

end PoissonDAG.PORS
