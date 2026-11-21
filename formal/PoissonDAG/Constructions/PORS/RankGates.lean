import PoissonDAG.Constructions.PORS.RowModel

/-! Explicit Boolean gate builder for mixed-radix and combinadic decoding.
Every intermediate is an array of wire numbers; reusing a word reuses its
wires. The algorithm never enumerates the raw rank domain or the k-subsets. -/
namespace PoissonDAG.PORS.RankGates

abbrev Build := StateM (Array Gate)
abbrev Word := Array Nat

def emit (g : Gate) : Build Nat := do
  let a ← getThe (Array Gate)
  set (a.push g)
  return a.size

def neg (x : Nat) : Build Nat :=
  if x=0 then pure 1 else if x=1 then pure 0 else emit (.neg x)
def both (x y : Nat) : Build Nat :=
  if x=0 ∨ y=0 then pure 0 else if x=1 then pure y else if y=1 ∨ x=y then pure x
  else emit (.conj x y)
def parity (x y : Nat) : Build Nat :=
  if x=0 then pure y else if y=0 then pure x else if x=y then pure 0
  else emit (.xor x y)
def either (x y : Nat) : Build Nat := do
  if x=1 ∨ y=1 then return 1
  if x=0 then return y
  if y=0 ∨ x=y then return x
  neg (← both (← neg x) (← neg y))
def mux (sel a b : Nat) : Build Nat := do
  if sel=1 then return a
  if sel=0 ∨ a=b then return b
  parity b (← both sel (← parity a b))

def lit (width n : Nat) : Word :=
  ((List.range width).map fun i => if n.testBit i then 1 else 0).toArray
def bit (a : Word) (i : Nat) : Nat := a[i]?.getD 0

def muxw (sel : Nat) (a b : Word) : Build Word := do
  let mut out := #[]
  for i in [:a.size] do
    out := out.push (← mux sel (bit a i) (bit b i))
  return out

/-- With subtract=true this returns (a-b mod 2^width, a≥b). -/
def addSub (a b : Word) (subtract : Bool) : Build (Word × Nat) := do
  let mut carry := if subtract then 1 else 0
  let mut out := #[]
  for i in [:a.size] do
    let x := bit a i
    let y ← if subtract then neg (bit b i) else pure (bit b i)
    let xy ← parity x y
    out := out.push (← parity xy carry)
    carry ← parity (← both x y) (← both xy carry)
  return (out,carry)

def eqw (a b : Word) : Build Nat := do
  let mut mismatch := 0
  for i in [:a.size] do
    mismatch ← either mismatch (← parity (bit a i) (bit b i))
  neg mismatch

def shl (a : Word) (i : Nat) : Word :=
  ((List.range a.size).map fun j => if j<i then 0 else bit a (j-i)).toArray

def times (a b : Word) : Build Word := do
  let mut out := lit a.size 0
  for i in [:b.size] do
    let flag := bit b i
    if flag != 0 then
      let part ← muxw flag (shl a i) (lit a.size 0)
      out := (← addSub out part false).1
  return out

/-- Fixed-divisor restoring long division. The caller allocates a guard bit
above every shifted reduced remainder. -/
def divmod (a : Word) (byNat : Nat) : Build (Word × Word) := do
  if byNat=1 then return (a,lit a.size 0)
  let mut rem := lit a.size 0
  let mut quot := lit a.size 0
  for j in [:a.size] do
    let i := a.size-1-j
    let shifted := (shl rem 1).set! 0 (bit a i)
    let (diff,ge) ← addSub shifted (lit a.size byNat) true
    rem ← muxw ge diff shifted
    quot := quot.set! i ge
  return (quot,rem)

/-- Binomial(v,j) via falling product. The chosen widths also accommodate this
intermediate product, before division by j!. -/
def binomWord (v : Word) (j : Nat) : Build Word := do
  let mut prod := lit v.size 1
  for h in [:j] do
    prod ← times prod (← addSub v (lit v.size h) true).1
  return (← divmod prod (Nat.factorial j)).1

/-- Greedy colex unranking. Each largest index is found by binary lifting;
the returned list is in increasing order. -/
def unrank (t k : Nat) (rank : Word) : Build (List Word) := do
  let mut rem := rank
  let mut selected := []
  let levels := Nat.log2 (t-1)+1
  for idx in [:k] do
    let j := k-idx
    let mut v := lit rank.size 0
    for h in [:levels] do
      let candidate := v.set! (levels-1-h) 1
      let coeff ← binomWord candidate j
      let (_,ge) ← addSub rem coeff true
      let (_,past) ← addSub candidate (lit rank.size t) true
      v ← muxw (← both ge (← neg past)) candidate v
    rem := (← addSub rem (← binomWord v j) true).1
    selected := v::selected
  return selected

structure Digits where
  bucket : Word
  leaves : List Word
  depths : List Word
  deriving Inhabited

def width (p : Row) := max (p.r+2)
  ((p.k+1)*(Nat.log2 (max p.t (p.E+p.k))+2)+2)

/-- Valid for the selected chainless or sum-simplex rows. The k-1 separators
of a simplex point form a (k-1)-subset of E+k-1 positions. -/
def decode (p : Row) : Build (Nat × List Digits) := do
  let w := width p
  let mut raw := lit w 0
  for i in [:p.r] do raw := raw.set! i (← emit (.input i))
  let mut rem := raw
  let mut coords := []
  for _ in [:p.K] do
    let (afterDepth,digits) ← divmod rem p.depthCount
    let (afterSupport,support) ← divmod afterDepth p.supports
    let (rest,bucket) ← divmod afterSupport p.buckets
    rem := rest
    let leaves ← unrank p.t p.k support
    let mut depths := []
    if p.cap=0 then
      depths := List.replicate p.k (lit w 0)
    else
      let bars ← unrank (p.E+p.k-1) (p.k-1) digits
      let mut next := lit w 0
      for bar in bars do
        depths := (← addSub bar next true).1 :: depths
        next := (← addSub bar (lit w 1) false).1
      depths := ((← addSub (lit w (p.E+p.k-1)) next true).1 :: depths).reverse
    coords := ⟨bucket,leaves,depths⟩ :: coords
  return (← eqw rem (lit w 0),coords.reverse)

end PoissonDAG.PORS.RankGates
