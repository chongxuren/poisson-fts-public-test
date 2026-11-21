import PoissonDAG.Constructions.PORS.FiniteCut
import Mathlib.Data.Nat.Choose.Basic

namespace PoissonDAG.PORS

structure Row where
  K : Nat
  b : Nat
  t : Nat
  k : Nat
  cap : Nat
  E : Nat
  M : Nat
  r : Nat
  ctr : Nat
  depthCount : Nat
  acceptedWords : Nat

namespace Row

def buckets (p : Row) := 2^p.b
def supports (p : Row) := Nat.fast_choose p.t p.k
def domain (p : Row) := (p.buckets * p.supports * p.depthCount)^p.K
def graphNodes (p : Row) := p.K*p.buckets*p.t*(p.cap+3)-1
def digestCalls (p : Row) := (p.r+127)/128
def signCeiling (p : Row) :=
  p.graphNodes + (p.digestCalls*2^p.r+p.acceptedWords-1)/p.acceptedWords
def verifyCeiling (p : Row) := p.digestCalls+p.K*(2*p.k+p.E+p.b)+p.M-1
def bytes (p : Row) := (p.ctr+7)/8 + 16*(p.K*(p.k+p.b)+p.M)

def child (p : Row) (m : Nat) : ℚ :=
  if m = 0 then 0
  else if m = 1 then 1 / ((p.supports*p.depthCount : Nat) : ℚ)
  else min 1 ((Nat.fast_choose (p.k*m) p.k : ℚ) / p.supports)

def bucketEnvelope (p : Row) (q : Nat) : ℚ :=
  if p.b = 0 then p.child q
  else ((List.range (q+1)).map (fun m =>
    ((Nat.fast_choose q m * (p.buckets-1)^(q-m) : Nat) : ℚ) * p.child m)).sum /
      ((p.buckets^q : Nat) : ℚ)

def rawEnvelope (p : Row) (q : Nat) : ℚ :=
  min ((p.acceptedWords : ℚ) / 2^p.r)
    (((p.domain : ℚ) / 2^p.r) * (p.bucketEnvelope q)^p.K)

end Row
end PoissonDAG.PORS
