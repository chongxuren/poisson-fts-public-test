import PoissonDAG.Constructions.PORS.RankGates
import PoissonDAG.Constructions.PORS.WireRender
import PoissonDAG.Constructions.PORS.Graph
import PoissonDAG.Constructions.PORS.SingleRefinedRow
import PoissonDAG.Constructions.PORS.BucketRefinedRow
import PoissonDAG.Constructions.PORS.ChainRefinedRow

namespace PoissonDAG.PORS
namespace Literal
open RankGates

/-- Split the leftmost extra leaves of the complete height-h tree. -/
def leftShape : Nat → Nat → Shape
  | 0, extra => if extra=0 then .leaf else .branch .leaf .leaf
  | h+1, extra => .branch (leftShape h (min (2^h) extra)) (leftShape h (extra-2^h))

def shape (n : Nat) := leftShape (Nat.log2 n) (n-2^(Nat.log2 n))

structure Part where
  active : Nat
  marks : Array (Nat×Nat)
  siblings : Word

def merge (countHere : Bool) (l r : Part) : Build Part := do
  let ls ← both (← neg l.active) r.active
  let rs ← both (← neg r.active) l.active
  let active ← either l.active r.active
  let lw := l.marks.back!
  let rw := r.marks.back!
  let lmark := l.marks.set! (l.marks.size-1) (← either lw.1 ls,lw.2)
  let rmark := r.marks.set! (r.marks.size-1) (← either rw.1 rs,rw.2)
  let mut count := (← addSub l.siblings r.siblings false).1
  if countHere then
    let inc := (lit count.size 0).set! 0 (← parity l.active r.active)
    count := (← addSub count inc false).1
  return ⟨active,(lmark++rmark).push (0,active),count⟩

def atShape (countHere : Bool) (leaf : Nat → Build Part) : Shape → Nat → Build Part
  | .leaf, off => leaf off
  | .branch l r, off => do
    merge countHere (← atShape countHere leaf l off) (← atShape countHere leaf r (off+l.leaves))

/-- A support leaf can occur only once. Its selected residual e supplies the
chain point c-e; every strictly later point is an actual verification hash. -/
def atLeaf (p : Row) (digits : Digits) (leaf : Nat) : Build Part := do
  let w := width p
  let mut selected := 0
  let mut openings := Array.replicate (p.cap+2) 0
  for (s,e) in digits.leaves.zip digits.depths do
    let here ← eqw s (lit w leaf)
    selected ← either selected here
    for v in [:p.cap+1] do
      let hit ← both here (← eqw e (lit w (p.cap-v)))
      openings := openings.set! v (← either (bit openings v) hit)
  let mut known := 0
  let mut marks := #[]
  for v in [:p.cap+2] do
    let offer := bit openings v
    marks := marks.push (offer,known)
    known ← either known offer
  return ⟨selected,marks,lit w 0⟩

def atCoord (p : Row) (child outer : Shape) (digits : Digits) : Build Part := do
  let inner ← atShape true (atLeaf p digits) child 0
  let outerPart ← atShape false (fun j => do
    let hit ← eqw digits.bucket (lit (width p) j)
    let mut marks := #[]
    for (s,h) in inner.marks do
      marks := marks.push (← both s hit,← both h hit)
    return ⟨← both inner.active hit,marks,lit (width p) 0⟩) outer 0
  return { outerPart with siblings := inner.siblings }

def build (p : Row) (forest outer child : Shape) : Build (List Nat) := do
  let (rankValid,coords) ← decode p
  let slots := coords.toArray
  let full ← atShape false (fun i => atCoord p child outer slots[i]!) forest 0
  let (_,past) ← addSub full.siblings (lit (width p) (p.M+1)) true
  let accept ← both rankValid (← neg past)
  return accept :: (full.marks.toList.map Prod.fst ++ full.marks.toList.map Prod.snd)

def scheme (p : Row) : Scheme :=
  let forest := shape p.K
  let outer := shape p.buckets
  let child := shape p.t
  let (outputs,gates) := (build p forest outer child).run #[.constant false,.constant true]
  let g := graph forest outer child p.cap
  ⟨g,render p.r (1+2*g.length) gates outputs,p.ctr⟩

theorem scheme_circuit_valid (p : Row) : (scheme p).encoder.Valid := render_valid _ _ _ _

theorem scheme_output_arity (p : Row) :
    (scheme p).encoder.outputs.length = 1+2*(scheme p).graph.length := render_arity _ _ _ _

def single : Scheme := scheme SingleRefined.p
def bucket : Scheme := scheme BucketRefined.p
def chainBuckets : Scheme := scheme ChainRefined.p

end Literal
end PoissonDAG.PORS
