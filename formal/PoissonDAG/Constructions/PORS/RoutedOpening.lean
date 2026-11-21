import PoissonDAG.Constructions.PORS.OpeningMasks

/-! Turn a decoded PORS support, bucket selection and residual-depth assignment
into the exact Octopus, outer-path and coordinate-compression traversal. -/
namespace PoissonDAG.PORS

/-- Stop precisely at the secret or intermediate chain index chosen below the
committed endpoint. Setting target=capacity-e recovers e+1 chain links. -/
def openChain : (links : Nat) → Nat → Opening (chain links)
  | 0, _ => .stop _
  | n+1, target =>
    if n+1 ≤ target then .stop _ else .hash (openChain n target)

/-- If a subtree has no selected leaf, signal absence to its parent. The first
nonempty sibling then stops at its root. Nodes hidden below that stop produce
no payload. If both children have marks, both recurse. -/
def openSelected (unit : Tree) (select : Nat → Option (Opening unit)) :
    (shape : Shape) → Nat → Option (Opening (shape.fill unit))
  | .leaf, off => select off
  | .branch l r, off =>
    match openSelected unit select l off, openSelected unit select r (off+l.leaves) with
    | none, none => none
    | some a, none => some (.join a (.stop _))
    | none, some b => some (.join (.stop _) b)
    | some a, some b => some (.join a b)

/-- Supports are optional residual depths indexed by coordinate and leaf.
The single bucket per coordinate and all forest joins are explicit. -/
def routedOpening (forest outer child : Shape) (capacity : Nat)
    (bucket : Nat → Nat) (depth : Nat → Nat → Option Nat) :
    Option (Opening (forest.fill (outer.fill (child.fill (chain (capacity+1)))))) :=
  let leafTree := chain (capacity+1)
  let childTree := child.fill leafTree
  let coordTree := outer.fill childTree
  let childOpen := fun i => openSelected leafTree
    (fun l => (depth i l).map (fun e => openChain (capacity+1) (capacity-e))) child 0
  let coordOpen := fun i => openSelected childTree
    (fun j => if j = bucket i then childOpen i else none) outer 0
  openSelected coordTree coordOpen forest 0

def Opening.continues {t} : Opening t → Prop
  | .stop _ => False
  | .hash _ => True
  | .join _ _ => True

private theorem last_unsupplied (m : List (Bool×Bool)) :
    get ((m++[(false,true)]).map Prod.fst) m.length = false := by
  have h : (m++[(false,true)])[m.length]? = some (false,true) := by
    simpa using after_prefix m [(false,true)] 0
  simp [get,List.getElem?_map,h]

private theorem continued_root {t} (a : Opening t) (ha : a.continues) :
    get (a.marks.map Prod.fst) (t.nodes-1) = false := by
  cases a with
  | stop t => exact False.elim ha
  | hash x => simpa [Opening.marks,Tree.nodes,x.mark_length] using last_unsupplied x.marks
  | join x y => simpa [Opening.marks,Tree.nodes,Opening.mark_length,Nat.add_assoc] using
      last_unsupplied (x.marks++y.marks)

private theorem selected_continues (unit : Tree) (select : Nat → Option (Opening unit))
    (shape : Shape) (off : Nat) (all : ∀ i v, select i = some v → v.continues)
    {out : Opening (shape.fill unit)} (h : openSelected unit select shape off = some out) :
    out.continues := by
  cases shape with
  | leaf => exact all off out h
  | branch l r =>
    cases hl : openSelected unit select l off <;>
      cases hr : openSelected unit select r (off+l.leaves) <;>
      simp [openSelected,hl,hr] at h <;> subst out <;> trivial

private theorem routed_continues {forest outer child : Shape} {c : Nat}
    {bucket : Nat → Nat} {depth : Nat → Nat → Option Nat}
    {a : Opening (forest.fill (outer.fill (child.fill (chain (c+1)))))}
    (h : routedOpening forest outer child c bucket depth = some a) : a.continues := by
  unfold routedOpening at h
  apply selected_continues _ _ _ 0 _ h
  intro i out hout
  apply selected_continues _ _ _ 0 _ hout
  intro j v hv
  split at hv
  · apply selected_continues _ _ _ 0 _ hv
    intro l ch hch
    cases hd : depth i l with
    | none => simp [hd] at hch
    | some e =>
      simp [hd] at hch
      subst ch
      simp [openChain,show ¬ c+1 ≤ c-e by omega,Opening.continues]
  · contradiction

/-- A route containing at least one valid selected opening always rehashes the
public root, including in the one-coordinate, one-bucket, one-leaf case. -/
theorem routed_authenticated {forest outer child : Shape} {c : Nat}
    {bucket : Nat → Nat} {depth : Nat → Nat → Option Nat}
    {a : Opening (forest.fill (outer.fill (child.fill (chain (c+1)))))}
    (route : routedOpening forest outer child c bucket depth = some a) :
    V2.Authenticated (graph forest outer child c) (a.marks.map Prod.fst)
      (a.marks.map Prod.snd) :=
  a.authenticated (continued_root a (routed_continues route))

end PoissonDAG.PORS
