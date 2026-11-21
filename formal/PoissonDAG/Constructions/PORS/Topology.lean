import PoissonDAG.Constructions.PORS.Graph

namespace PoissonDAG.PORS

private def orderedAt (base : Nat) : List Node → Prop
  | [] => True
  | x::xs => x.ValidAt base ∧ orderedAt (base+1) xs

private theorem ordered_append (xs ys : List Node) (base : Nat)
    (hx : orderedAt base xs) (hy : orderedAt (base+xs.length) ys) :
    orderedAt base (xs++ys) := by
  induction xs generalizing base with
  | nil => simpa using hy
  | cons x xs ih =>
    refine ⟨hx.1, ih (base+1) hx.2 ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hy

private theorem nodes_positive (t : Tree) : 0 < t.nodes := by
  cases t <;> simp [Tree.nodes]

private theorem emit_ordered (t : Tree) (base : Nat) : orderedAt base (t.emit base) := by
  induction t generalizing base with
  | secret => exact ⟨True.intro, True.intro⟩
  | hash t ih =>
    apply ordered_append _ _ _ (ih base)
    rw [Tree.emit_length]
    have hp := nodes_positive t
    exact ⟨by change base+t.nodes-1 < base+t.nodes; omega, True.intro⟩
  | join l r ihl ihr =>
    apply ordered_append
    · apply ordered_append _ _ _ (ihl base)
      simpa [Tree.emit_length] using ihr (base+l.nodes)
    · rw [List.length_append, Tree.emit_length, Tree.emit_length]
      have hl := nodes_positive l
      have hr := nodes_positive r
      refine ⟨?_, True.intro⟩
      change base+l.nodes-1 < base+(l.nodes+r.nodes) ∧
        base+l.nodes+r.nodes-1 < base+(l.nodes+r.nodes)
      omega

private theorem indexed {xs : List Node} {base : Nat} (h : orderedAt base xs)
    {i : Nat} {x : Node} (hx : xs[i]? = some x) : x.ValidAt (base+i) := by
  induction xs generalizing base i with
  | nil => simp at hx
  | cons v vs ih =>
    cases i with
    | zero =>
      have heq : v = x := by simpa using hx
      simpa [← heq] using h.1
    | succ i =>
      have hx' : vs[i]? = some x := by simpa using hx
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih h.2 hx'

theorem emitted_valid (t : Tree) : GraphValid (t.emit 0) := by
  intro i node h
  simpa only [Nat.zero_add] using indexed (emit_ordered t 0) h

theorem graph_valid (forest outer child : Shape) (capacity : Nat) :
    GraphValid (graph forest outer child capacity) := by
  intro i node h
  simpa only [Nat.zero_add] using indexed (emit_ordered _ 0) h

end PoissonDAG.PORS
