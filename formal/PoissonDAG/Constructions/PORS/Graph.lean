import PoissonDAG.Core.GraphFacts

/-! The three nested binary trees are expanded in postorder. Each occurrence
gets its own address, including each independent private seed. -/
namespace PoissonDAG.PORS

inductive Shape where
  | leaf
  | branch (left right : Shape)
  deriving Repr

def Shape.leaves : Shape → Nat
  | .leaf => 1
  | .branch l r => l.leaves + r.leaves

inductive Tree where
  | secret
  | hash (child : Tree)
  | join (left right : Tree)
  deriving Repr

def Tree.nodes : Tree → Nat
  | .secret => 1
  | .hash t => t.nodes + 1
  | .join l r => l.nodes + r.nodes + 1

def Tree.emit (base : Nat) : Tree → List Node
  | .secret => [.source]
  | .hash t => t.emit base ++ [.unary (base+t.nodes-1)]
  | .join l r => l.emit base ++ r.emit (base+l.nodes) ++
      [.binary (base+l.nodes-1) (base+l.nodes+r.nodes-1)]

theorem Tree.emit_length (t : Tree) (base : Nat) : (t.emit base).length = t.nodes := by
  induction t generalizing base with
  | secret => rfl
  | hash t ih => simp [Tree.emit, Tree.nodes, ih]
  | join l r ihl ihr => simp [Tree.emit, Tree.nodes, ihl, ihr, Nat.add_assoc]

def chain : Nat → Tree
  | 0 => .secret
  | n+1 => .hash (chain n)

theorem chain_nodes (n : Nat) : (chain n).nodes = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, Tree.nodes, ih]

def Shape.fill : Shape → Tree → Tree
  | .leaf, t => t
  | .branch l r, t => .join (l.fill t) (r.fill t)

theorem Shape.fill_nodes (s : Shape) (t : Tree) :
    (s.fill t).nodes + 1 = s.leaves * (t.nodes+1) := by
  induction s with
  | leaf => simp [Shape.fill, Shape.leaves]
  | branch l r ihl ihr =>
    simp only [Shape.fill, Tree.nodes, Shape.leaves, Nat.add_mul]
    omega

def graph (forest outer child : Shape) (capacity : Nat) : List Node :=
  (forest.fill (outer.fill (child.fill (chain (capacity+1))))).emit 0

theorem graph_length (forest outer child : Shape) (capacity : Nat) :
    (graph forest outer child capacity).length + 1 =
    forest.leaves * (outer.leaves * (child.leaves * (capacity+3))) := by
  simp [graph, Tree.emit_length, Shape.fill_nodes, chain_nodes, Nat.add_assoc]

end PoissonDAG.PORS
