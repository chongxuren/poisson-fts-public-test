import PoissonDAG.Model

/-! # Authenticated disclosures, challenge draft v0.2 -/
namespace PoissonDAG.V2

def IsParent (graph : List Node) (parent child : Nat) : Prop :=
  match graph[child]? with
  | some (.unary p) => parent = p
  | some (.binary l r) => parent = l ∨ parent = r
  | _ => False

/-- The value at `node` uses the transmitted value at `label`.
In the honest scan, known nodes that were not supplied were hashed. -/
inductive Uses (graph : List Node) (supplied known : List Bool) (label : Nat) : Nat → Prop
  | input : get supplied label = true → Uses graph supplied known label label
  | hash {parent child} : Uses graph supplied known label parent →
      get supplied child = false → get known child = true → IsParent graph parent child →
      Uses graph supplied known label child

def Authenticated (graph : List Node) (supplied plan : List Bool) : Prop :=
  let root := graph.length - 1
  let known := (close graph supplied plan).1
  get supplied root = false ∧ get known root = true ∧
    ∀ i : Fin graph.length, get supplied i = true → Uses graph supplied known i root

structure Eligible (s : Scheme) : Prop where
  base : s.Eligible
  authenticated : ∀ raw ∈ s.accepted, Authenticated s.graph (s.frontier raw) (s.plan raw)

def ConstructionCertificate (s : Scheme) (upperBytes : Nat) : Prop :=
  Eligible s ∧ s.size ≤ upperBytes

def UniversalLowerBound (lowerBytes : Nat) : Prop :=
  ∀ s : Scheme, Eligible s → lowerBytes ≤ s.size

theorem ofBaseConstruction {s : Scheme} {n : Nat} (h : PoissonDAG.ConstructionCertificate s n)
    (auth : ∀ raw ∈ s.accepted, Authenticated s.graph (s.frontier raw) (s.plan raw)) :
    ConstructionCertificate s n := ⟨⟨h.1, auth⟩, h.2⟩

theorem ofBaseLowerBound {n : Nat} (h : PoissonDAG.UniversalLowerBound n) :
    UniversalLowerBound n := fun s hs => h s hs.base

end PoissonDAG.V2
