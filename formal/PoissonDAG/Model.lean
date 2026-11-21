import Std
import Init.Data.Rat.Basic

/-!
Draft organizer-owned semantics, not an audited launch target.
All finite probabilities are derived from graph/circuit data. Poisson comparison
uses rational cuts, retaining every q. There is no entrant-supplied probability.
-/
namespace PoissonDAG

inductive Node where
  | source
  | unary (parent : Nat)
  | binary (left right : Nat)
  deriving DecidableEq, Repr

inductive Gate where
  | input (index : Nat)
  | constant (value : Bool)
  | neg (parent : Nat)
  | conj (left right : Nat)
  | xor (left right : Nat)
  deriving DecidableEq, Repr

structure Circuit where
  inputs : Nat
  gates : List Gate
  outputs : List Nat
  deriving Repr

def get (xs : List Bool) (i : Nat) : Bool := xs[i]?.getD false

def evalGate (raw : Nat) (previous : List Bool) : Gate → Bool
  | .input i => raw.testBit i
  | .constant b => b
  | .neg p => !(get previous p)
  | .conj l r => get previous l && get previous r
  | .xor l r => xor (get previous l) (get previous r)

def Circuit.eval (c : Circuit) (raw : Nat) : List Bool :=
  let values := c.gates.foldl (fun values gate => values ++ [evalGate raw values gate]) []
  c.outputs.map (get values)

def Circuit.Valid (c : Circuit) : Prop :=
  (∀ (i : Nat) (g : Gate), c.gates[i]? = some g → match g with
    | .input j => j < c.inputs
    | .constant _ => True
    | .neg p => p < i
    | .conj l r | .xor l r => l < i ∧ r < i) ∧
  ∀ o ∈ c.outputs, o < c.gates.length

def Node.ValidAt (i : Nat) : Node → Prop
  | .source => True
  | .unary p => p < i
  | .binary l r => l < i ∧ r < i

def ready (known : List Bool) : Node → Bool
  | .source => false
  | .unary p => get known p
  | .binary l r => get known l && get known r

/-- A single topological scan. Private sources never appear by empty-parent closure.
`allowed` limits honest verification; the covering experiment allows every node. -/
def close (graph : List Node) (disclosed allowed : List Bool) : List Bool × Nat :=
  (graph.zipIdx).foldl (fun (known, calls) (node, i) =>
    if get known i then (known, calls)
    else if get allowed i && ready known node then
      (known.set i true, calls + 1)
    else (known, calls)) (disclosed, 0)

def weight (xs : List Bool) : Nat := xs.count true
def union (a b : List Bool) : List Bool := (a.zip b).map (fun (x,y) => x || y)
def subset (a b : List Bool) : Bool := (a.zip b).all (fun (x,y) => !x || y)

structure Scheme where
  graph : List Node
  encoder : Circuit
  counterBits : Nat
  deriving Repr

def Scheme.raws (s : Scheme) : List Nat := List.range (2 ^ s.encoder.inputs)
def Scheme.accept (s : Scheme) (raw : Nat) : Bool := get (s.encoder.eval raw) 0
def Scheme.frontier (s : Scheme) (raw : Nat) : List Bool :=
  (s.encoder.eval raw).drop 1 |>.take s.graph.length
def Scheme.plan (s : Scheme) (raw : Nat) : List Bool :=
  (s.encoder.eval raw).drop (1 + s.graph.length) |>.take s.graph.length
def Scheme.accepted (s : Scheme) : List Nat := s.raws.filter s.accept
def Scheme.tau (s : Scheme) : Rat := (s.accepted.length : Rat) / (2 ^ s.encoder.inputs : Nat)
def Scheme.trials (s : Scheme) : Nat := 2 ^ s.counterBits
def Scheme.failure (s : Scheme) : Rat := (1 - s.tau) ^ s.trials
def Scheme.expectedTrials (s : Scheme) : Rat :=
  ((List.range s.trials).map (fun j => (1 - s.tau) ^ j)).foldl (· + ·) 0
def Scheme.digestCalls (s : Scheme) : Nat := (s.encoder.inputs + 127) / 128
def Scheme.signCost (s : Scheme) : Rat :=
  (s.graph.length : Rat) + (s.digestCalls : Rat) * s.expectedTrials
def Scheme.verifyCalls (s : Scheme) (raw : Nat) : Nat :=
  s.digestCalls + (close s.graph (s.frontier raw) (s.plan raw)).2
def Scheme.verifyCost (s : Scheme) : Rat :=
  (1 - s.failure) *
    (((s.accepted.map (fun raw => (s.verifyCalls raw : Rat))).foldl (· + ·) 0) /
      (s.accepted.length : Rat))
def Scheme.size (s : Scheme) : Nat :=
  (s.counterBits + 7) / 8 +
    16 * ((s.accepted.map (fun raw => weight (s.frontier raw))).foldl max 0)

/-- Conditional successful histories, with replacement; one common q. -/
def histories (accepted : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | q+1 => (histories accepted q).flatMap (fun hs => accepted.map (fun x => x :: hs))

def Scheme.covered (s : Scheme) (hs : List Nat) (target : Nat) : Bool := Id.run do
  let empty := List.replicate s.graph.length false
  let pooled := hs.foldl (fun known raw => union known (s.frontier raw)) empty
  -- The public key root is available in the covering experiment only.
  let pooled := pooled.set (s.graph.length - 1) true
  let known := (close s.graph pooled (List.replicate s.graph.length true)).1
  return s.accept target && subset (s.frontier target) known

/-- Includes the raw target's acceptance factor exactly once. -/
def Scheme.coverCoefficient (s : Scheme) (q : Nat) : Rat :=
  let hs := histories s.accepted q
  let numerator := ((hs.flatMap (fun h => s.raws.map (fun x => s.covered h x))).count true)
  (numerator : Rat) / ((s.accepted.length ^ q * 2 ^ s.encoder.inputs : Nat) : Rat)

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def partialSum (a : Nat → Rat) (n : Nat) : Rat :=
  ((List.range n).map (fun q => a q / (factorial q : Rat))).foldl (· + ·) 0

/-- Upper rational cuts for e: sum_{q<m}1/q! + (m+1)/(m*m!).
Only positive m are used. The analytic correspondence is not yet mechanized. -/
def expUpper (m : Nat) : Rat :=
  partialSum (fun _ => 1) m + (m+1 : Nat) / ((m * factorial m : Nat) : Rat)

/-- For bounded nonnegative a_q, equivalent to e^-1 sum a_q/q! <= budget.
No finite support assumption or nonsummable Real.tsum default is used. -/
def PoissonLE (a : Nat → Rat) (budget : Rat) : Prop :=
  ∀ n m : Nat, 0 < m → partialSum a n ≤ budget * expUpper m

def Scheme.WellFormed (s : Scheme) : Prop :=
  0 < s.graph.length ∧ 0 < s.encoder.inputs ∧ s.encoder.Valid ∧
  s.encoder.outputs.length = 1 + 2 * s.graph.length ∧
  (∀ (i : Nat) (node : Node), s.graph[i]? = some node → node.ValidAt i) ∧
  0 < s.accepted.length

def Scheme.Correct (s : Scheme) : Prop :=
  ∀ raw ∈ s.accepted,
    get (close s.graph (s.frontier raw) (s.plan raw)).1 (s.graph.length - 1) = true

def Scheme.Eligible (s : Scheme) : Prop :=
  s.WellFormed ∧ s.Correct ∧
  s.failure ≤ (1 : Rat) / 2^128 ∧
  s.signCost ≤ 2^24 ∧ s.verifyCost ≤ 512 ∧
  PoissonLE s.coverCoefficient ((1 : Rat) / 2^128)

def ConstructionCertificate (s : Scheme) (upperBytes : Nat) : Prop :=
  s.Eligible ∧ s.size ≤ upperBytes

def UniversalLowerBound (lowerBytes : Nat) : Prop :=
  ∀ s : Scheme, s.Eligible → lowerBytes ≤ s.size

end PoissonDAG
