import PoissonDAG.Constructions.GRSCC.Covering

/-! Homogeneous FORS with a unary leaf commitment and binary aggregation.
The definitions generate literal lists only when evaluated. All dimensions and
addresses are parametric; no compilation step evaluates a production forest. -/
namespace PoissonDAG.FORS

structure Config where
  height : Nat
  trees : Nat
  zeroBits : Nat
  counterBits : Nat

namespace Config

def leaves (p : Config) := 2^p.height
def heapSize (p : Config) := 2*p.leaves-1
def sources (p : Config) := p.trees*p.leaves
def heapEnd (p : Config) := p.sources+p.trees*p.heapSize
def vertexCount (p : Config) := p.heapEnd+(p.trees-1)
def secret (p : Config) (tree index : Nat) := tree*p.leaves+index

/-- Binary heap number 1 is the root. Descending heap numbers give a
topological order, after the initial contiguous run of private sources. -/
def heapAddress (p : Config) (tree h : Nat) :=
  p.sources+tree*p.heapSize+(p.heapSize-h)

def node (p : Config) (v : Nat) : Node :=
  if v < p.sources then .source
  else if v < p.heapEnd then
    let tree := (v-p.sources)/p.heapSize
    let h := p.heapSize-(v-p.sources)%p.heapSize
    if h ≥ p.leaves then .unary (p.secret tree (h-p.leaves))
    else .binary (p.heapAddress tree (2*h)) (p.heapAddress tree (2*h+1))
  else
    let link := v-p.heapEnd
    .binary (if link = 0 then p.heapAddress 0 1 else v-1)
      (p.heapAddress (link+1) 1)

def graph (p : Config) := (List.range p.vertexCount).map p.node

def rawBits (p : Config) := p.trees*p.height+p.zeroBits
def prefixBase (p : Config) := 2+2*p.rawBits+p.zeroBits
def prefixGate (p : Config) (tree h : Nat) :=
  p.prefixBase+tree*p.heapSize+(h-1)

/-- Two constants, raw bits, their negations, a conjunction of the virtual
zero bits, then the prefix indicators of every physical tree in heap order. -/
def gate (p : Config) (i : Nat) : Gate :=
  if i < 2 then .constant (decide (i=1))
  else if i < 2+p.rawBits then .input (i-2)
  else if i < 2+2*p.rawBits then .neg (2+(i-(2+p.rawBits)))
  else if i < p.prefixBase then
    let j := i-(2+2*p.rawBits)
    .conj (if j=0 then 1 else i-1) (2+p.rawBits+p.trees*p.height+j)
  else
    let j := i-p.prefixBase
    let tree := j/p.heapSize
    let h := j%p.heapSize+1
    if h=1 then .constant true
    else
      let bit := tree*p.height+(p.height-h.log2)
      .conj (p.prefixGate tree (h/2)) (if h%2=0 then 2+p.rawBits+bit else 2+bit)

def disclosureGate (p : Config) (v : Nat) :=
  if v < p.sources then p.prefixGate (v/p.leaves) (p.leaves+v%p.leaves)
  else if v < p.heapEnd then
    let tree := (v-p.sources)/p.heapSize
    let h := p.heapSize-(v-p.sources)%p.heapSize
    if h=1 then 0 else p.prefixGate tree (if h%2=0 then h+1 else h-1)
  else 0

def encoder (p : Config) : Circuit where
  inputs := p.rawBits
  gates := (List.range (p.prefixBase+p.trees*p.heapSize)).map p.gate
  outputs := [if p.zeroBits=0 then 1 else p.prefixBase-1] ++
    (List.range p.vertexCount).map p.disclosureGate ++ List.replicate p.vertexCount 1

def scheme (p : Config) : Scheme := ⟨p.graph, p.encoder, p.counterBits⟩

theorem graph_length (p : Config) : p.graph.length = p.vertexCount := by
  simp [graph]

theorem output_length (p : Config) :
    p.scheme.encoder.outputs.length = 1+2*p.scheme.graph.length := by
  simp [scheme, encoder, graph] <;> omega

theorem source_at (p : Config) {v : Nat} (hv : v < p.sources) :
    p.graph[v]? = some .source := by
  have hlen : v < p.vertexCount := by unfold vertexCount heapEnd; omega
  simp [graph, List.getElem?_map, List.getElem?_range hlen, node, hv]

/-- In the public interpreter, every covered disclosed source in the literal
forest has a supplier among the actual prior raw inputs. The key root is the
only initially available public vertex, and is explicitly excluded. -/
theorem source_has_history (p : Config) {v target : Nat} {history : List Nat}
    (hv : v < p.sources) (hroot : p.scheme.graph.length-1 ≠ v)
    (hfront : get (p.scheme.frontier target) v = true)
    (hc : p.scheme.covered history target = true) :
    ∃ raw ∈ history, get (p.scheme.frontier raw) v = true := by
  have hb : GRSCC.BackwardBarrier p.scheme.graph (fun j => j=v) := by
    intro n i hm hi
    subst i
    have hn := List.mk_mem_zipIdx_iff_getElem?.mp hm
    have hs : p.scheme.graph[v]? = some .source := p.source_at hv
    have hnSource : n = .source := Option.some.inj (hn.symm.trans hs)
    subst n
    trivial
  have hi : v < p.scheme.graph.length := by
    change v < p.graph.length
    rw [graph_length]
    unfold vertexCount heapEnd
    omega
  obtain ⟨raw, hr, ha⟩ := GRSCC.covered_requires_barrier_hit p.scheme history target v
    p.output_length hb hroot hi rfl hfront hc
  obtain ⟨j, hj, hjv⟩ := GRSCC.not_avoids_witness ha
  exact ⟨raw, hr, hj ▸ hjv⟩

end Config
end PoissonDAG.FORS
