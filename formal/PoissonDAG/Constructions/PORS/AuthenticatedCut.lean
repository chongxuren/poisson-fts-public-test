import PoissonDAG.Core.RestrictedScan
import PoissonDAG.V2.Model

/-! A pruned opening traverses actual graph edges. Leaves are supplied
addresses and interior vertices are permitted hashes whose own values are
absent from the payload. These conditions make every leaf authenticate
against the final root in the protected evaluator. -/
namespace PoissonDAG.PORS

inductive Cut (graph : List Node) (supplied plan : List Bool) : Nat → List Nat → Prop
  | leaf {i} : get supplied i = true → Cut graph supplied plan i [i]
  | unary {i p xs} : graph[i]? = some (.unary p) → get supplied i = false →
      get plan i = true → Cut graph supplied plan p xs → Cut graph supplied plan i xs
  | binary {i l r xs ys} : graph[i]? = some (.binary l r) → get supplied i = false →
      get plan i = true → Cut graph supplied plan l xs → Cut graph supplied plan r ys →
      Cut graph supplied plan i (xs++ys)

theorem Cut.derives {graph supplied plan i xs} (h : Cut graph supplied plan i xs) :
    PlanDerives graph (maskSet supplied) plan i := by
  induction h with
  | leaf hg => exact .disclosed (mem_maskSet.mpr hg)
  | unary hn _ hp _ ih => exact .unary hn hp ih
  | binary hn _ hp _ _ il ir => exact .binary hn hp il ir

theorem Cut.uses {graph supplied plan i xs} (valid : GraphValid graph)
    (len : supplied.length = graph.length) (h : Cut graph supplied plan i xs) :
    ∀ v ∈ xs, V2.Uses graph supplied (close graph supplied plan).1 v i := by
  induction h with
  | leaf hg =>
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact .input hg
  | unary hn hm hp sub ih =>
    have hknown := close_of_planDerives valid supplied plan len
      (List.getElem?_eq_some_iff.mp hn).choose (.unary hn hp sub.derives)
    intro v hv
    exact .hash (ih v hv) hm hknown (by simp [V2.IsParent,hn])
  | binary hn hm hp left right il ir =>
    have hknown := close_of_planDerives valid supplied plan len
      (List.getElem?_eq_some_iff.mp hn).choose (.binary hn hp left.derives right.derives)
    intro v hv
    cases List.mem_append.mp hv with
    | inl h => exact .hash (il v h) hm hknown (by simp [V2.IsParent,hn])
    | inr h => exact .hash (ir v h) hm hknown (by simp [V2.IsParent,hn])

theorem authenticated_of_cut {graph : List Node} {supplied plan : List Bool}
    {xs : List Nat} (valid : GraphValid graph) (nonempty : 0 < graph.length)
    (len : supplied.length = graph.length)
    (h : Cut graph supplied plan (graph.length-1) xs)
    (root : get supplied (graph.length-1) = false)
    (covers : ∀ i : Fin graph.length, get supplied i = true → i.val ∈ xs) :
    V2.Authenticated graph supplied plan := by
  refine ⟨root, close_of_planDerives valid supplied plan len (by omega) h.derives, ?_⟩
  intro i hi
  exact h.uses valid len i.val (covers i hi)

end PoissonDAG.PORS
