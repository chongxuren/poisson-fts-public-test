import PoissonDAG.Core.GraphFacts

/-! # Honest verification with a restricted computation plan

Replacing a forbidden operation by a private source gives an ordinary AND-DAG.
Its derivability semantics is exactly the protected restricted scan.
-/

namespace PoissonDAG

def restrictGraph (graph : List Node) (allowed : List Bool) : List Node :=
  graph.mapIdx (fun i node => if get allowed i then node else .source)

@[simp] theorem restrictGraph_length (graph : List Node) (allowed : List Bool) :
    (restrictGraph graph allowed).length = graph.length := by simp [restrictGraph]

theorem restrictGraph_get {graph : List Node} {allowed : List Bool} {i : Nat} {node : Node}
    (hn : graph[i]? = some node) (ha : get allowed i = true) :
    (restrictGraph graph allowed)[i]? = some node := by
  simp [restrictGraph, List.getElem?_mapIdx, hn, ha]

theorem restrictGraph_valid {graph : List Node} (hg : GraphValid graph)
    (allowed : List Bool) : GraphValid (restrictGraph graph allowed) := by
  intro i node hn
  simp only [restrictGraph, List.getElem?_mapIdx] at hn
  cases hnode : graph[i]? with
  | none => simp [hnode] at hn
  | some original =>
      simp only [hnode, Option.map_some, Option.some.injEq] at hn
      by_cases ha : get allowed i = true
      · simp only [ha, if_true] at hn
        subst node
        exact hg i original hnode
      · have haf : get allowed i = false := Bool.eq_false_iff.mpr ha
        simp only [haf, Bool.false_eq_true, if_false] at hn
        subst node
        trivial

theorem restrictGraph_zipIdx (graph : List Node) (allowed : List Bool) :
    (restrictGraph graph allowed).zipIdx =
      graph.zipIdx.map (fun (node, i) => (if get allowed i then node else .source, i)) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_zipIdx, restrictGraph, List.getElem?_mapIdx,
    List.getElem?_map, Option.map_map, Nat.zero_add]
  cases graph[i]? <;> simp

theorem closeStep_restrict (graph : List Node) (allowed : List Bool)
    (state : List Bool × Nat) (node : Node) (i : Nat) (hi : i < graph.length) :
    closeStep (List.replicate graph.length true) state
        (if get allowed i then node else .source, i) =
      closeStep allowed state (node, i) := by
  have hall : get (List.replicate graph.length true) i = true := by
    simp [get, hi]
  cases hk : get state.1 i <;> cases ha : get allowed i <;>
    simp [closeStep, hk, ha, hall, ready]

theorem fold_close_restrict (graph : List Node) (allowed : List Bool)
    (entries : List (Node × Nat))
    (hbound : ∀ entry ∈ entries, entry.2 < graph.length) (state : List Bool × Nat) :
    (entries.map (fun (node, i) => (if get allowed i then node else .source, i))).foldl
        (closeStep (List.replicate graph.length true)) state =
      entries.foldl (closeStep allowed) state := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨node, i⟩
      simp only [List.map_cons, List.foldl_cons]
      rw [closeStep_restrict graph allowed state node i (hbound (node, i) (by simp))]
      exact ih (fun entry he => hbound entry (by simp [he])) _

theorem close_restrict (graph : List Node) (disclosed allowed : List Bool) :
    close (restrictGraph graph allowed) disclosed
        (List.replicate (restrictGraph graph allowed).length true) =
      close graph disclosed allowed := by
  rw [close_eq_foldl, close_eq_foldl, restrictGraph_length, restrictGraph_zipIdx]
  apply fold_close_restrict
  intro entry he
  have hn := List.mem_zipIdx_iff_getElem?.mp he
  exact (List.getElem?_eq_some_iff.mp hn).choose

/-- A proof tree for a concrete permitted verification plan. -/
inductive PlanDerives (graph : List Node) (disclosed : Finset Nat)
    (allowed : List Bool) : Nat → Prop
  | disclosed {i} : i ∈ disclosed → PlanDerives graph disclosed allowed i
  | unary {i p} : graph[i]? = some (.unary p) → get allowed i = true →
      PlanDerives graph disclosed allowed p → PlanDerives graph disclosed allowed i
  | binary {i l r} : graph[i]? = some (.binary l r) → get allowed i = true →
      PlanDerives graph disclosed allowed l → PlanDerives graph disclosed allowed r →
      PlanDerives graph disclosed allowed i

theorem PlanDerives.restricted {graph : List Node} {disclosed : Finset Nat}
    {allowed : List Bool} {i : Nat} (h : PlanDerives graph disclosed allowed i) :
    Derives (restrictGraph graph allowed) disclosed i := by
  induction h with
  | disclosed hi => exact .disclosed hi
  | unary hn ha _ ih => exact .unary (restrictGraph_get hn ha) ih
  | binary hn ha _ _ ihl ihr => exact .binary (restrictGraph_get hn ha) ihl ihr

theorem close_of_planDerives {graph : List Node} (hg : GraphValid graph)
    (disclosed allowed : List Bool) (hlen : disclosed.length = graph.length)
    {i : Nat} (hi : i < graph.length)
    (h : PlanDerives graph (maskSet disclosed) allowed i) :
    get (close graph disclosed allowed).1 i = true := by
  rw [← close_restrict graph disclosed allowed]
  exact (close_complete_iff (restrictGraph_valid hg allowed) disclosed
    (by simpa using hlen) (by simpa using hi)).2 h.restricted

theorem closeStep_calls_le (allowed : List Bool) (state : List Bool × Nat)
    (entry : Node × Nat) :
    (closeStep allowed state entry).2 ≤ state.2 + (if get allowed entry.2 then 1 else 0) := by
  rcases state with ⟨known, calls⟩
  rcases entry with ⟨node, i⟩
  cases hk : get known i <;> cases ha : get allowed i <;> cases hr : ready known node <;>
    simp [closeStep, hk, ha, hr]

theorem fold_close_calls_le (allowed : List Bool) (entries : List (Node × Nat))
    (state : List Bool × Nat) :
    (entries.foldl (closeStep allowed) state).2 ≤ state.2 +
      (entries.map (fun entry => if get allowed entry.2 then 1 else 0)).sum := by
  induction entries generalizing state with
  | nil => simp
  | cons entry entries ih =>
      have hstep := closeStep_calls_le allowed state entry
      have hrest := ih (closeStep allowed state entry)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      omega

theorem sum_bits_eq_weight (xs : List Bool) :
    (xs.map (fun bit => if bit then 1 else 0)).sum = weight xs := by
  induction xs with
  | nil => rfl
  | cons bit xs ih => cases bit <;> simp [weight, ih, Nat.add_comm]

theorem close_calls_le_weight (graph : List Node) (disclosed allowed : List Bool)
    (hlen : allowed.length = graph.length) :
    (close graph disclosed allowed).2 ≤ weight allowed := by
  have h := fold_close_calls_le allowed graph.zipIdx (disclosed, 0)
  rw [← close_eq_foldl] at h
  have hmap : graph.zipIdx.map (fun entry => if get allowed entry.2 then 1 else 0) =
      allowed.map (fun bit => if bit then 1 else 0) := by
    have hm : graph.zipIdx.map (fun entry => if get allowed entry.2 then 1 else 0) =
        (graph.zipIdx.map Prod.snd).map (fun i => if get allowed i then 1 else 0) := by
      simp only [List.map_map, Function.comp_def]
    rw [hm, List.zipIdx_map_snd]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < allowed.length
    · simp [hi, ← hlen, get]
    · have hig : ¬ i < graph.length := by omega
      have haNone : allowed[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hrNone : (List.range' 0 graph.length)[i]? = none :=
        List.getElem?_eq_none_iff.mpr (by simp; omega)
      simp [haNone, hrNone]
  simpa [hmap, sum_bits_eq_weight] using h

end PoissonDAG
