import PoissonDAG.Model

/-! # The protected circuit evaluator as a topological scan -/

namespace PoissonDAG

def executeGates (raw : Nat) (gates : List Gate) : List Bool :=
  gates.foldl (fun values gate => values ++ [evalGate raw values gate]) []

theorem executeGates_take_eq (raw : Nat) (gates : List Gate) (value : Nat → Bool)
    (heq : ∀ (i : Nat) (hi : i < gates.length),
      evalGate raw ((List.range i).map value) gates[i] = value i) :
    ∀ n, n ≤ gates.length → executeGates raw (gates.take n) = (List.range n).map value := by
  intro n hn
  induction n with
  | zero => simp [executeGates]
  | succ n ih =>
    have hi : n < gates.length := by omega
    rw [List.take_succ_eq_append_getElem hi]
    simp only [executeGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change executeGates raw (gates.take n) ++
      [evalGate raw (executeGates raw (gates.take n)) gates[n]] = _
    rw [ih (by omega), heq n hi]
    simp [List.range_succ]

theorem get_map_range (value : Nat → Bool) {i n : Nat} (hi : i < n) :
    get ((List.range n).map value) i = value i := by
  simp [get, List.getElem?_map, List.getElem?_range hi]

theorem Circuit.eval_of_equations (c : Circuit) (raw : Nat) (value : Nat → Bool)
    (heq : ∀ (i : Nat) (hi : i < c.gates.length),
      evalGate raw ((List.range i).map value) c.gates[i] = value i)
    (hout : ∀ i ∈ c.outputs, i < c.gates.length) :
    c.eval raw = c.outputs.map value := by
  have hrun := executeGates_take_eq raw c.gates value heq c.gates.length (by omega)
  simp only [List.take_length] at hrun
  change c.outputs.map (get (executeGates raw c.gates)) = _
  rw [hrun]
  apply List.map_congr_left
  intro i hi
  exact get_map_range value (hout i hi)

end PoissonDAG
