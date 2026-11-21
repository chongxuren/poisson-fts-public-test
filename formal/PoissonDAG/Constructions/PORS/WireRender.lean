import PoissonDAG.Core.CircuitFacts

namespace PoissonDAG.PORS

/-- Wire zero is a valid constant-false fallback. Ordinary program wires have
addresses one greater than before rendering. -/
def wireRef (bound source : Nat) : Nat := if source<bound then source+1 else 0

private theorem wireRef_lt (bound source : Nat) : wireRef bound source < bound+1 := by
  unfold wireRef
  split <;> omega

def renderGate (inputs atIdx : Nat) : Gate → Gate
  | .input j => if j<inputs then .input j else .constant false
  | .constant b => .constant b
  | .neg a => .neg (wireRef atIdx a)
  | .conj a b => .conj (wireRef atIdx a) (wireRef atIdx b)
  | .xor a b => .xor (wireRef atIdx a) (wireRef atIdx b)

def render (width outputCount : Nat) (program : Array Gate) (wires : List Nat) : Circuit :=
  let table := wires.toArray
  ⟨width,.constant false :: (List.range program.size).map
    (fun i => renderGate width i (program[i]?.getD (.constant false))),
    (List.range outputCount).map (fun i => wireRef program.size (table[i]?.getD program.size))⟩

@[simp] theorem render_inputs (w n : Nat) (p : Array Gate) (a : List Nat) :
    (render w n p a).inputs=w := rfl

@[simp] theorem render_arity (w n : Nat) (p : Array Gate) (a : List Nat) :
    (render w n p a).outputs.length=n := by simp [render]

theorem render_valid (w n : Nat) (p : Array Gate) (a : List Nat) :
    (render w n p a).Valid := by
  constructor
  · intro i g h
    cases i with
    | zero =>
      have he : Gate.constant false=g := by simpa [render] using h
      subst g
      trivial
    | succ i =>
      have ht : i < p.size := by
        have hi := (List.getElem?_eq_some_iff.mp h).choose
        simpa [render] using hi
      have he : renderGate w i (p[i]?.getD (.constant false)) = g := by
        simpa [render,List.getElem?_map,List.getElem?_range ht] using h
      subst g
      cases hg : (p[i]?.getD (.constant false)) with
      | input j =>
        by_cases hj : j<w <;> simp [renderGate,hj,hg,render]
      | constant v => trivial
      | neg j => exact wireRef_lt i j
      | conj j k => exact ⟨wireRef_lt i j,wireRef_lt i k⟩
      | xor j k => exact ⟨wireRef_lt i j,wireRef_lt i k⟩
  · intro i hi
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    simpa [render] using wireRef_lt p.size (a.toArray[j]?.getD p.size)

end PoissonDAG.PORS
