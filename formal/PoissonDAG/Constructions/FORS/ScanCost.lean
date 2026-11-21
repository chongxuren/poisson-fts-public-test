import PoissonDAG.Core.GraphFacts

namespace PoissonDAG.FORS

private theorem step_conservation (plan : List Bool) (s : List Bool × Nat) (e : Node × Nat)
    (hb : e.2 < s.1.length) :
    weight (closeStep plan s e).1+s.2 = weight s.1+(closeStep plan s e).2 := by
  rcases s with ⟨known,calls⟩
  rcases e with ⟨n,i⟩
  change i < known.length at hb
  unfold closeStep
  simp only
  by_cases h : get known i = true
  · simp [h]
  · have hf : known[i] = false := by
      have hh := Bool.eq_false_iff.mpr h
      simpa [get, List.getElem?_eq_getElem hb] using hh
    simp only [if_neg h]
    split
    · simp [weight,List.count_set hb,hf,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · rfl

private theorem fold_conservation (plan : List Bool) (es : List (Node × Nat)) (s : List Bool × Nat)
    (hb : ∀ e ∈ es, e.2 < s.1.length) :
    weight (es.foldl (closeStep plan) s).1+s.2 = weight s.1+(es.foldl (closeStep plan) s).2 := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    have hstep := step_conservation plan s e (hb e (by simp))
    have hr := ih (closeStep plan s e) (by
      intro e' he'
      rw [closeStep_length]
      exact hb e' (by simp [he']))
    simp only [List.foldl_cons]
    omega

theorem calls_conservation (graph : List Node) (supplied plan : List Bool)
    (hlen : supplied.length = graph.length) :
    weight (close graph supplied plan).1 = weight supplied+(close graph supplied plan).2 := by
  have hh := fold_conservation plan graph.zipIdx (supplied,0) (by
    intro e he
    change e.2 < supplied.length
    rw [hlen]
    exact List.snd_lt_of_mem_zipIdx he)
  simpa only [← close_eq_foldl,Nat.add_zero] using hh

end PoissonDAG.FORS
