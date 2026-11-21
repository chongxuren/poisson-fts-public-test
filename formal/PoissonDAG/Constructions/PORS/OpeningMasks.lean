import PoissonDAG.Constructions.PORS.TreeOpening

namespace PoissonDAG.PORS

/-- The choice to stop at a node transmits only its label. A unary or binary
continuation computes that node instead. A private source can only be stopped. -/
inductive Opening : Tree → Type
  | stop (t) : Opening t
  | hash {t} : Opening t → Opening (.hash t)
  | join {l r} : Opening l → Opening r → Opening (.join l r)

def Opening.marks {t} : Opening t → List (Bool × Bool)
  | .stop v => List.replicate (v.nodes-1) (false,false) ++ [(true,false)]
  | .hash a => a.marks ++ [(false,true)]
  | .join a b => a.marks ++ b.marks ++ [(false,true)]

def Opening.labels {t} (a : Opening t) (off : Nat) : List Nat :=
  match a with
  | .stop v => [off+v.nodes-1]
  | .hash child => child.labels off
  | .join (l := l) a b => a.labels off ++ b.labels (off+l.nodes)

private theorem positive_nodes (t : Tree) : 0 < t.nodes := by cases t <;> simp [Tree.nodes]

theorem Opening.mark_length {t} (a : Opening t) : a.marks.length = t.nodes := by
  induction a with
  | stop t => have hp := positive_nodes t; simp [Opening.marks]; omega
  | hash a ha => simp [Opening.marks, Tree.nodes, ha]
  | join a b ha hb => simp [Opening.marks, Tree.nodes, ha,hb,Nat.add_assoc]

private def View (s p : List Bool) (off : Nat) (m : List (Bool×Bool)) : Prop :=
  ∀ j v, m[j]? = some v → get s (off+j) = v.1 ∧ get p (off+j) = v.2

private theorem view_left {s p a b off} (h : View s p off (a++b)) : View s p off a :=
  fun j v hv => h j v (before_suffix a b hv)

private theorem view_right {s p a b off} (h : View s p off (a++b)) :
    View s p (off+a.length) b := by
  intro j v hv
  simpa [Nat.add_assoc] using h (a.length+j) v ((after_prefix a b j).trans hv)

private theorem view_last {s p a v off} (h : View s p off (a++[v])) :
    get s (off+a.length) = v.1 ∧ get p (off+a.length) = v.2 := by
  simpa using view_right h 0 v (by simp)

private theorem Opening.traverse {t} (a : Opening t) (s p : List Bool) (off : Nat)
    (view : View s p off a.marks) : Traversal s p off t (a.labels off) := by
  induction a generalizing off with
  | stop t =>
    have hp := positive_nodes t
    have eqoff : off+(t.nodes-1)=off+t.nodes-1 := by omega
    apply Traversal.stop
    simpa [List.length_replicate,eqoff] using (view_last view).1
  | hash a ih =>
    have h := view_last view
    simp only [Opening.mark_length] at h
    exact .hash h.1 h.2 (ih off (view_left view))
  | join a b ia ib =>
    have h := view_last view
    simp only [List.length_append,Opening.mark_length] at h
    have vv := view_left view
    have right := view_right vv
    simp only [Opening.mark_length] at right
    have h' := h
    simp only [← Nat.add_assoc] at h'
    exact .join h'.1 h'.2 (ia off (view_left vv)) (ib _ right)

theorem Opening.actual_cut {t} (a : Opening t) :
    Cut (t.emit 0) (a.marks.map Prod.fst) (a.marks.map Prod.snd)
      (0+t.nodes-1) (a.labels 0) := by
  apply Traversal.cut _ (emitted_located t)
  apply a.traverse
  intro j v hv
  simp [get, List.getElem?_map,hv]

private theorem split_lookup {α : Type} (a b : List α) {i : Nat} {v : α}
    (h : (a++b)[i]? = some v) :
    (i < a.length ∧ a[i]? = some v) ∨
    (a.length ≤ i ∧ b[i-a.length]? = some v) := by
  by_cases hi : i < a.length
  · left
    have he := before_suffix a b (List.getElem?_eq_getElem hi)
    exact ⟨hi, (List.getElem?_eq_getElem hi).trans (he.symm.trans h)⟩
  · right
    have le : a.length ≤ i := by omega
    have he := after_prefix a b (i-a.length)
    rw [Nat.add_sub_of_le le] at he
    exact ⟨le,he.symm.trans h⟩

private theorem take_hash_prefix {a : List (Bool×Bool)} {i : Nat} {v : Bool×Bool}
    (h : (a++[(false,true)])[i]? = some v) (hv : v.1 = true) : a[i]? = some v := by
  rcases split_lookup _ _ h with ⟨_,hh⟩ | ⟨_,hh⟩
  · exact hh
  · generalize i-a.length = j at hh
    cases j with
    | zero => simp at hh; subst v; contradiction
    | succ j => simp at hh

theorem Opening.supplied_mem {t} (a : Opening t) {i : Nat} {v : Bool×Bool}
    (off : Nat) (h : a.marks[i]? = some v) (hv : v.1 = true) :
    off+i ∈ a.labels off := by
  induction a generalizing off i with
  | stop t =>
    rcases split_lookup _ _ h with ⟨hi,he⟩ | ⟨hi,he⟩
    · simp only [List.length_replicate] at hi
      simp [List.getElem?_replicate,hi] at he
      subst v
      contradiction
    · simp only [List.length_replicate] at hi he
      have hsize := (List.getElem?_eq_some_iff.mp he).choose
      simp only [List.length_singleton] at hsize
      have hp := positive_nodes t
      simp only [Opening.labels,List.mem_singleton]
      omega
  | hash a ih =>
    exact ih off (take_hash_prefix h hv)
  | join a b ia ib =>
    have hprefix := take_hash_prefix h hv
    rcases split_lookup _ _ hprefix with ⟨_,he⟩ | ⟨hi,he⟩
    · exact List.mem_append.mpr (Or.inl (ia off he))
    · have hm := ib (off+a.marks.length) he
      have idx : off+a.marks.length+(i-a.marks.length) = off+i := by omega
      rw [idx,Opening.mark_length] at hm
      exact List.mem_append.mpr (Or.inr hm)

theorem Opening.authenticated {t} (a : Opening t)
    (root : get (a.marks.map Prod.fst) (t.nodes-1) = false) :
    V2.Authenticated (t.emit 0) (a.marks.map Prod.fst) (a.marks.map Prod.snd) := by
  have valid : GraphValid (t.emit 0) := by
    intro i n h
    exact emitted_valid t i n h
  apply authenticated_of_cut valid (by simpa [Tree.emit_length] using positive_nodes t)
    (by simp [a.mark_length,Tree.emit_length])
    (by simpa only [Nat.zero_add,Tree.emit_length] using a.actual_cut)
    (by simpa only [Tree.emit_length] using root)
  intro i hi
  cases h : a.marks[i.val]? with
  | none => simp [get,List.getElem?_map,h] at hi
  | some v =>
    have hv : v.1 = true := by simpa [get,List.getElem?_map,h] using hi
    simpa using a.supplied_mem 0 h hv

end PoissonDAG.PORS
