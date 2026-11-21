import PoissonDAG.Constructions.PORS.AuthenticatedCut
import PoissonDAG.Constructions.PORS.Topology

namespace PoissonDAG.PORS

/-- An occurrence of an authored PORS tree at a specified offset in the
literal judge graph; a verified occurrence supplies all real parent lookups. -/
inductive Located (g : List Node) : Nat → Tree → Prop
  | secret {b} : g[b]? = some .source → Located g b .secret
  | hash {b t} : Located g b t → g[b+t.nodes]? = some (.unary (b+t.nodes-1)) →
      Located g b (.hash t)
  | join {b l r} : Located g b l → Located g (b+l.nodes) r →
      g[b+l.nodes+r.nodes]? = some (.binary (b+l.nodes-1) (b+l.nodes+r.nodes-1)) →
      Located g b (.join l r)

theorem after_prefix {α : Type} (pref rest : List α) (j : Nat) :
    (pref++rest)[pref.length+j]? = rest[j]? := by
  induction pref with
  | nil => simp
  | cons x xs ih => simpa [Nat.succ_add] using ih

theorem before_suffix {α : Type} (xs tail : List α) {j : Nat} {v : α}
    (h : xs[j]? = some v) : (xs++tail)[j]? = some v := by
  induction xs generalizing j with
  | nil => simp at h
  | cons x xs ih => cases j <;> simp_all

private def Inside (g : List Node) (b : Nat) (xs : List Node) : Prop :=
  ∀ j v, xs[j]? = some v → g[b+j]? = some v

private theorem within_left {g : List Node} {a b : List Node} {off : Nat}
    (h : Inside g off (a++b)) : Inside g off a := by
  intro j v hv
  exact h j v (before_suffix a b hv)

private theorem within_right {g : List Node} {a b : List Node} {off : Nat}
    (h : Inside g off (a++b)) : Inside g (off+a.length) b := by
  intro j v hv
  have hlookup := h (a.length+j) v ((after_prefix a b j).trans hv)
  simpa [Nat.add_assoc] using hlookup

private theorem inside_last {g : List Node} {xs : List Node} {v : Node} {off : Nat}
    (h : Inside g off (xs++[v])) : g[off+xs.length]? = some v := by
  have hh := within_right h 0 v (by simp)
  simpa using hh

private theorem located_of_inside (t : Tree) {g : List Node} (b : Nat)
    (h : Inside g b (t.emit b)) : Located g b t := by
  induction t generalizing b with
  | secret => exact .secret (by simpa using h 0 .source (by rfl))
  | hash t ih =>
    exact .hash (ih b (within_left h)) (by simpa [Tree.emit_length] using inside_last h)
  | join l r il ir =>
    have leftRight := within_left h
    have right := within_right leftRight
    have hr : Inside g (b+l.nodes) (r.emit (b+l.nodes)) := by
      simpa only [Tree.emit_length] using right
    refine .join (il b (within_left leftRight)) (ir (b+l.nodes) hr) ?_
    simpa [Tree.emit_length, Nat.add_assoc] using inside_last h

theorem emitted_located (t : Tree) : Located (t.emit 0) 0 t := by
  apply located_of_inside
  intro j v h
  simpa using h

/-- A stopping prefix frontier in the actual addressed tree. The record stores
only verifier conditions relevant to traversed vertices. -/
inductive Traversal (s p : List Bool) : (b : Nat) → (t : Tree) → List Nat → Prop
  | stop {b t} : get s (b+t.nodes-1) = true → Traversal s p b t [b+t.nodes-1]
  | hash {b t xs} : get s (b+t.nodes) = false → get p (b+t.nodes) = true →
      Traversal s p b t xs → Traversal s p b (.hash t) xs
  | join {b l r xs ys} : get s (b+l.nodes+r.nodes) = false →
      get p (b+l.nodes+r.nodes) = true → Traversal s p b l xs →
      Traversal s p (b+l.nodes) r ys → Traversal s p b (.join l r) (xs++ys)

theorem Traversal.cut {g s p b t xs} (tr : Traversal s p b t xs) (loc : Located g b t) :
    Cut g s p (b+t.nodes-1) xs := by
  induction tr with
  | stop hs => exact .leaf hs
  | hash hs hp child ih =>
    cases loc with
    | hash sub hn =>
      simpa [Tree.nodes, Nat.add_assoc] using Cut.unary hn hs hp (ih sub)
  | join hs hp left right il ir =>
    cases loc with
    | join hl hr hn =>
      have hh := Cut.binary hn hs hp (il hl) (ir hr)
      convert hh using 1 <;> simp only [Tree.nodes] <;> omega

end PoissonDAG.PORS
