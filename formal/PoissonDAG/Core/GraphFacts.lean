import PoissonDAG.Model
import Mathlib.Data.Finset.Card

/-!
# Forward derivation in an AND-DAG

`Derives` describes precisely the permitted graph rules. In particular, a source
has no derivation rule: it must be disclosed. The fixed-parent selector below
stops at the first disclosure on a single backward path. It does not normalize
or discard any other disclosure.
-/

namespace PoissonDAG

/-- The topological condition already present in `Scheme.WellFormed`. -/
def GraphValid (graph : List Node) : Prop :=
  ∀ (i : Nat) (node : Node), graph[i]? = some node → node.ValidAt i

/-- Derivability from the complete, possibly redundant disclosure set. -/
inductive Derives (graph : List Node) (disclosed : Finset Nat) : Nat → Prop
  | disclosed {i} : i ∈ disclosed → Derives graph disclosed i
  | unary {i p} : graph[i]? = some (.unary p) →
      Derives graph disclosed p → Derives graph disclosed i
  | binary {i l r} : graph[i]? = some (.binary l r) →
      Derives graph disclosed l → Derives graph disclosed r → Derives graph disclosed i

theorem Derives.mono {graph : List Node} {a b : Finset Nat}
    (hab : a ⊆ b) {i : Nat} (h : Derives graph a i) : Derives graph b i := by
  induction h with
  | disclosed hi => exact .disclosed (hab hi)
  | unary hn _ ih => exact .unary hn ih
  | binary hn _ _ ihl ihr => exact .binary hn ihl ihr

theorem derives_source_iff {graph : List Node} {a : Finset Nat} {i : Nat}
    (hn : graph[i]? = some .source) : Derives graph a i ↔ i ∈ a := by
  constructor
  · intro h
    cases h with
    | disclosed hi => exact hi
    | unary hn' _ => simp_all
    | binary hn' _ _ => simp_all
  · exact Derives.disclosed

theorem derives_unary_iff {graph : List Node} {a : Finset Nat} {i p : Nat}
    (hn : graph[i]? = some (.unary p)) :
    Derives graph a i ↔ i ∈ a ∨ Derives graph a p := by
  constructor
  · intro h
    cases h with
    | disclosed hi => exact Or.inl hi
    | unary hn' hp => simp_all
    | binary hn' _ _ => simp_all
  · rintro (hi | hp)
    · exact .disclosed hi
    · exact .unary hn hp

theorem derives_binary_iff {graph : List Node} {a : Finset Nat} {i l r : Nat}
    (hn : graph[i]? = some (.binary l r)) :
    Derives graph a i ↔ i ∈ a ∨ (Derives graph a l ∧ Derives graph a r) := by
  constructor
  · intro h
    cases h with
    | disclosed hi => exact Or.inl hi
    | unary hn' _ => simp_all
    | binary hn' hl hr => simp_all
  · rintro (hi | ⟨hl, hr⟩)
    · exact .disclosed hi
    · exact .binary hn hl hr

theorem derives_of_missing_iff {graph : List Node} {a : Finset Nat} {i : Nat}
    (hn : graph[i]? = none) : Derives graph a i ↔ i ∈ a := by
  constructor
  · intro h
    cases h with
    | disclosed hi => exact hi
    | unary hn' _ => simp_all
    | binary hn' _ _ => simp_all
  · exact Derives.disclosed

/-- Follow the unary parent or the left binary parent, stopping at the first
disclosed vertex. The guards make this total even for malformed input graphs. -/
def pivot (graph : List Node) (a : Finset Nat) (i : Nat) : Nat :=
  if i ∈ a then i else
  match graph[i]? with
  | some (.unary p) => if _h : p < i then pivot graph a p else i
  | some (.binary l _) => if _h : l < i then pivot graph a l else i
  | _ => i
termination_by i

theorem pivot_of_mem {graph : List Node} {a : Finset Nat} {i : Nat} (hi : i ∈ a) :
    pivot graph a i = i := by
  conv =>
    lhs
    rw [pivot]
  exact if_pos hi

theorem pivot_unary {graph : List Node} {a : Finset Nat} {i p : Nat}
    (hn : graph[i]? = some (.unary p)) (hp : p < i) (hi : i ∉ a) :
    pivot graph a i = pivot graph a p := by
  conv =>
    lhs
    rw [pivot]
  simp only [if_neg hi, hn, dif_pos hp]

theorem pivot_binary {graph : List Node} {a : Finset Nat} {i l r : Nat}
    (hn : graph[i]? = some (.binary l r)) (hl : l < i) (hi : i ∉ a) :
    pivot graph a i = pivot graph a l := by
  conv =>
    lhs
    rw [pivot]
  simp only [if_neg hi, hn, dif_pos hl]

theorem pivot_mem {graph : List Node} (hg : GraphValid graph) (a : Finset Nat)
    (i : Nat) (hi : Derives graph a i) : pivot graph a i ∈ a := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases ha : i ∈ a
    · simpa only [pivot_of_mem ha] using ha
    cases hn : graph[i]? with
    | none => exact False.elim (ha ((derives_of_missing_iff hn).mp hi))
    | some node =>
      cases node with
      | source => exact False.elim (ha ((derives_source_iff hn).mp hi))
      | unary p =>
        have hp : p < i := hg i _ hn
        have hd : Derives graph a p := ((derives_unary_iff hn).mp hi).resolve_left ha
        rw [pivot_unary hn hp ha]
        exact ih p hp hd
      | binary l r =>
        have hl : l < i := (hg i _ hn).1
        have hd : Derives graph a l :=
          (((derives_binary_iff hn).mp hi).resolve_left ha).1
        rw [pivot_binary hn hl ha]
        exact ih l hl hd

theorem not_derives_empty {graph : List Node} (hg : GraphValid graph) (i : Nat) :
    ¬ Derives graph ∅ i := by
  intro hi
  simpa using pivot_mem hg ∅ i hi

/-- The first disclosures on a common fixed path are comparable. This proof
uses only descent along that path; it does not assume that the disclosed sets
are minimal cuts, visited frontiers, or free of unused vertices. -/
theorem pivot_comparable {graph : List Node} (hg : GraphValid graph)
    (a b : Finset Nat) (i : Nat) (ha : Derives graph a i) (hb : Derives graph b i) :
    Derives graph b (pivot graph a i) ∨ Derives graph a (pivot graph b i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hai : i ∈ a
    · exact Or.inl (by simpa only [pivot_of_mem hai] using hb)
    by_cases hbi : i ∈ b
    · exact Or.inr (by simpa only [pivot_of_mem hbi] using ha)
    cases hn : graph[i]? with
    | none => exact False.elim (hai ((derives_of_missing_iff hn).mp ha))
    | some node =>
      cases node with
      | source => exact False.elim (hai ((derives_source_iff hn).mp ha))
      | unary p =>
        have hp : p < i := hg i _ hn
        have hap := ((derives_unary_iff hn).mp ha).resolve_left hai
        have hbp := ((derives_unary_iff hn).mp hb).resolve_left hbi
        rw [pivot_unary hn hp hai, pivot_unary hn hp hbi]
        exact ih p hp hap hbp
      | binary l r =>
        have hl : l < i := (hg i _ hn).1
        have hal := (((derives_binary_iff hn).mp ha).resolve_left hai).1
        have hbl := (((derives_binary_iff hn).mp hb).resolve_left hbi).1
        rw [pivot_binary hn hl hai, pivot_binary hn hl hbi]
        exact ih l hl hal hbl

/-- Retain every disclosure except for the first one on the chosen path. -/
def residual (graph : List Node) (a : Finset Nat) (root : Nat) : Finset Nat :=
  a.erase (pivot graph a root)

theorem root_not_mem_residual (graph : List Node) (a : Finset Nat) (root : Nat) :
    root ∉ residual graph a root := by
  by_cases hr : root ∈ a
  · simp [residual, pivot_of_mem hr]
  · exact fun h => hr (Finset.mem_of_mem_erase h)

theorem residual_card_add_one {graph : List Node} (hg : GraphValid graph)
    (a : Finset Nat) (root : Nat) (hr : Derives graph a root) :
    (residual graph a root).card + 1 = a.card := by
  exact Finset.card_erase_add_one (pivot_mem hg a root hr)

theorem residual_comparable {graph : List Node} (hg : GraphValid graph)
    (a b : Finset Nat) (root : Nat) (ha : Derives graph a root)
    (hb : Derives graph b root)
    (hab : residual graph a root = residual graph b root) :
    (∀ i ∈ a, Derives graph b i) ∨ (∀ i ∈ b, Derives graph a i) := by
  rcases pivot_comparable hg a b root ha hb with hp | hp
  · left
    intro i hi
    by_cases heq : i = pivot graph a root
    · simpa [heq] using hp
    · apply Derives.disclosed
      have hir : i ∈ residual graph a root := Finset.mem_erase.mpr ⟨heq, hi⟩
      rw [hab] at hir
      exact Finset.mem_of_mem_erase hir
  · right
    intro i hi
    by_cases heq : i = pivot graph b root
    · simpa [heq] using hp
    · apply Derives.disclosed
      have hir : i ∈ residual graph b root := Finset.mem_erase.mpr ⟨heq, hi⟩
      rw [← hab] at hir
      exact Finset.mem_of_mem_erase hir

/-! ## The Boolean masks and the actual topological scan -/

/-- A finite-set view of a mask, retaining all its true entries. -/
def maskSet (xs : List Bool) : Finset Nat :=
  (Finset.range xs.length).filter (fun i => get xs i = true)

theorem get_true_lt {xs : List Bool} {i : Nat} (h : get xs i = true) :
    i < xs.length := by
  by_contra hi
  have hn : xs[i]? = none := List.getElem?_eq_none (by omega)
  simp [get, hn] at h

theorem get_set_true_self (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    get (xs.set i true) i = true := by
  simp [get, List.getElem?_set_self hi]

@[simp] theorem mem_maskSet {xs : List Bool} {i : Nat} :
    i ∈ maskSet xs ↔ get xs i = true := by
  simp only [maskSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨get_true_lt h, h⟩⟩

theorem maskSet_cons (b : Bool) (xs : List Bool) :
    maskSet (b :: xs) =
      if b then insert 0 ((maskSet xs).image Nat.succ) else (maskSet xs).image Nat.succ := by
  ext i
  cases i with
  | zero => cases b <;> simp [get]
  | succ i => cases b <;> simp [get, Finset.mem_image]

@[simp] theorem maskSet_card (xs : List Bool) : (maskSet xs).card = weight xs := by
  induction xs with
  | nil => simp [maskSet, weight]
  | cons b xs ih =>
    have hz : 0 ∉ (maskSet xs).image Nat.succ := by simp
    have himg : ((maskSet xs).image Nat.succ).card = (maskSet xs).card :=
      Finset.card_image_of_injective _ Nat.succ_injective
    cases b <;> simp [maskSet_cons, weight, hz, himg, ih]

def closeStep (allowed : List Bool) (state : List Bool × Nat) (entry : Node × Nat) :
    List Bool × Nat :=
  if get state.1 entry.2 then state
  else if get allowed entry.2 && ready state.1 entry.1 then
    (state.1.set entry.2 true, state.2 + 1)
  else state

theorem close_eq_foldl (graph : List Node) (a allowed : List Bool) :
    close graph a allowed = graph.zipIdx.foldl (closeStep allowed) (a, 0) := rfl

@[simp] theorem closeStep_length (allowed : List Bool) (state : List Bool × Nat)
    (entry : Node × Nat) : (closeStep allowed state entry).1.length = state.1.length := by
  simp only [closeStep]
  split
  · rfl
  · split
    · exact List.length_set
    · rfl

theorem closeStep_get_ne (allowed : List Bool) (state : List Bool × Nat)
    (node : Node) {i j : Nat} (hij : i ≠ j) :
    get (closeStep allowed state (node, i)).1 j = get state.1 j := by
  simp only [closeStep]
  split
  · rfl
  · split
    · simp [get, List.getElem?_set_ne hij]
    · rfl

theorem closeStep_get_self (allowed : List Bool) (state : List Bool × Nat)
    (node : Node) {i : Nat} (hi : i < state.1.length) :
    get (closeStep allowed state (node, i)).1 i =
      (get state.1 i || (get allowed i && ready state.1 node)) := by
  cases hk : get state.1 i <;>
    cases ha : get allowed i <;>
    cases hr : ready state.1 node <;>
    simp [closeStep, hk, ha, hr, get_set_true_self state.1 i hi]

theorem closeStep_sound {graph : List Node} {a : Finset Nat} (allowed : List Bool)
    (state : List Bool × Nat) (entry : Node × Nat)
    (hs : ∀ i, get state.1 i = true → Derives graph a i)
    (hn : graph[entry.2]? = some entry.1) :
    ∀ i, get (closeStep allowed state entry).1 i = true → Derives graph a i := by
  rcases entry with ⟨node, j⟩
  intro i hi
  by_cases hij : j = i
  · subst i
    by_cases hk : get state.1 j = true
    · exact hs j hk
    by_cases hr : (get allowed j && ready state.1 node) = true
    · have hr' : ready state.1 node = true := (Bool.and_eq_true_iff.mp hr).2
      cases node with
      | source => simp [ready] at hr'
      | unary p => exact .unary hn (hs p hr')
      | binary l r =>
        exact .binary hn (hs l (Bool.and_eq_true_iff.mp hr').1)
          (hs r (Bool.and_eq_true_iff.mp hr').2)
    · simp [closeStep, hk, hr] at hi
  · exact hs i (by rwa [closeStep_get_ne allowed state node hij] at hi)

theorem fold_closeStep_sound {graph : List Node} {a : Finset Nat}
    (allowed : List Bool) (entries : List (Node × Nat)) (state : List Bool × Nat)
    (hs : ∀ i, get state.1 i = true → Derives graph a i)
    (hn : ∀ entry ∈ entries, graph[entry.2]? = some entry.1) :
    ∀ i, get (entries.foldl (closeStep allowed) state).1 i = true →
      Derives graph a i := by
  induction entries generalizing state with
  | nil => exact hs
  | cons entry entries ih =>
    apply ih (state := closeStep allowed state entry)
    · exact closeStep_sound allowed state entry hs (hn entry (by simp))
    · intro e he
      exact hn e (by simp [he])

/-- Every value computed by the honest, possibly restricted verification plan
is derivable from the entire disclosure mask. -/
theorem close_sound (graph : List Node) (a allowed : List Bool) :
    ∀ i, get (close graph a allowed).1 i = true → Derives graph (maskSet a) i := by
  rw [close_eq_foldl]
  apply fold_closeStep_sound
  · intro i hi
    exact .disclosed (mem_maskSet.mpr hi)
  · intro entry he
    exact List.mem_zipIdx_iff_getElem?.mp he

/-- The invariant of a full scan: the completed prefix agrees with derivability,
and the as yet unvisited suffix still agrees with the original disclosure mask. -/
structure ScanInv (graph : List Node) (a known : List Bool) (k : Nat) : Prop where
  length_eq : known.length = graph.length
  done : ∀ i, i < k → (Derives graph (maskSet a) i ↔ get known i = true)
  future : ∀ i, k ≤ i → get known i = get a i

theorem scanInv_step {graph : List Node} (hg : GraphValid graph) (a : List Bool)
    (_ha : a.length = graph.length) (state : List Bool × Nat) (k : Nat) (node : Node)
    (hn : graph[k]? = some node) (hs : ScanInv graph a state.1 k) :
    ScanInv graph a
      (closeStep (List.replicate graph.length true) state (node, k)).1 (k + 1) := by
  have hk : k < graph.length := (List.getElem?_eq_some_iff.mp hn).choose
  have hkl : k < state.1.length := by simpa [hs.length_eq] using hk
  have hal : get (List.replicate graph.length true) k = true := by
    simp [get, hk]
  have hknown : get state.1 k = get a k := hs.future k le_rfl
  have hderive : Derives graph (maskSet a) k ↔
      get state.1 k = true ∨ ready state.1 node = true := by
    cases node with
    | source => simpa [ready, hknown] using derives_source_iff (a := maskSet a) hn
    | unary p =>
      have hp : p < k := hg k _ hn
      simpa [ready, hknown, hs.done p hp] using derives_unary_iff (a := maskSet a) hn
    | binary l r =>
      have hlr := hg k _ hn
      simpa [ready, hknown, hs.done l hlr.1, hs.done r hlr.2] using
        derives_binary_iff (a := maskSet a) hn
  constructor
  · simpa using (closeStep_length (List.replicate graph.length true) state (node, k)).trans
      hs.length_eq
  · intro i hi
    by_cases hik : i = k
    · subst i
      rw [closeStep_get_self _ _ _ hkl, hal]
      simpa only [Bool.true_and, Bool.or_eq_true] using hderive
    · rw [closeStep_get_ne _ _ _ (Ne.symm hik)]
      exact hs.done i (by omega)
  · intro i hi
    rw [closeStep_get_ne _ _ _ (by omega)]
    exact hs.future i (by omega)

theorem fold_scanInv {graph : List Node} (hg : GraphValid graph) (a : List Bool)
    (ha : a.length = graph.length) (nodes : List Node) (k : Nat)
    (hnodes : ∀ j node, nodes[j]? = some node → graph[k + j]? = some node)
    (state : List Bool × Nat) (hs : ScanInv graph a state.1 k) :
    ScanInv graph a
      ((nodes.zipIdx k).foldl (closeStep (List.replicate graph.length true)) state).1
      (k + nodes.length) := by
  induction nodes generalizing k state with
  | nil => simpa using hs
  | cons node nodes ih =>
    have hn : graph[k]? = some node := by simpa using hnodes 0 node (by simp)
    have hs' := scanInv_step hg a ha state k node hn hs
    have ht : ∀ j n, nodes[j]? = some n → graph[(k + 1) + j]? = some n := by
      intro j n hj
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hnodes (j + 1) n (by simpa using hj)
    simpa [List.zipIdx_cons, List.foldl_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih (k := k + 1) (hnodes := ht)
        (state := closeStep (List.replicate graph.length true) state (node, k)) (hs := hs')

/-- The operational complete topological scan realizes graph derivability. -/
theorem close_complete_iff {graph : List Node} (hg : GraphValid graph)
    (a : List Bool) (ha : a.length = graph.length) {i : Nat} (hi : i < graph.length) :
    get (close graph a (List.replicate graph.length true)).1 i = true ↔
      Derives graph (maskSet a) i := by
  have hs : ScanInv graph a a 0 :=
    ⟨ha, by intro j hj; omega, by intro j hj; rfl⟩
  have hf := fold_scanInv hg a ha graph 0 (by intro j node hn; simpa using hn) (a, 0) hs
  simpa [close_eq_foldl] using (hf.done i (by simpa using hi)).symm

/-- Successful encodings retain all their frontier bits, including unused bits. -/
def Scheme.disclosures (s : Scheme) (raw : Nat) : Finset Nat := maskSet (s.frontier raw)

def Scheme.maxWords (s : Scheme) : Nat :=
  ((s.accepted.map (fun raw => weight (s.frontier raw))).foldl max 0)

theorem Scheme.graphValid (s : Scheme) (hs : s.WellFormed) : GraphValid s.graph := hs.2.2.2.2.1

theorem Circuit.eval_length (c : Circuit) (raw : Nat) : (c.eval raw).length = c.outputs.length := by
  simp [Circuit.eval]

theorem Scheme.frontier_length (s : Scheme) (hs : s.WellFormed) (raw : Nat) :
    (s.frontier raw).length = s.graph.length := by
  simp only [Scheme.frontier, List.length_take, List.length_drop, Circuit.eval_length,
    hs.2.2.2.1]
  omega

theorem Scheme.disclosures_subset (s : Scheme) (hs : s.WellFormed) (raw : Nat) :
    s.disclosures raw ⊆ Finset.range s.graph.length := by
  intro i hi
  exact Finset.mem_range.mpr (by
    simpa [s.frontier_length hs raw] using get_true_lt (mem_maskSet.mp hi))

theorem Scheme.correct_derives (s : Scheme) (hc : s.Correct) {raw : Nat}
    (hr : raw ∈ s.accepted) : Derives s.graph (s.disclosures raw) (s.graph.length - 1) :=
  close_sound s.graph (s.frontier raw) (s.plan raw) _ (hc raw hr)

theorem foldl_max_ge (xs : List Nat) (a : Nat) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (a := max a x))

theorem le_foldl_max_of_mem {xs : List Nat} {x : Nat} (hx : x ∈ xs) (a : Nat) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with hxy | hxy
    · subst x
      exact (le_max_right a y).trans (foldl_max_ge ys (max a y))
    · exact ih (a := max a y) hxy

theorem Scheme.disclosures_card_le (s : Scheme) {raw : Nat} (hr : raw ∈ s.accepted) :
    (s.disclosures raw).card ≤ s.maxWords := by
  change (maskSet (s.frontier raw)).card ≤ _
  rw [maskSet_card]
  change weight (s.frontier raw) ≤
    (s.accepted.map (fun raw => weight (s.frontier raw))).foldl max 0
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr ⟨raw, hr, rfl⟩

theorem Scheme.maxWords_pos (s : Scheme) (hs : s.WellFormed) (hc : s.Correct) :
    0 < s.maxWords := by
  obtain ⟨raw, hr⟩ := List.length_pos_iff_exists_mem.mp hs.2.2.2.2.2
  have hd := s.correct_derives hc hr
  have hp := pivot_mem (s.graphValid hs) (s.disclosures raw) (s.graph.length - 1) hd
  exact (Finset.card_pos.mpr ⟨_, hp⟩).trans_le (s.disclosures_card_le hr)

theorem union_replicate_false (xs : List Bool) :
    union (List.replicate xs.length false) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [union, List.length_cons, List.replicate_succ, List.zip_cons_cons,
      List.map_cons, Bool.false_or] using congrArg (List.cons x) ih

theorem get_set_true_mono (xs : List Bool) (j : Nat) {i : Nat}
    (hi : get xs i = true) : get (xs.set j true) i = true := by
  by_cases hji : j = i
  · subst j
    simp [get, List.getElem?_set_self (get_true_lt hi)]
  · simpa [get, List.getElem?_set_ne hji] using hi

theorem subset_of_pointwise (a b : List Bool)
    (h : ∀ i, get a i = true → get b i = true) : subset a b = true := by
  induction a generalizing b with
  | nil => simp [subset]
  | cons x xs ih =>
    cases b with
    | nil => simp [subset]
    | cons y ys =>
      have hh : (!x || y) = true := by
        have h0 := h 0
        cases x <;> cases y <;> simp_all [get]
      have ht : ∀ i, get xs i = true → get ys i = true := by
        intro i hi
        simpa [get] using h (i + 1) (by simpa [get] using hi)
      simpa [subset, hh] using ih ys ht

/-- If one complete disclosure set is forward derivable from another, then the
protected one-history covering experiment covers it. Granting the public root
can only add information; this includes signatures which already disclose it. -/
theorem Scheme.covered_singleton_of_derives (s : Scheme) (hs : s.WellFormed)
    {history target : Nat} (ht : target ∈ s.accepted)
    (hd : ∀ i ∈ s.disclosures target, Derives s.graph (s.disclosures history) i) :
    s.covered [history] target = true := by
  have hfront := s.frontier_length hs history
  have hunion : union (List.replicate s.graph.length false) (s.frontier history) =
      s.frontier history := by
    rw [← hfront]
    exact union_replicate_false _
  have ha : s.accept target = true := (List.mem_filter.mp ht).2
  change (s.accept target && subset (s.frontier target)
    (close s.graph
      ((union (List.replicate s.graph.length false) (s.frontier history)).set
        (s.graph.length - 1) true)
      (List.replicate s.graph.length true)).1) = true
  rw [hunion, Bool.and_eq_true]
  refine ⟨ha, subset_of_pointwise _ _ ?_⟩
  intro i hi
  have hib : i < s.graph.length := by
    simpa [s.frontier_length hs target] using get_true_lt hi
  apply (close_complete_iff (s.graphValid hs)
    ((s.frontier history).set (s.graph.length - 1) true) (by simpa using hfront) hib).mpr
  apply (hd i (mem_maskSet.mpr hi)).mono
  intro j hj
  exact mem_maskSet.mpr (get_set_true_mono _ _ (mem_maskSet.mp hj))

end PoissonDAG
