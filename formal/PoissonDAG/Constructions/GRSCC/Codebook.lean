import PoissonDAG.Constructions.GRSCC.Graph

/-!
# Canonical bounded constant-sum codebook

The codebook is generated lexicographically from bounded digits and the exact
sum constraint. It is a parameter-only table, not entrant-supplied advice. Raw
acceptance uses disjoint 32-bit threshold and 138-bit rank fields. This module
specifies the finite decoder; no theorem here identifies it with a literal
Boolean `Circuit` until a circuit compilation/refinement theorem is supplied.
-/
namespace PoissonDAG.GRSCC

/-- Lexicographic bounded constant-sum codebook. -/
def codebook : Nat → Nat → List (List Nat)
  | 0, e => if e = 0 then [[]] else []
  | k + 1, e => (List.range (min (capacity + 1) (e + 1))).flatMap
      (fun d => (codebook k (e - d)).map (d :: ·))

theorem codebook_length (k e : Nat) : (codebook k e).length = codeCount k e := by
  induction k generalizing e with
  | zero => by_cases he : e = 0 <;> simp [codebook, codeCount, he]
  | succ k ih => simp [codebook, codeCount, List.length_flatMap, ih]

theorem codebook_nodup (k e : Nat) : (codebook k e).Nodup := by
  induction k generalizing e with
  | zero => simp only [codebook]; split_ifs <;> simp
  | succ k ih =>
      unfold codebook
      apply List.nodup_flatMap.mpr
      refine ⟨?_, ?_⟩
      · intro d hd
        apply List.Nodup.map (fun left right h => (List.cons.inj h).2)
        exact ih (e - d)
      · apply List.nodup_range.imp
        intro a b hab x hx hy
        obtain ⟨left, _, hleft⟩ := List.mem_map.mp hx
        obtain ⟨right, _, hright⟩ := List.mem_map.mp hy
        exact hab (List.cons.inj (hleft.trans hright.symm)).1

theorem codebook_sound (k e : Nat) (digits : List Nat)
    (h : digits ∈ codebook k e) :
    digits.length = k ∧ digits.sum = e ∧ ∀ d ∈ digits, d ≤ capacity := by
  induction k generalizing e digits with
  | zero =>
      simp only [codebook] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst digits
        simp_all
      · simp at h
  | succ k ih =>
      simp only [codebook, List.mem_flatMap, List.mem_map] at h
      obtain ⟨d, hd, rest, hrest, rfl⟩ := h
      obtain ⟨hlen, hsum, hcap⟩ := ih (e - d) rest hrest
      have hdmin : d < min (capacity + 1) (e + 1) := List.mem_range.mp hd
      have hdcap : d ≤ capacity := by omega
      have hde : d ≤ e := by omega
      refine ⟨by simp [hlen], ?_, ?_⟩
      · simp only [List.sum_cons, hsum]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with hxd | hxr
        · simpa [hxd] using hdcap
        · exact hcap x hxr

theorem codebook_complete (k e : Nat) (digits : List Nat)
    (hlen : digits.length = k) (hsum : digits.sum = e)
    (hcap : ∀ d ∈ digits, d ≤ capacity) : digits ∈ codebook k e := by
  induction k generalizing e digits with
  | zero =>
      have hnil : digits = [] := List.length_eq_zero_iff.mp hlen
      subst digits
      have he : e = 0 := by simpa using hsum.symm
      subst e
      simp [codebook]
  | succ k ih =>
      cases digits with
      | nil => simp at hlen
      | cons d rest =>
          have hrestlen : rest.length = k := by simpa using hlen
          have hdcap : d ≤ capacity := hcap d (by simp)
          have hde : d ≤ e := by simp only [List.sum_cons] at hsum; omega
          have hd : d ∈ List.range (min (capacity + 1) (e + 1)) := by
            apply List.mem_range.mpr
            omega
          have hrestsum : rest.sum = e - d := by
            simp only [List.sum_cons] at hsum
            omega
          have hrestcap : ∀ x ∈ rest, x ≤ capacity :=
            fun x hx => hcap x (by simp [hx])
          apply List.mem_flatMap.mpr
          refine ⟨d, hd, ?_⟩
          apply List.mem_map.mpr
          exact ⟨rest, ih (e - d) rest hrestlen hrestsum hrestcap, rfl⟩

/-- The concrete table is computationally defined but sealed to elaboration.
All mathematical uses go through its proved generator equation and invariants. -/
@[irreducible] def canonicalBook : List (List Nat) := codebook positionCount depthSum

theorem canonicalBook_eq : canonicalBook = codebook positionCount depthSum := by
  unfold canonicalBook
  rfl

theorem canonicalBook_length : canonicalBook.length = codeCardinality := by
  rw [canonicalBook_eq, codebook_length, codeCount_fixed_eq]

theorem canonicalBook_nodup : canonicalBook.Nodup := by
  rw [canonicalBook_eq]
  exact codebook_nodup _ _

def decodedDigits (rank : Fin codeCardinality) : List Nat :=
  canonicalBook[rank.val]'(by
    rw [canonicalBook_length]
    exact rank.isLt)

theorem decodedDigits_injective : Function.Injective decodedDigits := by
  intro left right h
  have hl : left.val < canonicalBook.length := by
    rw [canonicalBook_length]
    exact left.isLt
  have hr : right.val < canonicalBook.length := by
    rw [canonicalBook_length]
    exact right.isLt
  have hi : left.val = right.val :=
    (canonicalBook_nodup.getElem_inj_iff
      (hi := hl) (hj := hr)).mp h
  exact Fin.ext hi

theorem decodedDigits_sound (rank : Fin codeCardinality) :
    (decodedDigits rank).length = 6 ∧ (decodedDigits rank).sum = 16 ∧
      ∀ d ∈ decodedDigits rank, d ≤ 8 := by
  have hmem : decodedDigits rank ∈ canonicalBook :=
    List.getElem_mem (by rw [canonicalBook_length]; exact rank.isLt)
  rw [canonicalBook_eq] at hmem
  have h := codebook_sound positionCount depthSum (decodedDigits rank) hmem
  simpa [positionCount, treeHeight, depthSum, capacity] using h

def decodedDepth (rank : Fin codeCardinality) (i : CodePosition) : Fin 9 :=
  let digits := decodedDigits rank
  have hi : i.val < digits.length := by
    rw [(decodedDigits_sound rank).1]
    exact i.isLt
  ⟨digits[i.val], by
    have h := (decodedDigits_sound rank).2.2 digits[i.val] (List.getElem_mem hi)
    omega⟩

theorem decodedDepth_sum (rank : Fin codeCardinality) :
    Finset.univ.sum (fun i => (decodedDepth rank i).val) = 16 := by
  have hlen := (decodedDigits_sound rank).1
  have hsum := (decodedDigits_sound rank).2.1
  have hlist : List.ofFn (fun i : Fin 6 => (decodedDepth rank i).val) =
      decodedDigits rank := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi₁ hi₂
      rw [List.getElem_ofFn]
      rfl
  calc
    Finset.univ.sum (fun i => (decodedDepth rank i).val) =
        (List.ofFn (fun i : Fin 6 => (decodedDepth rank i).val)).sum :=
          (List.sum_ofFn (f := fun i : Fin 6 => (decodedDepth rank i).val)).symm
    _ = (decodedDigits rank).sum := congrArg List.sum hlist
    _ = 16 := hsum

def decodedCodeword (rank : Fin codeCardinality) : Codeword :=
  ⟨decodedDepth rank, decodedDepth_sum rank⟩

theorem decodedCodeword_injective : Function.Injective decodedCodeword := by
  intro left right h
  apply decodedDigits_injective
  apply List.ext_getElem
  · rw [(decodedDigits_sound left).1, (decodedDigits_sound right).1]
  · intro i hi₁ hi₂
    have hi : i < 6 := by simpa only [(decodedDigits_sound left).1] using hi₁
    have hdepth := congrArg (fun c : Codeword => (c.depth ⟨i, hi⟩).val) h
    simpa only [decodedCodeword, decodedDepth] using hdepth

theorem decodedCodeword_surjective : Function.Surjective decodedCodeword := by
  intro code
  let digits := List.ofFn (fun i : CodePosition => (code.depth i).val)
  have hlen : digits.length = positionCount := by simp [digits, positionCount, treeHeight]
  have hsum : digits.sum = depthSum := by
    simpa only [digits, List.sum_ofFn, depthSum] using code.sum_eq
  have hcap : ∀ d ∈ digits, d ≤ capacity := by
    intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    have hi := (code.depth i).isLt
    dsimp [capacity]
    omega
  have hmem := codebook_complete positionCount depthSum digits hlen hsum hcap
  rw [← canonicalBook_eq] at hmem
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hirank : i < codeCardinality := by
    simpa only [canonicalBook_length] using hi
  refine ⟨⟨i, hirank⟩, ?_⟩
  apply Codeword.ext
  intro j
  apply Fin.ext
  have hdecoded : decodedDigits ⟨i, hirank⟩ = digits := hget
  have hval := congrArg (fun ds : List Nat => ds[j.val]?.getD 0) hdecoded
  have hdigits_val : digits[j.val]?.getD 0 = (code.depth j).val := by
    dsimp only [digits]
    rw [List.getElem?_ofFn, dif_pos j.isLt]
    rfl
  rw [hdigits_val] at hval
  have hj : j.val < (decodedDigits ⟨i, hirank⟩).length := by
    rw [(decodedDigits_sound ⟨i, hirank⟩).1]
    exact j.isLt
  rw [List.getElem?_eq_getElem hj] at hval
  change (decodedDigits ⟨i, hirank⟩)[j.val] = (code.depth j).val at hval ⊢
  exact hval

end PoissonDAG.GRSCC
