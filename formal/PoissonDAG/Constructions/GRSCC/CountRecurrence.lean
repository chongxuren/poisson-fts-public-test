import PoissonDAG.Constructions.GRSCC.Kernel
import PoissonDAG.Probability.FiniteKernels
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! Dense positive-count lists implement the finite state kernel exactly. -/
namespace PoissonDAG.GRSCC

open scoped BigOperators

abbrev OwnerState (q : Nat) := Finset (Fin q)
abbrev OwnerCount (q : Nat) := Fin (q + 1)

def ownerIndex {q : Nat} (state : OwnerState q) : OwnerCount q :=
  ⟨state.card, by
    have h := Finset.card_le_univ state
    simpa using Nat.lt_succ_of_le h⟩

def countKernel (q : Nat) (source target : OwnerCount q) : ℚ :=
  jointKernel q source.val target.val

theorem jointKernel_source_zero (q next : Nat) : jointKernel q 0 next = 0 := by
  simp [jointKernel]

theorem jointKernel_target_zero (q current : Nat) : jointKernel q current 0 = 0 := by
  simp [jointKernel]

theorem countStep_at_zero {q : Nat} (mass : OwnerCount q → ℚ) :
    FiniteKernels.step (countKernel q) mass 0 = 0 := by
  simp [FiniteKernels.step, countKernel, jointKernel_target_zero]

/-- Positive counts are stored densely; the discarded zero source has a zero row. -/
def positiveState {q : Nat} (mass : OwnerCount q → ℚ) : List ℚ :=
  List.ofFn (fun i : Fin q => mass i.succ)

theorem map_range_eq_ofFn {α : Type} (q : Nat) (f : Nat → α) :
    (List.range q).map f = List.ofFn (fun i : Fin q => f i.val) := by
  simpa using (List.ofFn_getElem_eq_map (List.range q) f).symm

private theorem sum_map_range_fin (q : Nat) (f : Nat → ℚ) :
    ((List.range q).map f).sum = ∑ i : Fin q, f i.val := by
  rw [map_range_eq_ofFn, Fin.sum_ofFn]

theorem kernelStep_positiveState {q : Nat} (mass : OwnerCount q → ℚ) :
    kernelStep q (positiveState mass) =
      positiveState (FiniteKernels.step (countKernel q) mass) := by
  unfold kernelStep positiveState
  rw [map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext target
  rw [sum_map_range_fin, FiniteKernels.step, Fin.sum_univ_succ]
  simp only [countKernel, Fin.val_zero, jointKernel_source_zero, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro source hsource
  simp [List.getElem?_ofFn, source.isLt, Fin.val_succ]

theorem positiveState_iterate {q : Nat} (mass : OwnerCount q → ℚ) (n : Nat) :
    ((kernelStep q)^[n] (positiveState mass)) =
      positiveState ((FiniteKernels.step (countKernel q))^[n] mass) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        kernelStep_positiveState]

theorem positiveState_sum {q : Nat} (mass : OwnerCount q → ℚ) (hzero : mass 0 = 0) :
    (positiveState mass).sum = ∑ count, mass count := by
  rw [Fin.sum_univ_succ, hzero, zero_add]
  exact Fin.sum_ofFn _

end PoissonDAG.GRSCC
