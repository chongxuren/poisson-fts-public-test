import PoissonDAG.Constructions.GRSCC.Encoding
import PoissonDAG.Constructions.GRSCC.Law
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.FieldSimp

/-! The exact route law for the protected Scheme.accepted list. Every
accepted-list index is a threshold coordinate and an actual decoded route;
product tuples therefore retain their independent uniform route law. -/
namespace PoissonDAG.GRSCC

open scoped BigOperators
set_option maxHeartbeats 20000

def acceptedElementEquiv (encoder : Circuit) (href : CircuitRefines encoder) :
    {raw // raw ∈ (schemeOfCircuit encoder).accepted} ≃ ↥acceptedRawSet where
  toFun raw := ⟨raw.val, by
    rw [← accepted_toFinset_of_refinement encoder href]
    exact List.mem_toFinset.mpr raw.property⟩
  invFun raw := ⟨raw.val, by
    apply List.mem_toFinset.mp
    rw [accepted_toFinset_of_refinement encoder href]
    exact raw.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def acceptedIndexRaw (encoder : Circuit) (href : CircuitRefines encoder)
    (i : Fin (schemeOfCircuit encoder).accepted.length) : ↥acceptedRawSet :=
  acceptedElementEquiv encoder href
    ((scheme_accepted_nodup _).getEquiv (schemeOfCircuit encoder).accepted i)

theorem acceptedIndexRaw_val (encoder : Circuit) (href : CircuitRefines encoder)
    (i : Fin (schemeOfCircuit encoder).accepted.length) :
    (acceptedIndexRaw encoder href i).val = (schemeOfCircuit encoder).accepted[i] := rfl

noncomputable def acceptedIndexEquiv (encoder : Circuit) (href : CircuitRefines encoder) :
    Fin (schemeOfCircuit encoder).accepted.length ≃ Fin threshold × Route :=
  ((scheme_accepted_nodup _).getEquiv (schemeOfCircuit encoder).accepted).trans
    ((acceptedElementEquiv encoder href).trans
      (acceptedPairEquiv.trans (Equiv.prodCongr (Equiv.refl _) routeEquiv)))

def acceptedIndexRoute (encoder : Circuit) (href : CircuitRefines encoder)
    (i : Fin (schemeOfCircuit encoder).accepted.length) : Route :=
  decodeAccepted (acceptedIndexRaw encoder href i)

theorem acceptedIndexEquiv_route (encoder : Circuit) (href : CircuitRefines encoder)
    (i : Fin (schemeOfCircuit encoder).accepted.length) :
    (acceptedIndexEquiv encoder href i).2 = acceptedIndexRoute encoder href i := by
  change routeEquiv (acceptedPairEquiv (acceptedIndexRaw encoder href i)).2 = _
  rw [routeEquiv_apply]
  rfl

theorem decodeRaw_acceptedIndex (encoder : Circuit) (href : CircuitRefines encoder)
    (i : Fin (schemeOfCircuit encoder).accepted.length) :
    decodeRaw (schemeOfCircuit encoder).accepted[i] =
      some (acceptedIndexRoute encoder href i) := by
  let raw := acceptedIndexRaw encoder href i
  have hfields := (mem_acceptedRawSet raw.val).mp raw.property
  rw [← acceptedIndexRaw_val encoder href i]
  change decodeRaw raw.val = some (decodeAccepted raw)
  simp only [decodeRaw, dif_pos hfields.2, decodeAccepted]

theorem frontier_acceptedIndex (encoder : Circuit) (href : CircuitRefines encoder)
    (i : Fin (schemeOfCircuit encoder).accepted.length) :
    (schemeOfCircuit encoder).frontier (schemeOfCircuit encoder).accepted[i] =
      (acceptedIndexRoute encoder href i).frontier := by
  have hbound := ((mem_acceptedRawSet _).mp (acceptedIndexRaw encoder href i).property).1
  rw [acceptedIndexRaw_val] at hbound
  exact scheme_frontier_of_refinement encoder href _ hbound _
    (decodeRaw_acceptedIndex encoder href i)

theorem plan_acceptedIndex (encoder : Circuit) (href : CircuitRefines encoder)
    (i : Fin (schemeOfCircuit encoder).accepted.length) :
    (schemeOfCircuit encoder).plan (schemeOfCircuit encoder).accepted[i] =
      (acceptedIndexRoute encoder href i).plan := by
  have hbound := ((mem_acceptedRawSet _).mp (acceptedIndexRaw encoder href i).property).1
  rw [acceptedIndexRaw_val] at hbound
  exact scheme_plan_of_refinement encoder href _ hbound _
    (decodeRaw_acceptedIndex encoder href i)

noncomputable def acceptedTupleEquiv (encoder : Circuit) (href : CircuitRefines encoder)
    (q : Nat) : (Fin q → Fin (schemeOfCircuit encoder).accepted.length) ≃
      (Fin q → Fin threshold) × (Fin q → Route) :=
  (Equiv.piCongrRight (fun _ : Fin q => acceptedIndexEquiv encoder href)).trans
    (Equiv.arrowProdEquivProdArrow (Fin q) (fun _ => Fin threshold) (fun _ => Route))

theorem acceptedTupleEquiv_routes (encoder : Circuit) (href : CircuitRefines encoder)
    (q : Nat) (sample : Fin q → Fin (schemeOfCircuit encoder).accepted.length) :
    (acceptedTupleEquiv encoder href q sample).2 =
      fun j => acceptedIndexRoute encoder href (sample j) := by
  funext j
  exact acceptedIndexEquiv_route encoder href (sample j)

/-- Additive test-function identity, valid for every tuple length, including
zero. Instantiating q+1 gives q histories and the independent target. -/
theorem acceptedTuple_pushforward {A : Type*} [AddCommMonoid A]
    (encoder : Circuit) (href : CircuitRefines encoder) (q : Nat)
    (f : (Fin q → Route) → A) :
    (∑ sample : Fin q → Fin (schemeOfCircuit encoder).accepted.length,
      f (fun j => acceptedIndexRoute encoder href (sample j))) =
      threshold ^ q • ∑ routes : Fin q → Route, f routes := by
  calc
    _ = ∑ pair : (Fin q → Fin threshold) × (Fin q → Route), f pair.2 := by
      apply Fintype.sum_equiv (acceptedTupleEquiv encoder href q)
      intro sample
      rw [acceptedTupleEquiv_routes]
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin]

theorem acceptedTuple_pushforward_rat (encoder : Circuit) (href : CircuitRefines encoder)
    (q : Nat) (f : (Fin q → Route) → ℚ) :
    (∑ sample : Fin q → Fin (schemeOfCircuit encoder).accepted.length,
      f (fun j => acceptedIndexRoute encoder href (sample j))) =
      (threshold : ℚ) ^ q * ∑ routes : Fin q → Route, f routes := by
  simpa only [nsmul_eq_mul, Nat.cast_pow] using
    acceptedTuple_pushforward encoder href q f

/-- Uniform accepted indices induce precisely uniform independent routes. -/
theorem acceptedTuple_uniform (encoder : Circuit) (href : CircuitRefines encoder)
    (q : Nat) (f : (Fin q → Route) → ℚ) :
    (∑ sample : Fin q → Fin (schemeOfCircuit encoder).accepted.length,
      f (fun j => acceptedIndexRoute encoder href (sample j))) /
        ((schemeOfCircuit encoder).accepted.length : ℚ) ^ q =
      (∑ routes : Fin q → Route, f routes) / (encodingCardinality : ℚ) ^ q := by
  have hthreshold : (threshold : ℚ) ≠ 0 := by norm_num [threshold]
  have hencoding : (encodingCardinality : ℚ) ≠ 0 := by
    norm_num [encodingCardinality, coordinateRadix, codeCardinality, slotCount,
      treeHeight, bucketCount, bucketBits, initialOwnerCount, initialOwnerBits, layerCount]
  rw [acceptedTuple_pushforward_rat, accepted_count_of_refinement encoder href]
  simp only [Nat.cast_mul, mul_pow]
  field_simp <;> ring

end PoissonDAG.GRSCC
