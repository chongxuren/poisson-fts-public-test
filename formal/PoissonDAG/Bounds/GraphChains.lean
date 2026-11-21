import PoissonDAG.Core.GraphFacts
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic

/-!
# A bounded partition into derivability chains

The partition key removes just one selected disclosure. Unused disclosures and
public-root disclosures remain subject to exactly the same rule as every other
vertex. Multiple accepted raw encodings may have the same disclosure set.
-/

namespace PoissonDAG

def chainCount (nodes words : Nat) : Nat :=
  ∑ j ∈ Finset.range words, Nat.choose (nodes - 1) j

theorem chainCount_mono_nodes {n m : Nat} (hnm : n ≤ m) (words : Nat) :
    chainCount n words ≤ chainCount m words := by
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.choose_le_choose j (Nat.sub_le_sub_right hnm 1)

theorem chainCount_mono_words (nodes : Nat) {a b : Nat} (hab : a ≤ b) :
    chainCount nodes a ≤ chainCount nodes b := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (by
    intro j hj hj'
    exact Nat.zero_le _)

/-- All possible residual sets, grouped by their cardinality. -/
def chainUniverse (nodes words : Nat) : Finset (Finset Nat) :=
  (Finset.range words).biUnion (fun j => (Finset.range (nodes - 1)).powersetCard j)

@[simp] theorem mem_chainUniverse {nodes words : Nat} {a : Finset Nat} :
    a ∈ chainUniverse nodes words ↔
      a ⊆ Finset.range (nodes - 1) ∧ a.card < words := by
  simp only [chainUniverse, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨j, hj, ha, hcard⟩
    exact ⟨ha, by simpa [hcard] using hj⟩
  · rintro ⟨ha, hcard⟩
    exact ⟨a.card, hcard, ha, rfl⟩

theorem chainUniverse_card (nodes words : Nat) :
    (chainUniverse nodes words).card = chainCount nodes words := by
  rw [chainUniverse, Finset.card_biUnion]
  · simp [chainCount, Finset.card_powersetCard]
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    exact hij ((Finset.mem_powersetCard.mp hai).2.symm.trans
      (Finset.mem_powersetCard.mp haj).2)

theorem chainCount_pos {nodes words : Nat} (hw : 0 < words) : 0 < chainCount nodes words := by
  rw [← chainUniverse_card]
  apply Finset.card_pos.mpr
  refine ⟨∅, ?_⟩
  simp [hw]

def Scheme.chainKey (s : Scheme) (raw : Nat) : Finset Nat :=
  residual s.graph (s.disclosures raw) (s.graph.length - 1)

theorem Scheme.chainKey_mem (s : Scheme) (hs : s.WellFormed) (hc : s.Correct)
    {raw : Nat} (hr : raw ∈ s.accepted) :
    s.chainKey raw ∈ chainUniverse s.graph.length s.maxWords := by
  apply mem_chainUniverse.mpr
  constructor
  · intro i hi
    have hin : i ∈ s.disclosures raw := Finset.mem_of_mem_erase hi
    have hib : i < s.graph.length := Finset.mem_range.mp (s.disclosures_subset hs raw hin)
    have hne : i ≠ s.graph.length - 1 := by
      intro heq
      subst i
      exact root_not_mem_residual s.graph (s.disclosures raw) (s.graph.length - 1) hi
    exact Finset.mem_range.mpr (by omega)
  · have hcard := residual_card_add_one (s.graphValid hs) (s.disclosures raw)
      (s.graph.length - 1) (s.correct_derives hc hr)
    have hbound := s.disclosures_card_le hr
    change (residual s.graph (s.disclosures raw) (s.graph.length - 1)).card < _
    omega

/-- Two accepted encodings in one partition class have comparable complete
disclosure sets. No pointwise bound on honest verification work is assumed. -/
theorem Scheme.same_chain_comparable (s : Scheme) (hs : s.WellFormed) (hc : s.Correct)
    {x y : Nat} (hx : x ∈ s.accepted) (hy : y ∈ s.accepted)
    (hkey : s.chainKey x = s.chainKey y) :
    (∀ i ∈ s.disclosures x, Derives s.graph (s.disclosures y) i) ∨
      (∀ i ∈ s.disclosures y, Derives s.graph (s.disclosures x) i) :=
  residual_comparable (s.graphValid hs) _ _ _
    (s.correct_derives hc hx) (s.correct_derives hc hy) hkey

end PoissonDAG
