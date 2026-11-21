import PoissonDAG.Constructions.FORS.RawBlocks
import PoissonDAG.Constructions.FORS.AcceptedRange
import PoissonDAG.Probability.SchemeExperiment

namespace PoissonDAG.FORS.Config

def blockDigit (p : Config) (raw : Nat) (i : Fin p.trees) :=
  raw / 2^(i.val*p.height) % 2^p.height

theorem digit_ext (p : Config) (x y : Fin p.messageCount)
    (h : ∀ i : Fin p.trees, p.blockDigit x i = p.blockDigit y i) : x = y := by
  have hm : p.messageCount = p.leaves^p.trees := by
    simp [messageCount, leaves, ← Nat.pow_mul, Nat.mul_comm]
  let xx : Fin (p.leaves^p.trees) := Fin.cast hm x
  let yy : Fin (p.leaves^p.trees) := Fin.cast hm y
  have he : xx = yy := by
    apply finFunctionFinEquiv.symm.injective
    funext i
    apply Fin.ext
    change x.val / p.leaves^i.val % p.leaves = y.val / p.leaves^i.val % p.leaves
    simpa only [leaves, ← Nat.pow_mul, Nat.mul_comm p.height i.val, blockDigit] using h i
  have hval : (xx : Nat) = (yy : Nat) := congrArg (fun z : Fin (p.leaves^p.trees) => z.val) he
  exact Fin.ext hval

theorem fixed_history_count (p : Config) (history : List Nat) :
    ((Finset.univ : Finset (Fin p.messageCount)).filter
      (fun x => p.scheme.covered history x.val = true)).card ≤ history.length^p.trees := by
  classical
  let hits := (Finset.univ : Finset (Fin p.messageCount)).filter
    (fun x => p.scheme.covered history x.val = true)
  have supply (x : hits) (i : Fin p.trees) :
      ∃ j : Fin history.length, p.blockDigit history[j] i = p.blockDigit x.val i := by
    have hc := (Finset.mem_filter.mp x.property).2
    obtain ⟨raw,hh,he⟩ := p.covered_requires_block x.val i history i.isLt hc
    obtain ⟨n,hn,hr⟩ := List.mem_iff_getElem.mp hh
    exact ⟨⟨n,hn⟩, by simpa [hr,blockDigit] using he⟩
  let supplier (x : hits) (i : Fin p.trees) : Fin history.length := (supply x i).choose
  have hinj : Function.Injective supplier := by
    intro x y hxy
    apply Subtype.ext
    apply p.digit_ext
    intro i
    have hs : supplier x i = supplier y i := congrFun hxy i
    have hx : p.blockDigit history[supplier x i] i = p.blockDigit x.val i :=
      (supply x i).choose_spec
    have hy : p.blockDigit history[supplier y i] i = p.blockDigit y.val i :=
      (supply y i).choose_spec
    have hblock := congrArg (fun j : Fin history.length => p.blockDigit history[j] i) hs
    exact hx.symm.trans (hblock.trans hy)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective supplier hinj

theorem fixed_history_sum (p : Config) (history : List Nat) :
    (∑ x : Fin p.messageCount, if p.scheme.covered history x then (1:ℚ) else 0)
      ≤ (history.length:ℚ)^p.trees := by
  rw [Finset.sum_boole]
  exact_mod_cast p.fixed_history_count history

end PoissonDAG.FORS.Config
