import PoissonDAG.Core.CircuitFacts
import Std.Sat.AIG.Lemmas

/-! # AIG compilation into the protected Boolean circuit

Each AIG declaration produces a positive gate and its negation. The translation
is linear in the AIG size and preserves shared subexpressions. Atom addresses
are bounded by construction. No truth table over the raw input space is used.
-/

namespace PoissonDAG.AIGCompiler

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α]

def address (gate : Nat) (invert : Bool) : Nat := 2 * gate + invert.toNat

theorem address_lt {gate limit : Nat} (h : gate < limit) (invert : Bool) :
    address gate invert < 2 * limit := by
  cases invert <;> simp [address] <;> omega

def positiveGate {width : Nat} (atom : α → Option (Fin width)) : AIG.Decl α → Gate
  | .false => .constant false
  | .atom a => match atom a with
    | none => .constant false
    | some i => .input i.val
  | .gate l r => .conj (address l.gate l.invert) (address r.gate r.invert)

def gateAt {width : Nat} (aig : AIG α) (atom : α → Option (Fin width))
    (index : Nat) : Gate :=
  if index % 2 = 0 then
    positiveGate atom (aig.decls[index / 2]?.getD .false)
  else .neg (index - 1)

def compile {width : Nat} (aig : AIG α) (atom : α → Option (Fin width))
    (outputs : List (AIG.Ref aig)) : Circuit where
  inputs := width
  gates := (List.range (2 * aig.decls.size)).map (gateAt aig atom)
  outputs := outputs.map (fun ref => address ref.gate ref.invert)

def assignment {width : Nat} (atom : α → Option (Fin width)) (raw : Nat)
    (a : α) : Bool :=
  match atom a with
  | none => false
  | some i => raw.testBit i.val

def value {width : Nat} (aig : AIG α) (atom : α → Option (Fin width))
    (raw index : Nat) : Bool :=
  if h : index / 2 < aig.decls.size then
    AIG.denote (assignment atom raw)
      ⟨aig, ⟨index / 2, decide (index % 2 = 1), h⟩⟩
  else false

theorem value_address {width : Nat} (aig : AIG α)
    (atom : α → Option (Fin width)) (raw : Nat) (ref : AIG.Ref aig) :
    value aig atom raw (address ref.gate ref.invert) =
      AIG.denote (assignment atom raw) ⟨aig, ref⟩ := by
  rcases ref with ⟨gate, invert, hgate⟩
  cases invert <;>
    simp [address, value, hgate, Nat.add_div, Nat.add_mod, AIG.denote]

def ValidGate (width index : Nat) : Gate → Prop
  | .input j => j < width
  | .constant _ => True
  | .neg p => p < index
  | .conj l r | .xor l r => l < index ∧ r < index

theorem gateAt_valid {width : Nat} (aig : AIG α)
    (atom : α → Option (Fin width)) (i : Nat) (hi : i < 2 * aig.decls.size) :
    ValidGate width i (gateAt aig atom i) := by
  by_cases heven : i % 2 = 0
  · have hquot : i / 2 < aig.decls.size := by omega
    simp only [gateAt, if_pos heven, Array.getElem?_eq_getElem hquot,
      Option.getD_some]
    cases hd : aig.decls[i / 2] with
    | false => trivial
    | atom a =>
        cases ha : atom a with
        | none => simp [positiveGate, ha, ValidGate]
        | some idx => simpa only [positiveGate, ha, ValidGate] using idx.isLt
    | gate l r =>
        have hdg := aig.hdag hquot hd
        have hl := address_lt hdg.1 l.invert
        have hr := address_lt hdg.2 r.invert
        change address l.gate l.invert < i ∧ address r.gate r.invert < i
        omega
  · simp only [gateAt, if_neg heven, ValidGate]
    omega

theorem compile_valid {width : Nat} (aig : AIG α)
    (atom : α → Option (Fin width)) (outputs : List (AIG.Ref aig)) :
    (compile aig atom outputs).Valid := by
  constructor
  · intro i g hg
    obtain ⟨hi, hg⟩ := List.getElem?_eq_some_iff.mp hg
    have hib : i < 2 * aig.decls.size := by simpa [compile] using hi
    have heq : g = gateAt aig atom i := by
      simpa [compile] using hg.symm
    change ValidGate width i g
    rw [heq]
    exact gateAt_valid aig atom i hib
  · intro o ho
    obtain ⟨ref, _, rfl⟩ := List.mem_map.mp ho
    simpa [compile] using address_lt ref.hgate ref.invert

theorem gateAt_equation {width : Nat} (aig : AIG α)
    (atom : α → Option (Fin width)) (raw i : Nat) (hi : i < 2 * aig.decls.size) :
    evalGate raw ((List.range i).map (value aig atom raw)) (gateAt aig atom i) =
      value aig atom raw i := by
  have hquot : i / 2 < aig.decls.size := by omega
  by_cases heven : i % 2 = 0
  · have hi0 : decide (i % 2 = 1) = false := by simp [heven]
    simp only [gateAt, if_pos heven, Array.getElem?_eq_getElem hquot,
      Option.getD_some, value, dif_pos hquot, hi0]
    cases hd : aig.decls[i / 2] with
    | false =>
        rw [AIG.denote_idx_false hd]
        rfl
    | atom a =>
        rw [AIG.denote_idx_atom hd]
        simp only [positiveGate, assignment, Bool.xor_false]
        cases atom a <;> rfl
    | gate l r =>
        have hdag := aig.hdag hquot hd
        have hl : address l.gate l.invert < i := by
          have h := address_lt hdag.1 l.invert
          omega
        have hr : address r.gate r.invert < i := by
          have h := address_lt hdag.2 r.invert
          omega
        simp only [positiveGate, evalGate, get_map_range _ hl, get_map_range _ hr]
        rw [value_address aig atom raw ⟨l.gate, l.invert, by omega⟩,
          value_address aig atom raw ⟨r.gate, r.invert, by omega⟩,
          AIG.denote_idx_gate hd, Bool.xor_false]
  · have hmod : i % 2 = 1 := by omega
    have hip : i - 1 < i := by omega
    have hprev : (i - 1) / 2 = i / 2 := by omega
    have hprevmod : (i - 1) % 2 = 0 := by omega
    simp only [gateAt, if_neg heven, evalGate, get_map_range _ hip]
    simp only [value, hprev, dif_pos hquot, hprevmod, hmod,
      Nat.zero_ne_one, decide_false, decide_true]
    simp [AIG.denote]

theorem compile_eval {width : Nat} (aig : AIG α)
    (atom : α → Option (Fin width)) (outputs : List (AIG.Ref aig)) (raw : Nat) :
    (compile aig atom outputs).eval raw =
      outputs.map (fun ref => AIG.denote (assignment atom raw) ⟨aig, ref⟩) := by
  have heq : ∀ i (hi : i < (compile aig atom outputs).gates.length),
      evalGate raw ((List.range i).map (value aig atom raw))
        (compile aig atom outputs).gates[i] = value aig atom raw i := by
    intro i hi
    have hib : i < 2 * aig.decls.size := by simpa [compile] using hi
    simpa [compile] using gateAt_equation aig atom raw i hib
  rw [Circuit.eval_of_equations _ raw (value aig atom raw) heq
    (compile_valid aig atom outputs).2]
  simp only [compile, List.map_map]
  apply List.map_congr_left
  intro ref href
  exact value_address aig atom raw ref

end PoissonDAG.AIGCompiler
