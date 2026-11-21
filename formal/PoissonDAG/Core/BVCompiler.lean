import PoissonDAG.Core.AIGCompiler
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit

/-! # Compiling many bitvector formulas with one shared AIG

The cache and DAG are threaded through all outputs. Each previously compiled
reference keeps its meaning by the verified prefix-extension property.
-/

namespace PoissonDAG.BVCompiler

open Std.Sat Std.Sat.AIG Std.Tactic.BVDecide

theorem prefix_trans {a b c : Array (AIG.Decl BVBit)}
    (hab : AIG.IsPrefix a b) (hbc : AIG.IsPrefix b c) : AIG.IsPrefix a c := by
  refine { size_le := Nat.le_trans hab.size_le hbc.size_le, idx_eq := ?_ }
  intro i hi
  rw [hbc.idx_eq i (Nat.lt_of_lt_of_le hi hab.size_le), hab.idx_eq i hi]

structure Batch (start : AIG BVBit) where
  aig : AIG BVBit
  refs : List (AIG.Ref aig)
  cache : BVExpr.Cache aig
  hpref : AIG.IsPrefix start.decls aig.decls

def compileList (aig : AIG BVBit) (cache : BVExpr.Cache aig) :
    List BVLogicalExpr → Batch aig
  | [] => ⟨aig, [], cache, .rfl⟩
  | expr :: exprs =>
    let first := BVLogicalExpr.bitblast.go aig expr cache
    let rest := compileList first.result.val.aig first.cache exprs
    { aig := rest.aig
      refs := first.result.val.ref.cast rest.hpref.size_le :: rest.refs
      cache := rest.cache
      hpref := prefix_trans (BVLogicalExpr.bitblast.go_isPrefix_aig cache) rest.hpref }

theorem compileList_length (aig : AIG BVBit) (cache : BVExpr.Cache aig)
    (exprs : List BVLogicalExpr) : (compileList aig cache exprs).refs.length = exprs.length := by
  induction exprs generalizing aig with
  | nil => rfl
  | cons expr exprs ih =>
      simp only [compileList, List.length_cons]
      rw [ih]

theorem compileList_eval (aig : AIG BVBit) (cache : BVExpr.Cache aig)
    (exprs : List BVLogicalExpr) (assign : BVExpr.Assignment)
    (hinv : BVExpr.Cache.Inv assign aig cache) :
    (compileList aig cache exprs).refs.map
        (fun ref => AIG.denote assign.toAIGAssignment ⟨(compileList aig cache exprs).aig, ref⟩) =
      exprs.map (BVLogicalExpr.eval assign) := by
  induction exprs generalizing aig with
  | nil => rfl
  | cons expr exprs ih =>
      let first := BVLogicalExpr.bitblast.go aig expr cache
      let rest := compileList first.result.val.aig first.cache exprs
      change (AIG.denote assign.toAIGAssignment
          ⟨rest.aig, first.result.val.ref.cast rest.hpref.size_le⟩ ::
        rest.refs.map (fun ref => AIG.denote assign.toAIGAssignment ⟨rest.aig, ref⟩)) =
          BVLogicalExpr.eval assign expr :: exprs.map (BVLogicalExpr.eval assign)
      congr 1
      · calc
          AIG.denote assign.toAIGAssignment
              ⟨rest.aig, first.result.val.ref.cast rest.hpref.size_le⟩ =
              AIG.denote assign.toAIGAssignment first.result.val := by
            simpa only [AIG.Ref.cast] using
              (AIG.denote.eq_of_isPrefix (assign := assign.toAIGAssignment)
                first.result.val rest.aig rest.hpref)
          _ = BVLogicalExpr.eval assign expr :=
            BVLogicalExpr.bitblast.go_eval_eq_eval expr aig assign cache hinv
      · exact ih _ _ (BVLogicalExpr.bitblast.go_Inv_of_Inv expr aig assign cache hinv)

def bitblast (exprs : List BVLogicalExpr) : Batch AIG.empty :=
  compileList AIG.empty .empty exprs

theorem bitblast_eval (exprs : List BVLogicalExpr) (assign : BVExpr.Assignment) :
    (bitblast exprs).refs.map
        (fun ref => AIG.denote assign.toAIGAssignment ⟨(bitblast exprs).aig, ref⟩) =
      exprs.map (BVLogicalExpr.eval assign) :=
  compileList_eval _ _ _ _ (BVExpr.Cache.Inv_empty _)

theorem bitblast_length (exprs : List BVLogicalExpr) :
    (bitblast exprs).refs.length = exprs.length := compileList_length _ _ _

/-- A single raw bitvector can supply every variable leaf. The construction's
formulas use variable zero; this total assignment also defines unused leaves. -/
def rawAssignment (width raw : Nat) : BVExpr.Assignment :=
  .leaf { w := width, bv := BitVec.ofNat width raw }

def rawAtom (width : Nat) (bit : BVBit) : Option (Fin width) :=
  if h : bit.idx.val < width then some ⟨bit.idx.val, h⟩ else none

theorem assignment_eq (width raw : Nat) :
    AIGCompiler.assignment (rawAtom width) raw = (rawAssignment width raw).toAIGAssignment := by
  funext bit
  change AIGCompiler.assignment (rawAtom width) raw bit =
    (BitVec.ofNat width raw).getLsbD bit.idx.val
  rw [BitVec.getLsbD_ofNat]
  by_cases h : bit.idx.val < width <;> simp [AIGCompiler.assignment, rawAtom, h]

def toCircuit (width : Nat) (exprs : List BVLogicalExpr) : Circuit :=
  let batch := bitblast exprs
  AIGCompiler.compile batch.aig (rawAtom width) batch.refs

theorem toCircuit_valid (width : Nat) (exprs : List BVLogicalExpr) :
    (toCircuit width exprs).Valid := AIGCompiler.compile_valid _ _ _

@[simp] theorem toCircuit_inputs (width : Nat) (exprs : List BVLogicalExpr) :
    (toCircuit width exprs).inputs = width := rfl

@[simp] theorem toCircuit_outputs_length (width : Nat) (exprs : List BVLogicalExpr) :
    (toCircuit width exprs).outputs.length = exprs.length := by
  simp [toCircuit, AIGCompiler.compile, bitblast_length]

theorem toCircuit_eval (width : Nat) (exprs : List BVLogicalExpr) (raw : Nat) :
    (toCircuit width exprs).eval raw =
      exprs.map (BVLogicalExpr.eval (rawAssignment width raw)) := by
  unfold toCircuit
  rw [AIGCompiler.compile_eval, assignment_eq]
  exact bitblast_eval _ _

end PoissonDAG.BVCompiler
