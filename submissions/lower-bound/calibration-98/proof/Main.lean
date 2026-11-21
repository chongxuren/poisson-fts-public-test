import PoissonDAG.V2.Lower99
theorem Submission.certificate : PoissonDAG.V2.UniversalLowerBound 98 :=
  fun s h => Nat.le_trans (by decide : 98 ≤ 99) (PoissonDAG.V2.lower99 s h)
