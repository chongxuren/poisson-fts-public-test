import PoissonDAG.Model

namespace PoissonDAG

-- These check executable semantics. They are not construction certificates.
example : (close [.source, .source, .binary 0 1]
    [true, true, false] [true, true, true]).1 = [true, true, true] := by decide

example : (close [.source, .source, .binary 0 1]
    [false, false, true] [true, true, true]).1 = [false, false, true] := by decide

example : (close [.source, .source, .binary 0 1]
    [false, false, false] [true, true, true]).2 = 0 := by decide

-- The only universal bound supplied here is deliberately unranked.
theorem zero_lower_bound : UniversalLowerBound 0 := by
  intro s _
  exact Nat.zero_le s.size

end PoissonDAG
