import PoissonDAG.Constructions.PORS.IncompleteSupport
import PoissonDAG.Constructions.PORS.BucketRefinedRow

namespace PoissonDAG.PORS.BucketRefined

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem accepted_word_count_replay :
    2^10+768 = p.t ∧ p.leftFilledWords 10 768 = p.acceptedWords := by
  decide +kernel

end PoissonDAG.PORS.BucketRefined
