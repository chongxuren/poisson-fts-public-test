import PoissonDAG.Constructions.PORS.IncompleteSupport
import PoissonDAG.Constructions.PORS.SingleRefinedRow

namespace PoissonDAG.PORS.SingleRefined

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem accepted_word_count_replay :
    2^18+229376 = p.t ∧ p.leftFilledWords 18 229376 = p.acceptedWords := by
  decide +kernel

end PoissonDAG.PORS.SingleRefined
