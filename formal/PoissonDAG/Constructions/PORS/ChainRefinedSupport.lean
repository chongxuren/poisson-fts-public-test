import PoissonDAG.Constructions.PORS.IncompleteSupport
import PoissonDAG.Constructions.PORS.ChainRefinedRow

namespace PoissonDAG.PORS.ChainRefined

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem accepted_word_count_replay :
    2^4+8 = p.t ∧ p.leftFilledWords 4 8 = p.acceptedWords := by
  decide +kernel

end PoissonDAG.PORS.ChainRefined
