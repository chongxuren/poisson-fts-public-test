# PORS+FP at 1,780 bytes

One tree has 491,520 leaves. The encoder opens nine leaves and accepts at most 102 sibling labels. The proposed maximum is 4 counter bytes plus 16 × (9 + 102) = 1,780 bytes. [Frozen row](../../../formal/PoissonDAG/Constructions/PORS/SingleRefinedRow.lean) · [Graph and encoder](../../../formal/PoissonDAG/Constructions/PORS/Literal.lean)

The row uses 152 raw bits and a 30-bit counter. Its counting argument gives at most 16,133,231 expected signing hashes and 121 hashes per successful verification. Lean verifies the row arithmetic, the pruned support count and the finite Poisson sum including a bound on the tail. [Arithmetic](../../../formal/PoissonDAG/Constructions/PORS/SingleRefinedChecks.lean) · [Support count](../../../formal/PoissonDAG/Constructions/PORS/SingleRefinedSupport.lean)

The open premise is `Literal.Refinement`. It requires that the production gates select precisely the counted words, emit the claimed number of labels and hash operations, and produce the routed opening for each accepted input. For every history length, coverage by the pooled disclosures must satisfy the counting bound. The submitted Lean theorem derives the full challenge goal assuming those properties. [Exact premise and theorem](../../../formal/PoissonDAG/Constructions/PORS/LiteralAssembly.lean)
