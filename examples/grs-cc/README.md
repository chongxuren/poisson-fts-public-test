# GRS-CC · 756-byte construction candidate

This directory contains the compact [program manifest](program.json) for the organizer's fixed [Lean scheme](../../formal/PoissonDAG/Constructions/GRSCC/Circuit.lean). Entrants can finish its certificate or submit a different explicit construction.

## What is transmitted?

A route picks one of 16 buckets, one of two starting owners, and one slot in each of seven layers. Each layer contributes one guard label and five authentication labels from a height-five binary tree. A six-coordinate codeword with entries in 0…8 and sum 16 selects their hash-chain depths. The 42 layer labels and five outer authentication labels cost at most 47 × 16 bytes. A 32-bit counter adds four bytes, giving **756 bytes**.

The addressed graph has 2,629,119 vertices. Each counter trial uses two hash calls for a 170-bit input. An accepted input decodes into a route. Expected signing uses fewer than 11,676,797 hashes. Honest verification uses at most 441 hashes on an accepted input. See the [graph](../../formal/PoissonDAG/Constructions/GRSCC/Graph.lean), [encoder](../../formal/PoissonDAG/Constructions/GRSCC/RankEncoding.lean), and [size, cost and correctness lemmas](../../formal/PoissonDAG/Constructions/GRSCC/Circuit.lean).

## What would earn the upper bound?

The [Lean assembly lemma](../../formal/PoissonDAG/Constructions/GRSCC/Reference.lean) reduces certification to two obligations for this exact scheme.

1. Show that pooling disclosures from one shared Poisson(1) history covers an independent raw target with probability at most 2⁻¹²⁸ in the model.
2. For every accepted raw input, show that every transmitted label contributes to the verifier's recomputed root under its executed plan.

With proofs of both, submit the unchanged manifest and an **unconditional** theorem named `Submission.certificate`. The research work on the covering recurrence and scalar envelope has not yielded a complete accepted certificate. [Construction submission rules](../../RULES.md#submit-a-construction)

To build the public components locally with the pinned Lean toolchain:

```sh
lake build PoissonDAG.Constructions.GRSCC.Reference
```
