# Merkle forest · 5,760-byte feasibility construction

The [Python reference](reference.py) signs and verifies messages. The [program.json](program.json) file is the same forest and Boolean encoder in the judge's explicit format. This example has a written covering argument and an exact arithmetic check. A full Lean certificate for the literal program is still open.

## Reproduce it

From the repository root, run:

```sh
python3 -B examples/merkle_forest/reference.py
mkdir -p build
python3 -B examples/merkle_forest/reference.py --emit-program > build/forest.json
cmp build/forest.json examples/merkle_forest/program.json
```

The demonstration signs a fixed message, verifies against its public key and reports the actual hash-call counts. It uses domain-separated, addressed SHA-256 truncated to 16 bytes for the example. The argument below concerns the challenge's symbolic covering experiment with independent uniform digest bits.

## Graph, encoder and costs

Build forty disjoint binary trees with 256 leaves each and combine their roots with 39 binary joins. The combined 16-byte root is the public key. Three digest blocks supply forty independent byte indices, one per tree. Every input is accepted. There is no counter.

For each index, disclose the selected leaf and its eight siblings along the path. Both bottom leaves are transmitted. Seven more labels come from internal levels. Every disclosed label feeds a hash along the path to the public root. The implementation serializes the 360 selected labels in increasing graph-index order.

| Quantity | Calculation | Result |
| --- | --- | ---: |
| Signature bytes | 40 × 9 × 16 | 5,760 |
| Signing hashes | 40 × 511 + 39 + 3 | 20,482 |
| Verification hashes | 40 × 8 + 39 + 3 | 362 |
| Honest failure probability | All raw inputs are accepted | 0 |

## Why the Poisson covering bound holds

Fix the shared number of uses at *q* and condition on the complete history. In each tree, a signature exposes two private leaves. Forward hashes produce internal nodes, so the pool can know at most min(256, 2*q*) leaves per tree. Covering a fresh target requires its selected leaf in all forty trees. Conditional on the history its forty indices are still independent, giving a coverage probability at most min(1, *q*/128)⁴⁰. The trees share the same *q*.

For *q* ≤ 64, bound its Poisson mass by 1/*q*! and conditional coverage by *q*⁴⁰/2²⁸⁰. For *q* ≥ 65, use coverage at most one and bound the factorial tail by a geometric series with ratio 1/66. The resulting rational bound is

```text
sum(q^40 / (q! * 2^280), q=0..64) + 66 / (65 * 65!) ≤ 2^-128.
```

The reference checks this inequality exactly. The public [Lean arithmetic theorem](../../formal/PoissonDAG/Arithmetic.lean) checks the same inequality. To earn a ranking, connect the actual circuit, graph closure, authenticated paths and Poisson cuts to the [V2 construction certificate](../../formal/PoissonDAG/V2/Model.lean). [Submission rules](../../RULES.md#submit-a-construction)
