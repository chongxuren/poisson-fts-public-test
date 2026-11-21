# FORS construction proofs

Each physical tree uses a private source, a unary hash commitment at each leaf, and a binary path to its root. A binary aggregation tree combines the roots. The counter variant accepts a digest when its last zero-bit field vanishes. The counter is part of the transmitted signature.

| Organizer reference | Trees × height | Zero bits | Counter bits | Bytes | Signing hashes, expected upper | Verification hashes, successful upper |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `fors-18-8-v1` | 8 × 18 | 0 | 0 | 2,432 | 6,291,457 | 161 |
| `fors-c-18-7-18-v1` | 7 × 18 | 18 | 25 | 2,132 | 6,029,311 | 141 |
| `fors-c-17-7-19-v1` | 7 × 17 | 19 | 26 | 2,020 | 3,801,087 | 134 |

For a fixed history and target, every selected private source must occur among the previous openings. With q prior signatures and k physical trees, at most qᵏ accepted targets can have suppliers in every tree. The proof counts those targets first, then averages over the single shared Poisson history count.

The [three Lean endpoints](Certificates.lean) prove the public V2 upper-bound claims. The [organizer library](../../formal/PoissonDAG/Constructions/FORS/Components.lean) builds their dependencies. The isolated submission checker compiles the final certificate and checks its exact scheme and byte bound.
