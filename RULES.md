# Public rehearsal rules

**The rehearsal pays $0.** Everyone can try the public checker. All ranks are practice ranks. A future prize challenge would require its own dates, rules and funded awards.

| Track | What Lean must prove | Better score | Practice opening |
| --- | --- | --- | --- |
| Lower bound | Every eligible scheme uses at least the claimed bytes | Larger | 97 B, deliberately below the known 99 B |
| Construction | The explicit submitted scheme is eligible and uses at most the claimed bytes | Smaller | Open until the first verified construction |

The formal contract is [V2/Model.lean](formal/PoissonDAG/V2/Model.lean), together with its [base model](formal/PoissonDAG/Model.lean). It measures maximum serialized signature bytes, expected signing and verification hashes, honest failure, and the chance that disclosures from one shared Poisson(1) history cover a fresh independent raw target. Each disclosure must contribute to the recomputed root. The covering target is a symbolic probability of at most 2⁻¹²⁸. Full adaptive ROM unforgeability would require another theorem. The independent input bits feed an explicit acyclic Boolean circuit.

## Prepare a submission

1. Fork the repository. Start a branch at the latest upstream `main`.
2. Add **one new directory** at `submissions/<track>/<id>/`, choosing either `construction` or `lower-bound`. A team may enter both tracks through separate PRs. Use lowercase letters, digits and hyphens for the ID and team name. Choose a fresh ID for each accepted entry.
3. Add the four common files below and, for a construction, `program.json`. Commit, push your branch and open a pull request to upstream `main`. No CLI account or wallet is required.

| File | Contents |
| --- | --- |
| `claim.json` | Claim, team and contract, as below |
| `proof/Main.lean` | The theorem named `Submission.certificate` |
| `ARGUMENT.md` | The mathematical argument in words |
| `PROVENANCE.md` | Contributors, source of the proof and prior work |

## Submit a lower bound

For example, the following two files reproduce the organizer's known theorem. Say so in the provenance.

```json
{"contract":"poisson-dag-v2-rehearsal-1","track":"lower-bound","id":"replay-99","team":"example-team","bound_bytes":99}
```

```lean
import PoissonDAG.V2.Lower99

theorem Submission.certificate : PoissonDAG.V2.UniversalLowerBound 99 :=
  PoissonDAG.V2.lower99
```

## Submit a construction

Supply an executable construction and a complete Lean proof for the same scheme. **Smaller maximum serialized signatures win.** The first eligible construction opens the track at its proven byte bound. Subsequent records must be strictly smaller. The 756 B GRS-CC and 5,760 B forest examples are unranked, so the first entry may exceed either figure.

1. Place the four common files and `program.json` in `submissions/construction/<id>/`. Set the track to `construction` and `bound_bytes` to your claimed upper bound, in whole bytes.
2. Bind the implementation to the claim using **one** of the two program formats below. For an original design, submit the actual DAG and Boolean encoder. The fixed organizer implementations listed below can be selected by name.
3. Prove `PoissonDAG.V2.ConstructionCertificate yourScheme N` in the unconditional theorem `Submission.certificate`. The judge constructs its own goal from the manifest and claimed byte count. Eligibility includes well-formedness, honest correctness, authenticated disclosures, honest failure ≤ 2⁻¹²⁸, expected signing ≤ 2²⁴ hashes, expected verification ≤ 512 hashes, and the shared-Poisson(1) covering target ≤ 2⁻¹²⁸. The size claim is a maximum.
4. Describe the construction, size and hash accounting in `ARGUMENT.md`. Credit the design and the proof authors in `PROVENANCE.md`. A runnable example, simulations or a theorem that assumes eligibility leaves the entry unranked.

**FORS references.** The three frozen configurations have [parameter sets and Lean proofs](examples/fors/). Use an exact manifest such as `{"representation":"organizer-reference-v1","scheme":"fors-c-17-7-19-v1"}`. The byte bound in your claim must follow from a proof for that exact scheme.

#### PORS family references

| Construction | Manifest scheme | Candidate bytes |
| --- | --- | ---: |
| PORS+FP | `pors-fp-1780-v1` | 1,780 |
| BPORS+FP | `bpors-fp-1492-v1` | 1,492 |
| BPORS-C+BFP | `bpors-c-bfp-1188-v1` | 1,188 |

Each manifest selects one [graph and encoder](formal/PoissonDAG/Constructions/PORS/Literal.lean). To complete its [conditional certificate](formal/PoissonDAG/Constructions/PORS/LiteralAssembly.lean), prove the row's `Refinement` for that circuit. The judge awards a score only for the unconditional theorem.

#### GRS-CC reference

**Fixed GRS-CC reference.** Copy the [756-byte manifest](examples/grs-cc/program.json) to `program.json`. It names exactly the organizer's graph and encoder at the checked base commit. This fits the upload limit even though the graph has 2,629,119 vertices. A change to any construction parameter describes a different scheme and must use the explicit format.

```json
{"contract":"poisson-dag-v2-rehearsal-1","track":"construction","id":"grs-proof","team":"example-team","bound_bytes":756}
```

The JSON above belongs in `claim.json`. The [GRS-CC Lean assembly](formal/PoissonDAG/Constructions/GRSCC/Certification.lean) reduces the remaining proof to local covering inequalities. Existing lemmas may be reused with attribution.

**Explicit graph and encoder.** A complete runnable example is the [5,760-byte Merkle forest](examples/merkle_forest/). Its [program.json](examples/merkle_forest/program.json) is generated from the same implementation used in the sign/verify demonstration.

A program has the following format. This tiny example illustrates syntax only.

```json
{"representation":"explicit-dag-circuit-v1","graph":[["source"],["unary",0]],"encoder":{"inputs":1,"gates":[["input",0],["constant",true],["constant",false]],"outputs":[1,1,2,2,1]},"counter_bits":1}
```

Graph nodes are `source`, `unary i`, or `binary i j`. Gates are `input i`, `constant true/false`, `neg i`, `conj i j`, or `xor i j`. Indices are zero-based. Parents refer to earlier nodes or gates. Outputs index the acceptance bit, the disclosure mask and the evaluation mask, in that order.

## How the judge accepts and ranks entries

- GitHub records a new check when a PR opens, is reopened, or receives a new head commit. For this test, the numeric GitHub Actions run ID determines priority. A retry of that run keeps its priority. The ledger replays accepted runs in that order, independent of when each proof finishes. Git author dates have no role.
- The read-only job reads the exact Git snapshot as data. It compiles entrant Lean inside an isolated container. A fresh container replays only the exported proof against the organizer's goal. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. Every submission needs a complete proof.
- A successful check triggers a separate job that commits the exact entry and updated scores together. It checks the PR head again. If the checker changed since submission, rebase and push again. Failed checks leave the ledger untouched.
- A verified claim earns a place only when it strictly improves the standing record at its intake priority. The gain is the difference in bytes, in the track's direction. The first verified construction establishes a record without a numerical gain. Identical scores give priority to the first record. Each team holds one place per track, ranked by its best qualifying byte score. Tracks are scored separately.
- The baseline is public and may be reproduced. A check that ties an earlier entry still earns a receipt. Reusing a result requires attribution. The two Markdown files are required; the judge checks their presence. It does not adjudicate originality or team identity.
- Entry limits are 64 regular files, 4 MiB per file and 16 MiB total. Proof files may import helper modules under `proof/`. Use only the pinned dependencies. The job uses a standard GitHub-hosted Ubuntu runner, with a 25-minute verification timeout, two container CPUs, 4 GiB of container RAM and a 32 MiB proof-export cap. The isolated containers have no network. Check the failed step on the PR's Actions run before retrying.
