# Public rehearsal rules

**The rehearsal pays $0.** Everyone can try the public checker. All ranks are practice ranks. A future prize challenge would require its own dates, rules and funded awards.

| Track | What Lean must prove | Better score | Practice opening |
| --- | --- | --- | --- |
| Lower bound | Every eligible scheme uses at least the claimed bytes | Larger | 97 B, deliberately below the known 99 B |
| Construction | The explicit submitted scheme is eligible and uses at most the claimed bytes | Smaller | Open until the first verified construction |

The formal contract is [V2/Model.lean](formal/PoissonDAG/V2/Model.lean), together with its [base model](formal/PoissonDAG/Model.lean). It measures maximum serialized signature bytes, expected signing and verification hashes, honest failure, and the chance that disclosures from one shared Poisson(1) history cover a fresh independent raw target. Each disclosure must contribute to the recomputed root. The covering target is a symbolic probability of at most 2⁻¹²⁸. Full adaptive ROM unforgeability would require another theorem. The independent input bits feed an explicit acyclic Boolean circuit.

## Submit a lower bound

1. Fork the repository. Start a branch at the latest upstream `main`.
2. Add **one new directory** at `submissions/lower-bound/<id>/`. Use lowercase letters, digits and hyphens for the ID and team name. Choose a fresh ID for each accepted entry.
3. Add the four files below, commit, push your branch and open a pull request to upstream `main`. No CLI account or wallet is required.

| File | Contents |
| --- | --- |
| `claim.json` | Claim, team and contract, as below |
| `proof/Main.lean` | The theorem named `Submission.certificate` |
| `ARGUMENT.md` | The mathematical argument in words |
| `PROVENANCE.md` | Contributors, source of the proof and prior work |

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

Use `submissions/construction/<id>/`, set the track to `construction`, and add `program.json`. Define the same scheme in your proof and prove `PoissonDAG.V2.ConstructionCertificate yourScheme N`. The judge independently translates the JSON and checks definitional equality against its own theorem target. The proposed 756 B GRS-CC scheme still needs this certificate.

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
