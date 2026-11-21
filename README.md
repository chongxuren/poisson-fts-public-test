# Poisson hash-DAG challenge · public test

Prove a universal lower bound on signature bytes or certify a shorter construction under the same Poisson(1) DAG-covering model. This public repository tests the Lean judge, automatic acceptance and leaderboard. **Practice only. Cash awards are $0.**

[Live leaderboard](https://chongxuren.github.io/poisson-fts-public-test/) · [Submission rules and examples](RULES.md) · [Proof checks](https://github.com/chongxuren/poisson-fts-public-test/actions/workflows/submit.yml)

| Research result | Status |
| --- | --- |
| 99 B universal lower bound | [Organizer's Lean theorem](formal/PoissonDAG/V2/Lower99.lean) |
| 756 B GRS-CC construction | Proposed. A complete construction certificate is still outstanding. |

Signing uses at most 2²⁴ expected hashes and verification at most 512. The model imposes a 2⁻¹²⁸ symbolic covering target on a fresh independent input. The practice lower-bound track starts at 97 B so participants can rehearse record changes using the published theorem.

Open a PR with one new entry. GitHub Actions checks the exact claim and proof, then commits accepted entries and the [score ledger](docs/scores.json) together. The sample records demonstrate the process. For local infrastructure checks, run `python3 -B -m unittest discover -s tests -v`. The full Lean and container tests run in the **Test the challenge** workflow.
