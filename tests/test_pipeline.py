import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from ci.verify import verify
from judge.entry import prepare

import json


def fixture(proof, bound, track="lower-bound"):
    claim = {"contract": "poisson-dag-v2-rehearsal-1", "id": "fixture",
             "team": "organizer", "track": track, "bound_bytes": bound}
    files = {"claim.json": json.dumps(claim).encode(),
             "proof/Main.lean": (ROOT / "tests" / proof).read_bytes(),
             "ARGUMENT.md": b"Rehearsal fixture.", "PROVENANCE.md": b"Organizer."}
    if track == "construction":
        files["program.json"] = json.dumps({
            "representation": "explicit-dag-circuit-v1", "graph": [["source"]],
            "encoder": {"inputs": 1, "gates": [["constant", True]], "outputs": [0, 0, 0]},
            "counter_bits": 1}).encode()
    return files, f"submissions/{track}/fixture"


class JudgeTests(unittest.TestCase):
    def test_both_claim_types(self):
        for track in ("lower-bound", "construction"):
            with self.subTest(track=track), tempfile.TemporaryDirectory() as tmp:
                prepare(*fixture("wrong.lean", 99, track), Path(tmp))
                self.assertIn("Judge.goal", (Path(tmp) / "Expected.lean").read_text())

    def test_fors_manifests_bind_distinct_circuits(self):
        refs = {"fors-18-8-v1": "18, 8, 0, 0", "fors-c-18-7-18-v1": "18, 7, 18, 25",
                "fors-c-17-7-19-v1": "17, 7, 19, 26"}
        for ref, fields in refs.items():
            with self.subTest(ref=ref), tempfile.TemporaryDirectory() as tmp:
                files, path = fixture("wrong.lean", 2020, "construction")
                program = {"representation": "organizer-reference-v1", "scheme": ref}
                files["program.json"] = json.dumps(program).encode()
                self.assertEqual(prepare(files, path, Path(tmp))["reference"], ref)
                self.assertIn("Config.scheme ⟨" + fields + "⟩", (Path(tmp) / "Expected.lean").read_text())
        with tempfile.TemporaryDirectory() as tmp:
            files, path = fixture("wrong.lean", 2020, "construction")
            files["program.json"] = b'{"representation":"organizer-reference-v1","scheme":"fors-unknown"}'
            with self.assertRaisesRegex(ValueError, "unknown organizer reference"):
                prepare(files, path, Path(tmp))

    @unittest.skipUnless(os.environ.get("JUDGE_IMAGE"), "requires the pinned Linux judge")
    def test_kernel(self):
        cases = [("base.lean", 99, "lower-bound", True),
                 ("weak.lean", 98, "lower-bound", True),
                 ("base.lean", 100, "lower-bound", False),
                 ("placeholder.lean", 100, "lower-bound", False),
                 ("wrong.lean", 756, "construction", False),
                 ("conditional.lean", 17, "construction", False)]
        for proof, bound, track, valid in cases:
            with self.subTest(proof=proof, bound=bound), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp)
                prepare(*fixture(proof, bound, track), directory)
                if valid:
                    verify(directory, fixture_debug=True)
                else:
                    with self.assertRaisesRegex(ValueError, "kernel rejected"):
                        verify(directory, fixture_debug=True)

    @unittest.skipUnless(os.environ.get("JUDGE_IMAGE"), "requires the pinned Linux judge")
    def test_construction_literal_binding(self):
        # Exercise exact matching without putting an invented eligible scheme on the board.
        for changed_program in (False, True):
            with self.subTest(changed_program=changed_program), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp)
                files, path = fixture("conditional.lean", 17, "construction")
                if changed_program:
                    program = json.loads(files["program.json"])
                    program["counter_bits"] = 2
                    files["program.json"] = json.dumps(program).encode()
                prepare(files, path, directory)
                expected = directory / "Expected.lean"
                target = expected.read_text().replace(
                    "def Judge.goal : Prop := ", "def Judge.goal : Prop := PoissonDAG.V2.Eligible Judge.literal → ")
                expected.write_text(target)
                if changed_program:
                    with self.assertRaisesRegex(ValueError, "kernel rejected"):
                        verify(directory, fixture_debug=True)
                else:
                    verify(directory, fixture_debug=True)

    def test_reference_manifest(self):
        files, path = fixture("grs_reference.lean", 756, "construction")
        files["program.json"] = (ROOT / "examples/grs-cc/program.json").read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            claim = prepare(files, path, Path(tmp))
            text = (Path(tmp) / "Expected.lean").read_text()
            self.assertEqual(claim["reference"], "grs-cc-v1")
            self.assertIn(":= PoissonDAG.GRSCC.scheme", text)
            self.assertIn("ConstructionCertificate Judge.literal 756", text)
        files["program.json"] = files["program.json"].replace(b"grs-cc-v1", b"other")
        with tempfile.TemporaryDirectory() as tmp, self.assertRaises(ValueError):
            prepare(files, path, Path(tmp))

    def test_pors_references_bind_exact_schemes(self):
        rows = [("pors-fp-1780-v1", "single", 1780),
                ("bpors-fp-1492-v1", "bucket", 1492),
                ("bpors-c-bfp-1188-v1", "chainBuckets", 1188)]
        for reference, scheme, size in rows:
            with self.subTest(reference=reference), tempfile.TemporaryDirectory() as tmp:
                files, path = fixture("conditional.lean", size, "construction")
                files["program.json"] = json.dumps({
                    "representation": "organizer-reference-v1", "scheme": reference}).encode()
                self.assertEqual(prepare(files, path, Path(tmp))["reference"], reference)
                expected = (Path(tmp) / "Expected.lean").read_text()
                self.assertIn(":= PoissonDAG.PORS.Literal." + scheme + "\n", expected)
                self.assertIn(f":= PoissonDAG.V2.ConstructionCertificate Judge.literal {size}\n", expected)

    @unittest.skipUnless(os.environ.get("JUDGE_IMAGE"), "requires the pinned Linux judge")
    def test_reference_proof(self):
        files, path = fixture("grs_reference.lean", 756, "construction")
        files["program.json"] = (ROOT / "examples/grs-cc/program.json").read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            prepare(files, path, directory)
            with self.assertRaisesRegex(ValueError, "kernel rejected"):
                verify(directory, fixture_debug=True)
            expected = directory / "Expected.lean"
            expected.write_text(expected.read_text().replace(
                ": Prop := ", ": Prop := PoissonDAG.V2.Eligible Judge.literal → "))
            verify(directory, fixture_debug=True)

    @unittest.skipUnless(os.environ.get("JUDGE_IMAGE"), "requires the pinned Linux judge")
    def test_grs_actual_size_and_hash_budgets(self):
        files, path = fixture("grs_budgets.lean", 756, "construction")
        files["program.json"] = (ROOT / "examples/grs-cc/program.json").read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            prepare(files, path, directory)
            expected = directory / "Expected.lean"
            definitions, full_goal = expected.read_text().split("def Judge.goal : Prop := ")
            self.assertEqual(full_goal.strip(),
                             "PoissonDAG.V2.ConstructionCertificate Judge.literal 756")
            # A component check has a separate test-only goal and cannot promote a score.
            expected.write_text(definitions + """def Judge.goal : Prop :=
  Judge.literal.WellFormed ∧ Judge.literal.Correct ∧ Judge.literal.size ≤ 756 ∧
  Judge.literal.signCost ≤ 2^24 ∧ Judge.literal.verifyCost ≤ 512 ∧
  Judge.literal.failure ≤ (1 : Rat) / 2^128
""")
            verify(directory, fixture_debug=True)

    @unittest.skipUnless(os.environ.get("JUDGE_IMAGE"), "requires the pinned Linux judge")
    def test_full_forest_manifest_compiles(self):
        # Exercise the real full-size input. The test-only goal checks a projection;
        # a ranked submission still has to establish every eligibility condition.
        files, path = fixture("wrong.lean", 5760, "construction")
        files["program.json"] = (ROOT / "examples/merkle_forest/program.json").read_bytes()
        files["proof/Main.lean"] = b"theorem Submission.certificate : (0 : Nat) = 0 := rfl\n"
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            prepare(files, path, directory)
            expected = directory / "Expected.lean"
            model, definition = expected.read_text().split("def Judge.goal : Prop := ")
            self.assertEqual(definition.strip(), "PoissonDAG.V2.ConstructionCertificate Judge.literal 5760")
            expected.write_text(model + "def Judge.goal : Prop := Judge.literal.counterBits = 0\n")
            verify(directory, fixture_debug=True)
