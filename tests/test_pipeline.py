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

    @unittest.skipUnless(os.environ.get("JUDGE_IMAGE"), "requires the pinned Linux judge")
    def test_kernel(self):
        cases = [("base.lean", 99, "lower-bound", True),
                 ("weak.lean", 98, "lower-bound", True),
                 ("base.lean", 100, "lower-bound", False),
                 ("placeholder.lean", 100, "lower-bound", False),
                 ("wrong.lean", 756, "construction", False)]
        for proof, bound, track, valid in cases:
            with self.subTest(proof=proof, bound=bound), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp)
                prepare(*fixture(proof, bound, track), directory)
                if valid:
                    verify(directory, fixture_debug=True)
                else:
                    with self.assertRaisesRegex(ValueError, "kernel rejected"):
                        verify(directory, fixture_debug=True)
