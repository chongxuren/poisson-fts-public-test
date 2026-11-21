import json
import unittest
from fractions import Fraction
from pathlib import Path

from examples.merkle_forest import reference as forest
from judge.entry import MAX_FILE, scheme_literal


class ForestTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = forest.build_program()

    def test_published_program(self):
        path = Path(__file__).resolve().parents[1] / "examples/merkle_forest/program.json"
        self.assertLessEqual(path.stat().st_size, MAX_FILE)
        self.assertEqual(json.loads(path.read_bytes()), self.program)
        self.assertTrue(scheme_literal(self.program))
        self.assertEqual(len(self.program["graph"]), 20479)
        self.assertLessEqual(forest.covering_envelope(), Fraction(1, 2**128))

    def test_masks_follow_the_merkle_paths(self):
        # Independent path computation, including every possible byte in at least one tree.
        for run in range(7):
            indices = [(40*run+t) % 256 for t in range(40)]
            raw = int.from_bytes(bytes(indices), "little")
            supplied, plan = forest.masks(self.program, raw)
            expected = set()
            hashes = set(range(40*511, 20479))
            for t, leaf in enumerate(indices):
                start = t * 511
                expected.add(start + leaf)
                for h in range(8):
                    width = 256 >> h
                    expected.add(start + ((leaf >> h) ^ 1))
                    start += width
                    hashes.add(start + (leaf >> (h+1)))
            self.assertEqual({i for i, b in enumerate(supplied) if b}, expected)
            self.assertEqual({i for i, b in enumerate(plan) if b}, hashes)

    def test_sign_verify_and_counts(self):
        seed, message = bytes(range(32)), b"Poisson DAG rehearsal"
        root = forest.public_key(self.program, seed)
        signing, checking = forest.CountedHash(), forest.CountedHash()
        signature = forest.sign(self.program, seed, message, signing)
        self.assertEqual((len(signature), signing.calls), (5760, 20482))
        self.assertTrue(forest.verify(self.program, root, message, signature, checking))
        self.assertEqual(checking.calls, 362)
        for changed, payload in [(message, signature[:-1]), (b"other", signature),
                                 (message, bytes([signature[0] ^ 1]) + signature[1:])]:
            self.assertFalse(forest.verify(self.program, root, changed, payload, forest.CountedHash()))
