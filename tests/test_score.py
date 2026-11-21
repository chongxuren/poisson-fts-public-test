import unittest
from judge.score import standings


def entry(track, run, team, bound):
    return {"track": track, "run": run, "team": team, "bound_bytes": bound}


class ScoringTests(unittest.TestCase):
    def test_priority_and_minimum_maximum(self):
        results = standings([entry("lower-bound", 30, "a", 99), entry("construction", 35, "c", 720),
                             entry("lower-bound", 10, "b", 98), entry("construction", 25, "d", 750),
                             entry("lower-bound", 50, "c", 99), entry("lower-bound", 20, "b", 98)])
        self.assertEqual(results["best"], {"construction": 720, "lower-bound": 99})
        self.assertEqual([row["delta"] for row in results["history"]], [1, 0, None, 1, 30, 0])
        self.assertEqual([row["team"] for row in results["rankings"]["lower-bound"]], ["a", "b"])
        self.assertEqual([row["team"] for row in results["rankings"]["construction"]], ["c", "d"])

    def test_one_place_per_team(self):
        results = standings([entry("lower-bound", 10, "a", 98), entry("lower-bound", 20, "a", 99)])
        self.assertEqual(len(results["rankings"]["lower-bound"]), 1)
        self.assertEqual(results["rankings"]["lower-bound"][0]["bound_bytes"], 99)
