import unittest
from judge.score import standings


def entry(track, run, team, bound):
    return {"track": track, "run": run, "team": team, "bound_bytes": bound}


class ScoringTests(unittest.TestCase):
    def test_priority_and_minimum_maximum(self):
        results = standings([entry("lower-bound", 30, "a", 101), entry("construction", 35, "c", 720),
                             entry("lower-bound", 10, "b", 100), entry("construction", 25, "d", 750),
                             entry("lower-bound", 50, "c", 101), entry("lower-bound", 20, "b", 100)])
        self.assertEqual(results["best"], {"construction": 720, "lower-bound": 101})
        self.assertEqual([row["delta"] for row in results["history"]], [1, 0, 6, 1, 30, 0])
        self.assertEqual([row["team"] for row in results["rankings"]["lower-bound"]], ["a", "b"])
        self.assertEqual([row["team"] for row in results["rankings"]["construction"]], ["c", "d"])

    def test_opening_proofs_do_not_rank_a_team(self):
        entries = [entry("lower-bound", 1, "example", 99), entry("construction", 2, "example", 756)]
        results = standings(entries)
        self.assertEqual(results["best"], results["opening"])
        self.assertEqual(results["rankings"], {"lower-bound": [], "construction": []})
        self.assertEqual([row["delta"] for row in results["history"]], [0, 0])

    def test_construction_opening_threshold(self):
        results = standings([entry("construction", 1, "larger", 757),
                             entry("construction", 2, "tied", 756),
                             entry("construction", 3, "smaller", 755)])
        self.assertEqual([(row["record"], row["delta"]) for row in results["history"]],
                         [(False, -1), (False, 0), (True, 1)])
        self.assertEqual([row["team"] for row in results["rankings"]["construction"]], ["smaller"])

    def test_one_place_per_team(self):
        results = standings([entry("lower-bound", 10, "a", 100), entry("lower-bound", 20, "a", 101)])
        self.assertEqual(len(results["rankings"]["lower-bound"]), 1)
        self.assertEqual(results["rankings"]["lower-bound"][0]["bound_bytes"], 101)
