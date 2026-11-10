#!/usr/bin/env python3
"""Check sampling regressions without requiring another SMT solver.

Run with: python3 tests/sampling/test_models.py build/csb
"""

import argparse
from pathlib import Path
import re
import subprocess
import unittest


FIXTURES = Path(__file__).resolve().parent
DEFINITION = re.compile(
    r"\(\s*define-fun\s+\|([^|]+)\|\s+\(\)\s+"
    r"(Bool|\(_ BitVec (\d+)\))\s+"
    r"(true|false|#b[01]+|#x[0-9a-fA-F]+)\s*\)"
)


class SamplingModels(unittest.TestCase):
    def output(self, fixture, *options):
        result = subprocess.run(
            [str(SOLVER), *options, str(FIXTURES / fixture)],
            capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def parse_models(self, output, expected):
        blocks = re.findall(r"\(model\s*\n(.*?)\n\)", output, re.DOTALL)
        self.assertEqual(len(blocks), expected, output)
        models = []
        for block in blocks:
            model = {}
            for name, sort, width, literal in DEFINITION.findall(block):
                self.assertNotIn(name, model)
                if sort == "Bool":
                    self.assertIn(literal, ("true", "false"))
                    model[name] = literal == "true"
                else:
                    self.assertTrue(literal.startswith(("#b", "#x")))
                    value = int(literal[2:], 2 if literal[1] == "b" else 16)
                    self.assertLess(value, 1 << int(width))
                    model[name] = value
            self.assertTrue(model, block)
            models.append(model)
        return models

    def samples(self, fixture, seed, count=128, backend="-s"):
        output = self.output(fixture, backend, "-n", str(count), "--seed", str(seed))
        # unconstrained.smt2 also explicitly requests the last model.
        expected = count + (fixture == "unconstrained.smt2")
        models = self.parse_models(output, expected)
        if fixture == "unconstrained.smt2":
            self.assertEqual(models[-1], models[-2], "get-model changed the sample")
            models.pop()
        return models

    def check_boolean_connectives(self, model):
        self.assertEqual(set(model), {"a", "b", "c", "d"})
        self.assertEqual(model["a"], not model["b"], model)
        self.assertEqual(model["c"], model["a"] != model["d"], model)
        self.assertTrue(not model["d"] or model["c"], model)
        self.assertTrue(model["b"] or model["c"], model)

    def check_mixed_bitvectors(self, model):
        self.assertEqual(set(model), {"choose", "spare", "x", "y", "result"})
        x, y, result = model["x"], model["y"], model["result"]
        self.assertEqual(result, (x + y if model["choose"] else x - y) & 7, model)
        self.assertLess(x, 6, model)
        self.assertNotEqual(y, 0, model)
        signed_result = result if result < 4 else result - 8
        self.assertLess(signed_result, 2, model)
        self.assertEqual(result & 1, 1, model)

    def test_minimal_issue14(self):
        for seed in (12, 18, 42):
            with self.subTest(seed=seed):
                count = 1000 if seed == 18 else 128
                for model in self.samples("minimal.smt2", seed, count):
                    self.assertEqual(set(model), {"v1", "v2"})
                    self.assertTrue(model["v1"] or not model["v2"], model)

    def test_boolean_connectives(self):
        for backend in ("-s", "-u"):
            with self.subTest(backend=backend):
                for model in self.samples("boolean-connectives.smt2", 18, 32, backend):
                    self.check_boolean_connectives(model)

    def test_mixed_bitvectors_and_unused_boolean(self):
        for backend in ("-s", "-u"):
            with self.subTest(backend=backend):
                for model in self.samples("mixed-bitvectors.smt2", 18, 32, backend):
                    self.check_mixed_bitvectors(model)

    def test_projected_samples_include_consistent_witnesses(self):
        models = self.samples("projected.smt2", 18)
        for model in models:
            self.assertEqual(set(model), {"flag", "witness", "odd"})
            self.assertEqual(model["flag"], model["witness"] < 4, model)
            self.assertEqual(model["odd"], bool(model["witness"] & 1), model)
        self.assertEqual({model["flag"] for model in models}, {False, True})

    def test_all_minimal_solutions_remain_sampleable(self):
        models = self.samples("minimal.smt2", 18)
        self.assertEqual({(m["v1"], m["v2"]) for m in models},
                         {(False, False), (True, False), (True, True)})

    def test_unigen_true_and_false(self):
        for model in self.samples("forced-booleans.smt2", 18, 32, "-u"):
            self.assertEqual(model, {"yes": True, "no": False, "copy": False})

    def test_sat_solver_model_reconstruction(self):
        # SAT mode enables simplifications and substitution-map reconstruction.
        for backend in ("--minisat", "--simplifying-minisat"):
            for fixture, check in (
                ("boolean-connectives.smt2", self.check_boolean_connectives),
                ("mixed-bitvectors.smt2", self.check_mixed_bitvectors),
            ):
                with self.subTest(backend=backend, fixture=fixture):
                    models = self.parse_models(self.output(fixture, backend, "-p"), 1)
                    check(models[0])

    def test_unsatisfiable_inputs_have_no_models(self):
        for options in (("-s", "-n", "1"), ("--minisat", "-p")):
            with self.subTest(options=options):
                output = self.output("unsat.smt2", *options)
                self.assertRegex(output, r"(?m)^unsat$")
                self.parse_models(output, 0)

    def check_counts(self, backend):
        # Exhaustively count the small arithmetic fixture, including spare Bool.
        mixed_count = 2 * sum(
            1 for choose in (False, True) for x in range(6) for y in range(1, 8)
            if ((x + y if choose else x - y) & 7) in (1, 5, 7)
        )
        for fixture, expected in (
            ("minimal.smt2", 3), ("forced-booleans.smt2", 1),
            ("boolean-connectives.smt2", 3), ("projected.smt2", 2),
            ("mixed-bitvectors.smt2", mixed_count), ("unsat.smt2", 0),
            ("unconstrained.smt2", 1 << 75),
        ):
            with self.subTest(backend=backend, fixture=fixture):
                output = self.output(fixture, backend)
                counts = re.findall(r"(?m)^s mc (\d+)$", output)
                self.assertEqual(counts, [str(expected)], output)

    def test_exact_counting(self):
        if "--ganak" not in self.output("minimal.smt2", "--help"):
            self.skipTest("Ganak backend is not enabled")
        self.check_counts("--ganak")

    def test_approximate_counting_on_small_inputs(self):
        self.check_counts("-a")

    def test_bitvector_ite_issue14(self):
        for seed in (12, 18, 42):
            with self.subTest(seed=seed):
                for model in self.samples("bitvector-ite.smt2", seed):
                    self.assertEqual(set(model), {
                        "Z.cond1", "Z.cond2", "Z.a", "Z.b", "Z.c", "Z.result",
                    })
                    for name in ("Z.a", "Z.b", "Z.c"):
                        self.assertLess(model[name], 2, model)
                    selected = (model["Z.a"] if model["Z.cond1"] else
                                model["Z.b"] if model["Z.cond2"] else model["Z.c"])
                    self.assertEqual(model["Z.result"], selected, model)

    def test_forced_true_and_false(self):
        for model in self.samples("forced-booleans.smt2", 18):
            self.assertEqual(model, {"yes": True, "no": False, "copy": False})

    def test_seed_reproducibility(self):
        for fixture in ("minimal.smt2", "bitvector-ite.smt2", "unconstrained.smt2"):
            for count in (1, 32):
                with self.subTest(fixture=fixture, count=count):
                    first = self.samples(fixture, 18, count)
                    # Compare assignments, since definition order is immaterial.
                    self.assertEqual(first, self.samples(fixture, 18, count))

    def test_unconstrained_bits_are_sampled(self):
        models = self.samples("unconstrained.smt2", 18)
        for model in models:
            self.assertEqual(set(model), {"flag", "other", "wide", "byte"})
        for name in ("flag", "other", "wide", "byte"):
            self.assertGreater(len({model[name] for model in models}), 1, name)
        self.assertEqual({model["wide"] >> 64 for model in models}, {0, 1})
        # All 64 bits of --seed must affect completion, including its high half.
        self.assertNotEqual(models, self.samples("unconstrained.smt2", 18 + (1 << 32)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver", type=Path)
    args, remaining = parser.parse_known_args()
    SOLVER = args.solver.resolve()
    unittest.main(argv=[__file__] + remaining)
