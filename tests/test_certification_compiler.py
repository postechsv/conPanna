"""Boundary and answer-guided producer regressions, not a second solver.

Run: python3 -B -m unittest discover -s tests -v
Actual semantic/kernel checks live in examples/certification-demo.lean.
This different constructor-code fixture also checks that production does not
depend on Bakery's constructor names/codes. No native unify is called here.
"""
import copy
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import certification_compiler as compiler

SIGNATURE = [
    {"id": 10, "inputs": [], "output": 0, "role": "free"},
    {"id": 11, "inputs": [0], "output": 0, "role": "free"},
    {"id": 12, "inputs": [0], "output": 1, "role": "free"},
    {"id": 13, "inputs": [], "output": 2, "role": "zero"},
    {"id": 14, "inputs": [1], "output": 2, "role": "free"},
    {"id": 15, "inputs": [2, 2], "output": 2, "role": "add"},
    {"id": 16, "inputs": [2, 2], "output": 3, "role": "free"},
]

def var(i):
    return {"var": i}

def app(i, *args):
    return {"app": i, "args": list(args)}

def plus(a, b):
    return app(15, a, b)

def answer(parameters, *images):
    return {"parameters": parameters, "images": list(images)}

def request(scope, eqs, answers):
    return {"aggregate": "system", "problem": "inputSystem", "answers": "inputAnswers",
        "signature": copy.deepcopy(SIGNATURE), "scope": scope, "eqs": eqs, "proposed": answers}

def equation(a, b, sort=2):
    return {"sort": sort, "left": a, "right": b}

def flattened(t):
    if t == app(13):
        return []
    if t.get("app") == 15:
        return flattened(t["args"][0]) + flattened(t["args"][1])
    return [t]

class InputTests(unittest.TestCase):
    def setUp(self):
        self.valid = request([2, 2], [equation(var(0), var(1))],
            [answer([2], var(0), var(0))])

    def test_valid_many_sorted_signature(self):
        compiler.validate_request(self.valid)

    def test_reject_out_of_scope_variable(self):
        self.valid["eqs"][0]["left"] = var(2)
        self.assertRaisesRegex(ValueError, "outside", compiler.validate_request, self.valid)

    def test_reject_wrong_variable_sort(self):
        self.valid["scope"][0] = 0
        self.assertRaisesRegex(ValueError, "wrong sort", compiler.validate_request, self.valid)

    def test_reject_wrong_constructor_sort(self):
        self.valid["eqs"][0]["left"] = app(10)
        self.assertRaisesRegex(ValueError, "wrong sort", compiler.validate_request, self.valid)

    def test_reject_unknown_constructor(self):
        self.valid["eqs"][0]["left"] = app(99)
        self.assertRaisesRegex(ValueError, "unknown constructor", compiler.validate_request, self.valid)

    def test_reject_wrong_arity(self):
        self.valid["eqs"][0]["left"] = app(15, var(0))
        self.assertRaisesRegex(ValueError, "arity", compiler.validate_request, self.valid)

    def test_reject_duplicate_constructor(self):
        self.valid["signature"].append(copy.deepcopy(SIGNATURE[0]))
        self.assertRaisesRegex(ValueError, "duplicate", compiler.validate_request, self.valid)

    def test_reject_recursive_payload_bag(self):
        self.valid["signature"][2]["inputs"] = [2]
        self.assertRaisesRegex(ValueError, "payload", compiler.validate_request, self.valid)

    def test_reject_missing_input_image(self):
        self.valid["proposed"][0]["images"].pop()
        self.assertRaisesRegex(ValueError, "every original", compiler.validate_request, self.valid)

    def test_reject_unused_parameter_without_altering_fixed_goal(self):
        self.valid["proposed"][0]["parameters"].append(0)
        before = copy.deepcopy(self.valid)
        self.assertRaisesRegex(ValueError, "before fixing", compiler.validate_request, self.valid)
        self.assertEqual(before, self.valid)

    def test_reject_boolean_variable_index(self):
        self.valid["eqs"][0]["left"] = var(True)
        self.assertRaisesRegex(ValueError, "natural", compiler.validate_request, self.valid)

class ProducerTests(unittest.TestCase):
    def test_singleton_trace_matches_manual_rule_correspondence(self):
        singleton = app(14, app(12, var(0)))
        trace = compiler.certify(ROOT, request([0, 2, 2],
            [equation(plus(var(1), var(2)), singleton)],
            [answer([0], var(0), singleton, app(13)),
             answer([0], var(0), app(13), singleton)]))
        root = trace["proof"]
        self.assertEqual(root["rule"], "atom")
        self.assertEqual(len(root["children"]), 2)
        for answer_index, branch in enumerate(root["children"]):
            self.assertEqual(branch["rule"], "bind")
            self.assertEqual(branch["child"]["rule"], "bind")
            leaf = branch["child"]["child"]
            self.assertEqual(leaf["rule"], "cover")
            self.assertEqual(leaf["index"], answer_index)
            self.assertEqual(leaf["beta"], [var(0)])

    def test_configuration_binding_exposes_and_retains_bag_fields(self):
        # C=pair(P,Q), C=pair(Q,P), 2P=3Q forces P=Q=empty.
        # The free configuration binding must propagate into the other equation;
        # the bag cycle is handled by zero-sided SHARING, never free OCCURS.
        pair = lambda a, b: app(16, a, b)
        p, q = var(1), var(2)
        trace = compiler.certify(ROOT, request([3, 2, 2],
            [equation(var(0), pair(p, q), 3),
             equation(var(0), pair(q, p), 3),
             equation(plus(p, p), plus(q, plus(q, q)))],
            [answer([], pair(app(13), app(13)), app(13), app(13))]))
        nodes = []
        node = trace["proof"]
        while "child" in node:
            nodes.append(node)
            node = node["child"]
        self.assertEqual(nodes[0]["rule"], "bind")
        self.assertEqual(nodes[0]["sort"], 3)
        self.assertIn("sharing", [n["rule"] for n in nodes])
        self.assertEqual(node["rule"], "cover")
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

    def test_two_bag_fields_with_distinct_purified_singletons(self):
        # One enclosing free equation has TWO nonlinear bag frontiers. Naming
        # a singleton in one field must neither lose nor duplicate the other.
        pair = lambda a, b: app(16, a, b)
        a = app(14, app(12, var(0)))
        b = app(14, app(12, var(1)))
        p, q, r, s = (var(i) for i in range(2, 6))
        trace = compiler.certify(ROOT, request([0, 0, 2, 2, 2, 2],
            [equation(pair(plus(p, a), plus(r, b)),
                      pair(plus(q, a), plus(s, b)), 3)],
            [answer([0, 0, 2, 2], var(0), var(1), var(2), var(2), var(3), var(3))]))
        def walk(node):
            yield node
            if "child" in node:
                yield from walk(node["child"])
            for child in node.get("children", []):
                yield from walk(child)
        nodes = list(walk(trace["proof"]))
        self.assertGreaterEqual(sum(n["rule"] == "purify" for n in nodes), 2)
        self.assertGreaterEqual(sum(n["rule"] == "sharing" for n in nodes), 2)
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

    def test_shared_parameter_cannot_cover_independent_fields(self):
        diagonal = answer([2], var(0), var(0))
        general = answer([2, 2, 2], plus(var(0), var(1)), plus(var(0), var(2)))
        trace = compiler.certify(ROOT, request([2, 2], [], [diagonal, general]))
        self.assertEqual(trace["proof"]["rule"], "cover")
        self.assertEqual(trace["proof"]["index"], 1)
        self.assertEqual(flattened(trace["proof"]["beta"][0]), [])
        self.assertEqual(flattened(trace["proof"]["beta"][1]), [var(0)])
        self.assertEqual(flattened(trace["proof"]["beta"][2]), [var(1)])

    def test_repeated_parameter_gets_one_unit_assignment(self):
        image = plus(plus(var(0), var(0)), var(1))
        trace = compiler.certify(ROOT, request([2, 2], [equation(var(0), var(1))],
            [answer([2, 2], image, image)]))
        leaf = trace["proof"]["child"]
        self.assertEqual(leaf["rule"], "cover")
        self.assertEqual(flattened(leaf["beta"][0]), [])
        self.assertEqual(flattened(leaf["beta"][1]), [var(0)])
        bundle = compiler.compile_bundle(trace)
        self.assertTrue(any(s.get("rule") == "bind_successor" for s in bundle["steps"]))

    def test_incomplete_diagonal_family_fails_closed(self):
        self.assertRaisesRegex(ValueError, "could not close", compiler.certify, ROOT,
            request([2, 2], [], [answer([2], var(0), var(0))]))

    def test_unsound_identity_answer_fails_closed(self):
        self.assertRaisesRegex(ValueError, "could not close", compiler.certify, ROOT,
            request([2, 2], [equation(var(0), var(1))],
                [answer([2, 2], var(0), var(1))]))

    def test_omitted_singleton_branch_fails_closed(self):
        singleton = app(14, app(12, var(0)))
        self.assertRaisesRegex(ValueError, "could not close", compiler.certify, ROOT,
            request([0, 2, 2], [equation(plus(var(1), var(2)), singleton)],
                [answer([0], var(0), singleton, app(13))]))

    def test_two_nonlinear_equations_preserve_independent_parameters(self):
        twice = lambda x: plus(x, x)
        thrice = lambda x: plus(x, plus(x, x))
        trace = compiler.certify(ROOT, request([2, 2, 2, 2],
            [equation(twice(var(0)), thrice(var(1))),
             equation(thrice(var(2)), twice(var(3)))],
            [answer([2, 2], thrice(var(0)), twice(var(0)), twice(var(1)), thrice(var(1)))]))
        nodes, leaf = [], trace["proof"]
        while "child" in leaf:
            nodes.append(leaf)
            leaf = leaf["child"]
        self.assertEqual(sum(n["rule"] == "sharing" for n in nodes), 2)
        self.assertEqual(leaf["rule"], "cover")
        self.assertNotEqual(flattened(leaf["beta"][0]), flattened(leaf["beta"][1]))
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

if __name__ == "__main__":
    unittest.main()
