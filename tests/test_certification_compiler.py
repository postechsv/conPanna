"""Boundary and answer-guided producer regressions, not a second solver.

Run: python3 -B -m unittest discover -s tests -v
Focused kernel negatives: python3 -B tests/test_certification_compiler.py --negatives
Actual semantic/kernel checks live in examples/certification-demo.lean.
This different constructor-code fixture also checks that production does not
depend on Bakery's constructor names/codes. Coordinator tests also call native unify.
"""
import copy
import json
import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "certifier"))
import certifier as compiler

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
    def test_named_finite_side_conditions(self):
        table = compiler.checked_table([[1, 0], [0, 1]])
        self.assertEqual(table.count("SideCondition.tableCons"), 2)
        self.assertNotIn("funext", table)
        self.assertNotIn("congrArg", table)
        branches = compiler.atom_children([0, 2], [None, None])
        self.assertEqual(branches.count("SideCondition.finCons"), 2)
        self.assertEqual(branches.count("SideCondition.noSupplier"), 2)
        self.assertNotIn("False.elim", branches)

    def test_atom_branch_slots_cannot_be_omitted(self):
        self.assertRaisesRegex(ValueError, "one slot", compiler.atom_children,
            [1, 1], [None])
        self.assertRaisesRegex(ValueError, "one slot", compiler.atom_children,
            [], [None])
        self.assertRaisesRegex(ValueError, "non-unit", compiler.atom_children,
            [2], [{}])
        self.assertRaisesRegex(ValueError, "requires a branch", compiler.atom_children,
            [1], [None])

    def test_fast_normal_forms_agree_with_proof_normalization(self):
        import random
        rng = random.Random(47)
        leaves = [var(0), var(1), app(13), app(14, app(12, app(10))),
            app(14, app(12, app(11, app(10))))]
        def bag(depth):
            return rng.choice(leaves) if depth == 0 or rng.randrange(3) == 0 else plus(bag(depth - 1), bag(depth - 1))
        hs = compiler.maude_heads(SIGNATURE)
        commands = ["mod NORMALIZATION-CHECK is protecting CERTIFICATION-PRODUCER .",
            "op erased : Nat Term Heads -> Term . vars S : Nat . vars A B : Term .",
            "vars HS : Heads . vars P : String .",
            "ceq erased(S, A, HS) = B if normal(B, P) := norm(S, A, HS) . endm"]
        for _ in range(32):
            a = bag(2)
            for sort, term in [(2, a), (3, app(16, a, bag(2)))]:
                encoded = compiler.maude_term(term)
                commands.append(f"red in NORMALIZATION-CHECK : normalized({sort},{encoded},{hs}) == erased({sort},{encoded},{hs}) .")
        output = compiler.maude_run(ROOT, "\n".join(commands))
        self.assertEqual(output.count("result Bool: true"), 64)
        self.assertNotIn("result Bool: false", output)

    def test_answer_guided_witnesses_close_by_existing_mutate(self):
        p, q, r, s = (var(i) for i in range(4))
        rq = request([2] * 4, [equation(plus(p, q), plus(r, s))],
            [answer([2] * 4, plus(p, q), plus(r, s), plus(p, r), plus(q, s))])
        trace = compiler.certify(ROOT, rq)
        self.assertEqual(trace["proof"]["rule"], "mutate")
        child = trace["proof"]["child"]
        self.assertEqual(child["rule"], "cover")
        self.assertEqual(child["scope"], [2] * 8)
        self.assertEqual(child["beta"], [p, q, r, s])
        bundle = compiler.compile_bundle(trace)
        self.assertTrue(any(step.get("rule") == "mutate_successor" for step in bundle["steps"]))
        # Same equation and a correlated but incomplete answer must NOT close
        # the FINITE witness attempt. Do not run an expensive doomed fallback.
        rq["proposed"] = [answer([2], p, p, p, p)]
        command = "red in CERTIFICATION-PRODUCER : tryWitness(" + compiler.maude_context(rq["scope"]) + "," + \
            compiler.maude_terms([p, q, r, s]) + "," + compiler.maude_equations(rq["eqs"]) + "," + \
            compiler.maude_answers(rq["proposed"]) + "," + compiler.maude_context(rq["scope"]) + "," + \
            compiler.maude_heads(rq["signature"]) + "," + compiler.maude_term(plus(p, q)) + "," + \
            compiler.maude_term(plus(r, s)) + ",hypText(0)) ."
        self.assertIn("result CoverChoice: noCover", compiler.maude_run(ROOT, command))

    def test_untargeted_receives_no_answers_and_generates_its_own_family(self):
        rq = request([2, 2], [equation(plus(var(0), var(0)), plus(var(1), var(1)))], [])
        trace = compiler.untargeted_unify(ROOT, rq)
        self.assertEqual(trace["proof"]["rule"], "sharing")
        self.assertEqual(len(trace["generated"]), 1)
        self.assertTrue(compiler.compile_bundle(trace)["steps"])
        rq["proposed"] = [answer([2], var(0), var(0))]
        self.assertRaisesRegex(ValueError, "NO supplied", compiler.untargeted_unify, ROOT, rq)

    def test_untargeted_numbers_distinct_singleton_leaves(self):
        a = app(14, app(12, var(0)))
        trace = compiler.untargeted_unify(ROOT,
            request([0, 2, 2], [equation(plus(var(1), var(2)), a)], []))
        self.assertEqual(len(trace["generated"]), 2)
        leaves = []
        def visit(node):
            if node["rule"] == "cover":
                leaves.append(node["index"])
            if "child" in node:
                visit(node["child"])
            for child in node.get("children", []):
                visit(child)
        visit(trace["proof"])
        self.assertEqual(leaves, [0, 1])
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

    def test_bag_cycle_is_covered_by_cancellation_not_free_occurs(self):
        trace = compiler.certify(ROOT, request([2, 2],
            [equation(var(0), plus(var(0), var(1)))],
            [answer([2], var(0), app(13))]))
        self.assertEqual(trace["proof"]["rule"], "cover")
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

    def test_cyclic_definitions_stop_without_pruning_a_solution(self):
        # P=[a]+Q and Q=P+[b] is genuinely impossible, but conditional
        # rewriting itself must just stop; the existing NONEMPTY branch proves it.
        a = app(14, app(12, app(10)))
        b = app(14, app(12, app(11, app(10))))
        trace = compiler.certify(ROOT, request([2, 2],
            [equation(var(0), plus(a, var(1))),
             equation(var(1), plus(var(0), b))], []))
        self.assertNotEqual(trace["proof"]["rule"], "cover")
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

    def test_equal_powers_cover_before_sharing(self):
        # Native's diagonal answer guides closure; the proof uses multiplicity
        # cancellation, not a 2-by-2 sharing table or a guessed ground instance.
        trace = compiler.certify(ROOT, request([2, 2],
            [equation(plus(var(0), var(0)), plus(var(1), var(1)))],
            [answer([2], var(0), var(0))]))
        self.assertEqual(trace["proof"]["rule"], "cover")
        def has_rule(node, rule):
            if isinstance(node, dict):
                return node.get("rule") == rule or any(has_rule(x, rule) for x in node.values())
            return isinstance(node, list) and any(has_rule(x, rule) for x in node)
        self.assertTrue(has_rule(trace["proof"]["derived"], "multiplicity"))
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

    def test_larger_equal_powers_do_not_enumerate_a_grid(self):
        # A 7-by-7 fallback grid has 2^49 subsets. The answer-guided shortcut
        # emits one COVER with multiplicity evidence instead of constructing it.
        def copies(k, term):
            result = app(13)
            for _ in range(k):
                result = plus(term, result)
            return result
        trace = compiler.certify(ROOT, request([2, 2],
            [equation(copies(7, var(0)), copies(7, var(1)))],
            [answer([2], var(0), var(0))]))
        self.assertEqual(trace["proof"]["rule"], "cover")
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

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
            self.assertEqual(branch["rule"], "cover")
            leaf = branch
            self.assertEqual(leaf["rule"], "cover")
            self.assertEqual(leaf["index"], answer_index)
            self.assertEqual(leaf["beta"], [var(0)])
        generated = "\n".join(s["value"] for s in compiler.compile_bundle(trace)["steps"])
        self.assertIn("SideCondition.finCons", generated)
        self.assertNotIn("Fin.cases", generated)

    def test_configuration_binding_exposes_and_retains_bag_fields(self):
        # C=pair(P,Q), C=pair(Q,P), 2P=3Q forces P=Q=empty.
        # The free configuration binding must propagate into the other equation;
        # the bag cycle is now closed by conditional CANCEL/zero evidence.
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
        self.assertNotIn("sharing", [n["rule"] for n in nodes])
        self.assertEqual(node["rule"], "cover")
        self.assertTrue(compiler.compile_bundle(trace)["steps"])

    def test_two_bag_fields_with_distinct_purified_singletons(self):
        # Two bag fields are independently cancelled with checked DECOMPOSE
        # evidence, without purification or sharing of either field.
        pair = lambda a, b: app(16, a, b)
        a = app(14, app(12, var(0)))
        b = app(14, app(12, var(1)))
        p, q, r, s = (var(i) for i in range(2, 6))
        trace = compiler.certify(ROOT, request([0, 0, 2, 2, 2, 2],
            [equation(pair(plus(p, a), plus(r, b)),
                      pair(plus(q, a), plus(s, b)), 3)],
            [answer([0, 0, 2, 2], var(0), var(1), var(2), var(2), var(3), var(3))]))
        def walk(node):
            if isinstance(node, dict):
                yield node
                for child in node.values():
                    yield from walk(child)
            elif isinstance(node, list):
                for child in node:
                    yield from walk(child)
        self.assertEqual(trace["proof"]["rule"], "cover")
        nodes = list(walk(trace["proof"]["derived"]))
        self.assertGreaterEqual(sum(n.get("rule") == "cancel" for n in nodes), 2)
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
        leaf = trace["proof"]
        self.assertEqual(leaf["rule"], "cover")
        self.assertEqual(leaf["rule"], "cover")
        self.assertEqual(flattened(leaf["beta"][0]), [])
        self.assertEqual(flattened(leaf["beta"][1]), [var(0)])
        bundle = compiler.compile_bundle(trace)
        self.assertTrue(bundle["steps"])

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

class CoordinatorTests(unittest.TestCase):
    def setUp(self):
        self.rq = compiler.load_json(ROOT / "examples/certification-request.json")
        self.native = compiler.NativeInterface(self.rq)

    def test_two_native_answers_preserve_all_input_images(self):
        output = compiler.maude_run(ROOT, self.native.query(self.rq), source=self.rq["native"]["source"])
        answers = self.native.answers(output)
        self.assertEqual(len(answers), 2)
        self.assertTrue(all(a["parameters"] == [0] for a in answers))
        self.assertTrue(all(a["images"][0] == var(0) for a in answers))
        self.assertNotEqual(answers[0]["images"][1], answers[1]["images"][1])
        compiler.validate_request(dict(self.rq, proposed=answers))

    def test_repeated_parameter_and_flat_associative_output(self):
        output = "Unifier 1\nP:Bag --> union(#1:Bag,#1:Bag,#1:Bag)\nQ:Bag --> #1:Bag\nN:Ticket --> #2:Ticket\n"
        a = self.native.answers(output)[0]
        self.assertEqual(a["parameters"], [0, 2])
        self.assertEqual(a["images"][1], app(7, var(1), app(7, var(1), var(1))))
        self.assertEqual(a["images"][2], var(1))

    def test_missing_binding_is_a_passthrough_not_an_empty_term(self):
        a = self.native.answers("Unifier 1\nP:Bag --> Q:Bag\n")[0]
        self.assertEqual(a["parameters"], [0, 2])
        self.assertEqual(a["images"], [var(0), var(1), var(1)])

    def test_native_answer_parameters_are_local_to_each_unifier(self):
        answers = self.native.answers("Unifier 1\nP:Bag --> #1:Bag\nQ:Bag --> #1:Bag\n"
            "Unifier 2\nP:Bag --> empty\nQ:Bag --> #1:Bag\n")
        self.assertEqual(answers[0]["parameters"], [0, 2])
        self.assertEqual(answers[1]["parameters"], [0, 2])

    def test_reject_wrong_sort_or_unknown_constructor(self):
        for image in ("#1:Ticket", "mystery(#1:Bag)"):
            with self.subTest(image=image):
                self.assertRaises(ValueError, self.native.answers, "Unifier 1\nP:Bag --> " + image)

    def test_reject_duplicate_domain_or_cyclic_substitution(self):
        for output in ("Unifier 1\nP:Bag --> empty\nP:Bag --> empty",
                "Unifier 1\nP:Bag --> Q:Bag\nQ:Bag --> union(P:Bag,empty)"):
            self.assertRaises(ValueError, self.native.answers, output)

    def test_reject_already_supplied_answers(self):
        self.rq["proposed"] = [answer([0, 2, 2], var(0), var(1), var(2))]
        self.assertRaisesRegex(ValueError, "--certify", compiler.NativeInterface, self.rq)

    def test_no_unifier_is_an_empty_family(self):
        self.assertEqual(self.native.answers("No unifier.\nBye."), [])
        self.assertRaises(ValueError, self.native.answers, "Unifier 1\nNo unifier.")

    def test_ground_native_success_keeps_all_unmentioned_inputs(self):
        rq = dict(self.rq, eqs=[equation(app(5), app(5))])
        output = compiler.maude_run(ROOT, self.native.query(rq), source=rq["native"]["source"])
        self.assertEqual(self.native.answers(output), [answer([0, 2, 2], var(0), var(1), var(2))])

    def test_real_empty_native_family_is_certified_not_confused_with_failure(self):
        from tempfile import TemporaryDirectory
        rq = dict(self.rq, eqs=[equation(app(5), app(6, app(3, var(0))))])
        with TemporaryDirectory(prefix="conpanna-coordinator-") as temp:
            result = compiler.coordinate(ROOT, rq, Path(temp))
            self.assertEqual(result["request"]["proposed"], [])
            trace = compiler.load_json(Path(temp) / "03-trace.json")
            self.assertEqual(trace["answers"], "coordinatedAnswers")
            self.assertIsInstance(trace["proof"], dict)
            self.assertEqual(result["certificate"]["format"], "rule-bundle-v1")

    def test_full_and_manual_stages_use_identical_certification_queries(self):
        from tempfile import TemporaryDirectory
        with TemporaryDirectory(prefix="conpanna-coordinator-") as temp:
            out = Path(temp)
            result = compiler.coordinate(ROOT, self.rq, out)
            target = compiler.load_json(out / "02-target.json")
            self.assertEqual(len(target["proposed"]), 2)
            query = (out / "02-target-query.maude").read_text().strip()
            self.assertEqual(query, compiler.certification_query(target, "CERTIFICATION-QUERY"))
            self.assertEqual(compiler.compile_target(out, (out / "02-target.stdout").read_text()), result)
            self.assertEqual(result["certificate"]["format"], "rule-bundle-v1")
            self.assertFalse(compiler.load_json(out / "status.json")["kernel_checked"])
            self.assertIn("protecting BAKERY-DEMO-NATIVE", (out / "wrapper.maude").read_text())
            self.assertIn("protecting CERTIFICATION-PRODUCER", (out / "wrapper.maude").read_text())
            other = copy.deepcopy(self.rq)
            other["eqs"][0]["left"] = var(1)
            self.assertRaisesRegex(ValueError, "another request", compiler.prepare_native, ROOT, other, out)

class NativeInputTests(unittest.TestCase):
    QUERY = "unify in BAKERY-DEMO-NATIVE : union(P:Bag,Q:Bag) =? singleton(wait(N:Ticket)) ."
    MODEL = ROOT / "certifier/examples/bakery.maude"

    def test_inferred_data_agrees_with_legacy_typed_fixture(self):
        inferred = compiler.native_request(self.MODEL, self.QUERY)
        legacy = compiler.load_json(ROOT / "examples/certification-request.json")
        for key in ("signature", "scope", "eqs"):
            self.assertEqual(inferred[key], legacy[key])
        for key in ("sort_names", "constructor_names", "variables", "module"):
            self.assertEqual(inferred["native"][key], legacy["native"][key])

    def test_multiple_equations_share_original_variable_slots(self):
        rq = compiler.native_request(self.MODEL,
            "unify in BAKERY-DEMO-NATIVE : P:Bag =? Q:Bag /\\ Q:Bag =? singleton(wait(N:Ticket)) .")
        self.assertEqual(rq["native"]["variables"], ["N", "P", "Q"])
        self.assertEqual(rq["eqs"][0], equation(var(1), var(2)))
        self.assertEqual(rq["eqs"][1], equation(var(2), app(6, app(3, var(0)))))

    def test_reject_bad_queries_before_any_external_process(self):
        for query in (
            self.QUERY + " quit .",
            self.QUERY.replace("BAKERY-DEMO-NATIVE", "WRONG"),
            "unify in BAKERY-DEMO-NATIVE : union(P:Bag,P:Ticket) =? empty .",
            "unify in BAKERY-DEMO-NATIVE : empty =? zero .",
            "unify in BAKERY-DEMO-NATIVE : P:Bag =? #1:Bag .",
            "unify in BAKERY-DEMO-NATIVE : P:Bag =? Q:Missing .",
        ):
            with self.subTest(query=query):
                self.assertRaises(ValueError, compiler.native_request, self.MODEL, query)

    def test_reject_extra_model_theories_or_declarations(self):
        from unittest.mock import Mock
        model = self.MODEL.read_text()
        for extra in ("protecting NAT .", "eq empty = empty .", "subsort Ticket < Mode ."):
            with self.subTest(extra=extra):
                source = Mock(read_text=Mock(return_value=model.replace("endfm", extra + "\nendfm")))
                self.assertRaises(ValueError, compiler.native_request, source, self.QUERY)
        source = Mock(read_text=Mock(return_value=model.replace("assoc comm", "comm")))
        self.assertRaises(ValueError, compiler.native_request, source, self.QUERY)

    def test_renamed_model_is_not_bakery_specific(self):
        from tempfile import TemporaryDirectory
        replacements = {"BAKERY-DEMO-NATIVE": "CLIENT", "Ticket": "Token", "Mode": "Item",
            "Bag": "Pool", "Conf": "Record", "singleton": "inject", "union": "sum",
            "empty": "none", "wait": "active"}
        text = self.MODEL.read_text()
        for old, new in replacements.items():
            text = text.replace(old, new)
        with TemporaryDirectory(prefix="conpanna-native-") as temp:
            model = Path(temp) / "client.maude"
            model.write_text(text)
            rq = compiler.native_request(model,
                "unify in CLIENT : sum(L:Pool,R:Pool) =? inject(active(T:Token)) .")
            result = compiler.coordinate(ROOT, rq, Path(temp) / "cache")
            self.assertEqual(len(result["request"]["proposed"]), 2)
            self.assertEqual(rq["native"]["variables"], ["L", "R", "T"])
            self.assertEqual(result["certificate"]["format"], "rule-bundle-v1")

    def test_standalone_package_needs_no_repository_or_lean(self):
        from tempfile import TemporaryDirectory
        import shutil
        with TemporaryDirectory(prefix="standalone-certifier-") as temp:
            bundle = Path(temp) / "engine"
            bundle.mkdir()
            for name in ("certifier.py", "wrapper.maude", "certification.maude"):
                shutil.copy2(ROOT / "certifier" / name, bundle / name)
            shutil.copy2(self.MODEL, Path(temp) / "input.maude")
            compiler.run_checked([sys.executable, "-B", str(bundle / "certifier.py"),
                "--ctor", str(Path(temp) / "input.maude"), "--unify", self.QUERY], cwd=Path(temp))
            out = bundle / ".cache"
            reply = compiler.load_json(out / "result.json")
            self.assertEqual(len(reply["request"]["proposed"]), 2)
            self.assertEqual(reply["certificate"]["format"], "rule-bundle-v1")
            self.assertEqual((out / "ctor.maude").read_text(), self.MODEL.read_text())
            self.assertIn("load ctor.maude", (out / "wrapper.maude").read_text())
            self.assertFalse(compiler.load_json(out / "status.json")["kernel_checked"])
            # Reuse the same cache with a different, ground, unsatisfiable query.
            compiler.run_checked([sys.executable, "-B", str(bundle / "certifier.py"),
                "--ctor", str(Path(temp) / "input.maude"), "--unify",
                "unify in BAKERY-DEMO-NATIVE : empty =? singleton(wait(zero)) ."], cwd=Path(temp))
            reply = compiler.load_json(out / "result.json")
            self.assertEqual(reply["request"]["scope"], [])
            self.assertEqual(reply["request"]["proposed"], [])

    def test_client_names_do_not_collide_with_calculus_types_and_helpers(self):
        from tempfile import TemporaryDirectory
        text = self.MODEL.read_text().replace("Bag", "Terms").replace("union", "appendTerms")
        with TemporaryDirectory(prefix="certifier-names-") as temp:
            model = Path(temp) / "client.maude"
            model.write_text(text)
            rq = compiler.native_request(model,
                "unify in BAKERY-DEMO-NATIVE : appendTerms(P:Terms,Q:Terms) =? singleton(wait(N:Ticket)) .")
            result = compiler.coordinate(ROOT, rq, Path(temp) / "cache")
            self.assertEqual(len(result["request"]["proposed"]), 2)
            wrapper = (Path(temp) / "cache/wrapper.maude").read_text()
            self.assertIn("sort Terms to NativeSort2", wrapper)

    def test_interrupted_new_request_invalidates_old_proof_artifacts(self):
        from tempfile import TemporaryDirectory
        with TemporaryDirectory(prefix="certifier-cache-") as temp:
            out = Path(temp)
            rq = compiler.native_request(self.MODEL, self.QUERY)
            compiler.coordinate(ROOT, rq, out)
            new = compiler.native_request(self.MODEL,
                "unify in BAKERY-DEMO-NATIVE : P:Bag =? Q:Bag .")
            compiler.prepare_native(ROOT, new, out, replace=True)
            self.assertEqual(compiler.load_json(out / "result.json")["stage"], "pending")
            self.assertEqual(compiler.load_json(out / "04-proof.json")["stage"], "pending")

# Standalone test harnesses, NOT part of the coordinator package.
def precompile(root):
    """Cache the unchanged general proofs, not the problem certificate."""
    import time
    cache = root / ".lake/build/certification"
    cache.mkdir(parents=True, exist_ok=True)
    # Let Lake validate dependency traces; do not implement a second build cache.
    ready = compiler.run_checked(["lake", "--no-build", "--no-cache", "build",
        "+conPanna.Certification.Client:olean"], cwd=root, lean=True, allow_stale=True)
    if ready is not None:
        print("Certification backend: cached (Lake validated dependencies)", flush=True)
        return cache
    # Existing project dependencies must already be built (as in normal Lake use).
    # Explicit steps prevent independent backend modules compiling concurrently.
    for name in ("Core", "Sharing", "Enumeration", "Syntax", "Calculus", "Semantics", "Parser", "Client"):
        start = time.monotonic()
        # Lake creates .ilean and dependency traces needed by the editor.
        # --old avoids unrelated transitive rebuilds in this experiment.
        # The Certification library itself fixes -j1 -M512 in lakefile.toml.
        compiler.run_checked(["lake", "--old", "--no-cache", "build",
            f"+conPanna.Certification.{name}:olean"], cwd=root, lean=True)
        print(f"{name}: ready in {time.monotonic() - start:.2f}s", flush=True)
    return cache

def native_demo_answer(output):
    """Fixed DEMO grammar; unknown/multiple answers fail, never silently certify."""
    if len(re.findall(r"^Unifier \d+$", output, re.MULTILINE)) != 1:
        raise ValueError("demo expects exactly one proposed native unifier")
    pairs = re.findall(r"^(P:Bag|Q:Bag|N:Ticket) --> (.+)$", output, re.MULTILINE)
    bindings = dict(pairs)
    if len(pairs) != 3 or len(bindings) != 3:
        raise ValueError("unexpected native answer variables")
    parameter = bindings["N:Ticket"]
    if not re.fullmatch(r"#\d+:Ticket", parameter):
        raise ValueError("unexpected native ticket parameter")
    expected = f"singleton(wait({parameter}))"
    if bindings["P:Bag"] != expected or bindings["Q:Bag"] != expected:
        raise ValueError("native answer is outside this demo's input contract")
    # Transparent signature map: ticket=s0, bag=s2, wait=c3, singleton=c6.
    atom = {"app": 6, "args": [{"app": 3, "args": [{"var": 0}]}]}
    return [{"var": 0}, atom, atom]

def comparison_cases():
    """Small empirical fixtures, NOT constructor-specific search heuristics.

    Codes match the existing Bakery registered signature and are kernel-checked
    against it below. Targeted Sigma is fixed here; baseline gets only E and B.
    """
    signature = [
        {"id": i, "inputs": args, "output": sort, "role": role}
        for i, args, sort, role in [
            (0, [], 0, "free"), (1, [0], 0, "free"),
            (2, [], 1, "free"), (3, [0], 1, "free"), (4, [0], 1, "free"),
            (5, [], 2, "zero"), (6, [1], 2, "free"),
            (7, [2, 2], 2, "add"), (8, [0, 0, 2], 3, "free")]]
    v = lambda i: {"var": i}
    app = lambda i, *args: {"app": i, "args": list(args)}
    plus = lambda a, b: app(7, a, b)
    def copies(k, a):
        result = app(5)
        for _ in range(k):
            result = plus(a, result)
        return result
    def case(name, context, left, right, answers):
        return name, {"aggregate": "system", "problem": "inputSystem", "answers": "inputAnswers",
            "signature": signature, "scope": context,
            "eqs": [{"sort": 2, "left": left, "right": right}], "proposed": answers}
    def answer(context, *images):
        return {"parameters": context, "images": list(images)}
    yield case("2P = 2Q", [2, 2], copies(2, v(0)), copies(2, v(1)),
        [answer([2], v(0), v(0))])
    yield case("3P = 3Q", [2, 2], copies(3, v(0)), copies(3, v(1)),
        [answer([2], v(0), v(0))])
    atom = app(6, app(3, v(0)))
    yield case("P + Q = [wait n]", [0, 2, 2], plus(v(1), v(2)), atom,
        [answer([0], v(0), atom, app(5)), answer([0], v(0), app(5), atom)])
    yield case("P + [wait n] = Q + [wait n]", [0, 2, 2], plus(v(1), atom), plus(v(2), atom),
        [answer([0, 2], v(0), v(1), v(1))])
    yield case("P + Q = R + S", [2] * 4, plus(v(0), v(1)), plus(v(2), v(3)),
        [answer([2] * 4, plus(v(0), v(1)), plus(v(2), v(3)), plus(v(0), v(2)), plus(v(1), v(3)))])
    yield case("2P = 3Q (fallback control)", [2, 2], copies(2, v(0)), copies(3, v(1)),
        [answer([2], copies(3, v(0)), copies(2, v(0)))])

def check_comparison_certificate(root, cache, request, trace, bundle):
    """Standalone TEST harness. Production never invokes an external Lean checker.

    For baseline, the goal is exactness of its newly computed family; for
    targeted, exactness of the pre-supplied family. They need not be identical.
    Generated baseline contexts deliberately retain redundant passthrough slots.
    """
    proof_path = cache / "comparison.proof.json"
    proof_path.write_text(json.dumps(bundle) + "\n")
    proposed = trace["generated"] if "generated" in trace else request["proposed"]
    answer_data = ["{ parameters := " + compiler.scope(a["parameters"]) +
        ", images := " + compiler.terms(a["images"]) + " }" for a in proposed]
    source = """import conPanna.Certification.Client
import examples.bakery_acu
namespace CertificationComparison
open BakeryACU Structural.Indexed BakeryACU.BakeryTheory.Generated
open DirectCertification DirectCertification.Substitution DirectCertification.Substitution.Worklist
derive_direct_profile profile for BakeryTheory.certified
""" + "def inputSystem : List (Problem Sig " + compiler.scope(request["scope"]) + ") := " + compiler.equations(request["eqs"]) + "\n" + \
        "def inputAnswers : List (Answer Sig " + compiler.scope(request["scope"]) + ") := [" + ",".join(answer_data) + "]\n" + \
        "run_elab do\n  let dump ← IO.FS.readFile " + json.dumps(str(proof_path)) + "\n" + \
        "  let expected ← `(∀ values, Worklist.Holds registration inputSystem values ↔ Solutions registration inputAnswers values)\n" + \
        "  let (type, proof) ← LeanReady.prepareProof expected dump\n" + \
        "  Lean.addDecl (.thmDecl { name := `CertificationComparison.checked, levelParams := [], type := type, value := proof })\n" + \
        "#print axioms checked\nend CertificationComparison\n"
    source_path = cache / "comparison.lean"
    source_path.write_text(source)
    return compiler.run_checked(["lake", "env", "lean", "-j1", "-M512", str(source_path)], cwd=root, lean=True)

def compare_search(root):
    """Brief empirical comparison. No upstream native-unification time included."""
    import copy
    import statistics
    import time
    cache = precompile(root)
    rows = []
    for name, original in comparison_cases():
        for mode in ("targeted", "untargeted"):
            request = copy.deepcopy(original)
            if mode == "untargeted":
                request["proposed"] = []
            print(f"Comparing {name}: {mode}", flush=True)
            row = {"problem": name, "mode": mode, "failure_phase": "search_or_reference_dump"}
            try:
                measurements = []
                for _ in range(3):
                    metrics = {}
                    trace = (compiler.untargeted_unify(root, request, metrics=metrics, with_sound=False)
                        if mode == "untargeted" else compiler.certify(root, request, metrics=metrics))
                    measurements.append(metrics)
                row.update({key: statistics.median(m[key] for m in measurements)
                    for key in ("wall_ms", "rewrites", "maude_cpu_ms")})
                def count_rules(node):
                    return 1 + (count_rules(node["child"]) if "child" in node else 0) + \
                        sum(count_rules(child) for child in node.get("children", []) if child is not None)
                row.update(search_rule_nodes=count_rules(trace["proof"]),
                    answer_count=len(trace.get("generated", request["proposed"])), search_completed=True)
                if mode == "untargeted":
                    row["failure_phase"] = "soundness_evidence"
                    compiler.annotate_generated_sound(root, request, trace, metrics=row)
                row["total_rewrites"] = row["rewrites"] + row.get("sound_rewrites", 0)
                bundle = compiler.compile_bundle(trace)
                row.update(proof_nodes=len(bundle["steps"]), failure_phase="lean_check")
                start = time.monotonic()
                check_comparison_certificate(root, cache, request, trace, bundle)
                row.update(lean_ms=round((time.monotonic() - start) * 1000, 3), status="kernel_checked")
                del row["failure_phase"]
                print(f"  {row['total_rewrites']:,} total rewrites; {row['proof_nodes']} proof nodes; "
                    f"Maude wall {row['wall_ms']:.1f} ms; Lean wall {row['lean_ms']:.1f} ms; checked", flush=True)
            except (RuntimeError, ValueError, RecursionError) as error:
                # Preserve failure honestly; never call a capped run impossible.
                row.update(status="not_checked", error=str(error))
                if "stack overflow" in str(error):
                    detail = "Maude stack limit"
                elif "bad_alloc" in str(error):
                    detail = "memory-allocation failure under the safety caps"
                else:
                    detail = str(error).splitlines()[0]
                print("  Not checked (" + row["failure_phase"] + "): " + detail, flush=True)
            rows.append(row)
            (cache / "comparison.json").write_text(json.dumps(rows, indent=2) + "\n")
    print("Results: " + str(cache / "comparison.json"), flush=True)
    return rows

def negative_demo(root):
    """Run the SAME demo negative tests without all unrelated positive examples.

    Only an ignored test consumer is generated; there is no second maintained
    Lean test/implementation. Explicit markers keep its dependency prefix intact.
    This avoids spending one process's CPU budget on every regression twice.
    """
    import os
    cache = precompile(root)
    text = (root / "examples/certification-demo.lean").read_text()
    prefix_marker = "-- CERTIFICATION-NEGATIVE-PREFIX-END"
    tests_marker = "-- CERTIFICATION-NEGATIVE-TESTS-BEGIN"
    if text.count(prefix_marker) != 1 or text.count(tests_marker) != 1:
        raise ValueError("negative test source markers must occur exactly once")
    source = text.split(prefix_marker)[0] + text.split(tests_marker)[1]
    path = cache / "negatives.lean"
    path.write_text(source)
    env = dict(os.environ, CONPANNA_CERT_NEGATIVES="1")
    print("Checking focused negative tests under the unchanged limits", flush=True)
    checked = compiler.run_checked(["lake", "env", "lean", "-j1", "-M512",
        str(path)], cwd=root, lean=True, env=env)
    print(checked.rstrip())
    for label in ("wrong successor", "wrong scope", "wrong conditional hypothesis",
                  "proof hole", "duplicate node", "unsupported node kind",
                  "wrong final proof", "omitted support row", "identical heads",
                  "eligible supplier skipped"):
        if "Rejected " + label not in checked:
            raise ValueError("negative test did not run: " + label)


def demo(root):
    import os
    import time
    cache = precompile(root)
    if os.environ.get("CONPANNA_CERT_STRESS") == "1":
        # A separate consumer reuses the SAME producer/compiler/checker. Do not
        # cumulatively spend its CPU budget checking every other certificate first.
        print("Checking fixed balance problem/answer only; no native unify", flush=True)
        start = time.monotonic()
        checked = compiler.run_checked(["lake", "env", "lean", "-j1", "-M512",
            "examples/certification-balance.lean"], cwd=root, lean=True)
        print(checked.rstrip())
        print(f"Balance consumer: {time.monotonic() - start:.2f}s")
        print("CERTIFIED: soundness and completeness; no sorry")
        return
    start = time.monotonic()
    native = compiler.maude_run(root, "unify in BAKERY-DEMO-NATIVE : "
        "P:Bag =? Q:Bag /\\ Q:Bag =? singleton(wait(N:Ticket)) .",
        source=compiler.ENGINE_DIR / "examples/bakery.maude")
    answer = native_demo_answer(native)
    print("Native answer: (n, P, Q) := (N, [wait(N)], [wait(N)])")
    trace = compiler.certify(root, {"aggregate": "system", "problem": "bindSystem", "answers": "bindAnswers",
        "scope": [0, 2, 2], "eqs": [
            {"sort": 2, "left": {"var": 1}, "right": {"var": 2}},
            {"sort": 2, "left": {"var": 2}, "right": answer[1]}],
        "proposed": [{"parameters": [0], "images": answer}]})
    print(f"Legacy binding control trace: {trace['proof']['rule']} -> "
        f"{trace['proof']['child']['rule']} -> {trace['proof']['child']['child']['rule']}")
    (cache / "demo.trace.json").write_text(json.dumps(trace, indent=2) + "\n")
    proof_path = cache / "demo.proof.json"
    proof_path.write_text(json.dumps(compiler.compile_bundle(trace)) + "\n")
    print(f"Maude + Python: {time.monotonic() - start:.3f}s")
    start = time.monotonic()
    # Check THIS produced certificate, not a separately regenerated first proof.
    # The remaining examples still exercise the independent regression suite.
    env = dict(os.environ, CONPANNA_CERTIFICATE=str(proof_path))
    print("Checking supplied binding certificate plus the regression certificates", flush=True)
    checked = compiler.run_checked(["lake", "env", "lean", "-j1", "-M512",
        "examples/certification-demo.lean"], cwd=root, lean=True, env=env)
    print(checked.rstrip())
    print(f"Lean consumer: {time.monotonic() - start:.2f}s (no backend recompilation)")
    print("CERTIFIED: soundness and completeness; no sorry")
    print("Inspect: examples/certification-demo.lean; .lake/build/certification/demo.trace.json")

if __name__ == "__main__":
    if sys.argv[1:] == ["--build"]:
        precompile(ROOT)
    elif sys.argv[1:] == ["--negatives"]:
        negative_demo(ROOT)
    elif sys.argv[1:] == ["--demo"]:
        demo(ROOT)
    elif sys.argv[1:] == ["--compare"]:
        compare_search(ROOT)
    else:
        unittest.main()
