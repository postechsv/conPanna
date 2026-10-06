"""Untrusted rule-data compiler and Maude certificate producer wrapper.
The constructor translator does no unification, search, or Lean syntax evaluation.
--build caches general Lean proofs; --demo runs an explicit experimental pipeline.
Rule templates are restricted. Lean independently fixes and checks the goals.
Not a general ACU search engine or a production certificate loader.
--certify takes an EXISTING problem/answer family. It never invokes native unify
or Lean. Only --demo is a standalone test harness with an upstream native query.
"""
import json
import re
import sys

def number(x):
    if type(x) is not int or x < 0:
        raise ValueError("expected natural number")
    return str(x)

def scope(xs):
    return "[" + ", ".join("Tag.s" + number(x) for x in xs) + "]"

def position(x):
    x = int(number(x))
    return ".here" if x == 0 else "(.there " + position(x - 1) + ")"

def term(t, context=None):
    if context is not None and ACTIVE_COMPILER is not None:
        return ACTIVE_COMPILER.term(t, context)
    if "var" in t:
        return "(Term.var (sig := Sig) " + position(t["var"]) + ")"
    return "(Term.app (sig := Sig) Symbol.c" + number(t["app"]) + " " + terms(t["args"]) + ")"

def terms(ts, context=None):
    return ".nil" if not ts else "(.cons " + term(ts[0], context) + " " + terms(ts[1:], context) + ")"

def equations(es, context=None):
    return "[" + ", ".join("(equation (s := Tag.s" + number(e["sort"]) + ") "
        + term(e["left"], context) + " " + term(e["right"], context) + ")" for e in es) + "]"

def fin(x):
    return "⟨" + number(x) + ", of_decide_eq_true rfl⟩"

def finite_values(xs):
    if not xs:
        return "(fun (i : Fin 0) => Fin.elim0 i)"
    body = number(xs[-1])
    for index in reversed(range(len(xs) - 1)):
        body = "(if i = " + number(index) + " then " + number(xs[index]) + " else " + body + ")"
    if all(x == xs[0] for x in xs):
        body = number(xs[0])
    binder = "_" if all(x == xs[0] for x in xs) else "i"
    return "(fun (" + binder + " : Fin " + number(len(xs)) + ") => " + body + ")"

def finite_proofs(xs, argument=None):
    if not xs:
        return "(fun (i : Fin 0) => Fin.elim0 i)" if argument is None else "(Fin.elim0 " + argument + ")"
    applied = "" if argument is None else " " + argument
    return "(Fin.cases " + fact(xs[0]) + " (fun i => " + finite_proofs(xs[1:], "i") + ")" + applied + ")"

def finite_terms(xs):
    if not xs:
        return "(fun (i : Fin 0) => Fin.elim0 i)"
    body = term(xs[-1])
    for index in reversed(range(len(xs) - 1)):
        body = "(if i = " + number(index) + " then " + term(xs[index]) + " else " + body + ")"
    return "(fun (i : Fin " + number(len(xs)) + ") => " + body + ")"

def atom_children(coefficients, children, argument=None, expected=None, offset=0):
    if not coefficients:
        return "(fun (i : Fin 0) => Fin.elim0 i)" if argument is None else "(Fin.elim0 " + argument + ")"
    if coefficients[0] == 1:
        child = complete(children[0])
        if ACTIVE_COMPILER is not None and expected is not None:
            child = ACTIVE_COMPILER.successor(children[0], expected(offset), child, "atom")
        head = "(fun _ => " + child + ")"
    else:
        if children[0] is not None:
            raise ValueError("non-unit atom coefficient has a branch")
        head = "(fun impossible => False.elim ((of_decide_eq_true rfl : (" + number(coefficients[0]) + " : Nat) ≠ 1) impossible))"
    applied = "" if argument is None else " " + argument
    return "(Fin.cases " + head + " (fun i => " + atom_children(coefficients[1:], children[1:], "i", expected, offset + 1) + ")" + applied + ")"

def fact(f):
    if f == "rfl":
        return "rfl"
    if type(f) is dict and "or" in f and f["or"] in ("left", "right"):
        return "(Or.in" + ("l" if f["or"] == "left" else "r") + " rfl)"
    raise ValueError("unsupported finite fact")

def equality(e, context=None):
    if ACTIVE_COMPILER is not None:
        return ACTIVE_COMPILER.equality(e, context)
    return nested_equality(e, context)

def nested_equality(e, context=None):
    if e["rule"] == "scoped":
        return equality(e["child"], e["scope"])
    ctx = e.get("scope") if context is None else context
    if e["rule"] == "refl":
        return "(Equality.refl (sig := Sig) (Γ := " + scope(ctx) + ") " + term(e["term"], ctx) + ")"
    if e["rule"] == "symm":
        return "(Equality.symm (sig := Sig) (Γ := " + scope(ctx) + ") " + equality(e["child"], ctx) + ")"
    if e["rule"] == "trans":
        return "(Equality.trans (sig := Sig) (Γ := " + scope(ctx) + ") " + equality(e["left"], ctx) + " " + equality(e["right"], ctx) + ")"
    if e["rule"] == "congr":
        return "(Equality.congr (sig := Sig) (Γ := " + scope(ctx) + ") Symbol.c" + number(e["head"]) + " " + equalities(e["args"], ctx) + ")"
    if e["rule"] in ("unit", "comm", "assoc", "swap_right"):
        return "(Equality." + e["rule"] + " (sig := Sig) (Γ := " + scope(ctx) + ") Operator.acu " + \
            " ".join(term(x, ctx) for x in e["terms"]) + ")"
    raise ValueError("unsupported equality rule")

def equalities(es, context):
    return ".nil" if not es else "(.cons " + equality(es[0], context) + " " + equalities(es[1:], context) + ")"

def derives(d, context=None):
    if d["rule"] == "hyp":
        return "(.hyp " + fin(d["index"]) + ")"
    if d["rule"] == "axiom":
        return "(Derives.axiom (sig := Sig) (Γ := " + scope(context) + ") " + equality(d["equality"], context) + ")"
    if d["rule"] == "symm":
        return "(Derives.symm (sig := Sig) (Γ := " + scope(context) + ") " + derives(d["child"], context) + ")"
    if d["rule"] == "decompose":
        return "(.decompose Symbol.c" + number(d["head"]) + " rfl " + terms(d["leftArgs"], context) + \
            " " + terms(d["rightArgs"], context) + " " + position(d["field"]) + " " + derives(d["child"], context) + ")"
    if d["rule"] == "congr":
        return "(Derives.congr (sig := Sig) (Γ := " + scope(context) + ") Symbol.c" + \
            number(d["head"]) + " " + derives_args(d["args"], context) + ")"
    if d["rule"] == "multiplicity":
        return "(Derives.multiplicity (sig := Sig) (Γ := " + scope(context) + ") Operator.acu " + \
            number(d["count"]) + " (of_decide_eq_true rfl) " + term(d["left"], context) + \
            " " + term(d["right"], context) + " " + derives(d["child"], context) + ")"
    if d["rule"] == "trans":
        return "(Derives.trans (sig := Sig) (Γ := " + scope(context) + ") " + derives(d["left"], context) + " " + derives(d["right"], context) + ")"
    if d["rule"] == "cancel":
        return "(Derives.cancel (sig := Sig) (Γ := " + scope(context) + ") Operator.acu " + term(d["common"], context) + " " + term(d["left"], context) + " " + \
            term(d["right"], context) + " " + derives(d["child"], context) + ")"
    raise ValueError("unsupported derivation rule")

def derives_args(ds, context):
    return ".nil" if not ds else "(.cons " + derives(ds[0], context) + " " + derives_args(ds[1:], context) + ")"

def occurs_path(p, *, proper=False):
    if p["rule"] == "root" and not proper:
        return ".root"
    if p["rule"] == "field":
        return "(.field Symbol.c" + number(p["head"]) + " rfl " + terms(p["args"]) + " " + \
            position(p["field"]) + " " + occurs_path(p["child"]) + ")"
    raise ValueError("invalid free-occurs path")

def slots(xs):
    return ".nil" if not xs else "(." + ("take" if xs[0] else "skip") + " " + slots(xs[1:]) + ")"

def checked_table(xs):
    if not xs:
        return "rfl"
    return "(congr (congrArg List.cons (funext " + finite_proofs(["rfl"] * len(xs[0])) + ")) " + checked_table(xs[1:]) + ")"

def sharing_fields(p, sound=False):
    counts = p["counts"]
    left, right = p["left"], p["right"]
    disjoint = [{"or": "left" if a == 0 else "right"} for a, b in zip(left, right)]
    if not all(a == 0 or b == 0 for a, b in zip(left, right)):
        raise ValueError("non-disjoint sharing")
    context_arg = "inputs" if sound else "Γ"
    return "(sig := Sig) (s := Tag.s" + number(p["sort"]) + ") (" + context_arg + " := " + scope(p["scope"]) + ") " +         "(n := " + number(len(left)) + ") (rows := " + number(len(p["rows"])) + ") (cols := " + number(len(p["cols"])) + ") " +         ("profile " if sound else "") + "Operator.acu " + slots(p["slots"]) + " " +         finite_values(left) + " " + finite_values(right) + " " + finite_values(p["rows"]) + " " + finite_values(p["cols"]) + " " +         finite_proofs(counts[0]) + " " + finite_proofs(counts[1]) + " " + finite_proofs(disjoint)

def complete(p):
    body = nested_complete(p)
    if ACTIVE_COMPILER is not None:
        return ACTIVE_COMPILER.completeness(p, body)
    return body

def nested_complete(p):
    if ACTIVE_COMPILER is not None:
        images, eqs = ACTIVE_COMPILER.state(p)
    else:
        images = terms(p["images"], p["scope"])
        eqs = equations(p["eqs"], p["scope"]) if "eqs" in p else None
    common = "" if p["rule"] in ("sharing", "purify") else "(Γ := " + scope(p["scope"]) + ") (images := " + images + ") (eqs := " + eqs + ") "
    if p["rule"] == "bind":
        removal = "(" + position(p["remove"]) + " : Binding.Removal Tag.s" + number(p["sort"]) +             " " + scope(p["scope"]) + " " + scope(p["after"]) + ")"
        replacement = term(p["replacement"], p["after"])
        child = complete(p["child"])
        if ACTIVE_COMPILER is not None:
            source = ACTIVE_COMPILER.snapshot(p)
            expected = "(ReplayState.substitute " + source + " (Binding.Removal.substitution " + removal + " " + replacement + "))"
            child = ACTIVE_COMPILER.successor(p["child"], expected, child, "bind")
        return "(.bind (sig := Sig) " + common + "(Δ := " + scope(p["after"]) + ") " + removal + " " + replacement + " " + derives(p["premise"], p["scope"]) + " " + child + ")"
    if p["rule"] == "cover":
        return "(.cover (sig := Sig) " + common + fin(p["index"]) + " " + terms(p["beta"]) + " " + derives_args(p["derived"], p["scope"]) + ")"
    if p["rule"] == "sharing":
        state = "(images := " + images + ") (eqs := " + eqs + ") " if "images" in p else ""
        child = complete(p["child"])
        table = "[" + ", ".join(finite_values(x) for x in p["generators"]) + "]" if "generators" in p else \
            "(FiniteSharing.supportGenerators " + finite_values(p["rows"]) + " " + finite_values(p["cols"]) + ")"
        if ACTIVE_COMPILER is not None:
            bindings = "(Sharing.substitution (sig := Sig) Operator.acu " + slots(p["slots"]) + " " + finite_values(p["left"]) + " " + finite_values(p["right"]) + " " + table + ")"
            expected = "(ReplayState.substitute " + ACTIVE_COMPILER.snapshot(p) + " " + bindings + ")"
            child = ACTIVE_COMPILER.successor(p["child"], expected, child, "sharing")
        if "generators" in p:
            return "(Complete.sharingTable " + state + sharing_fields(p) + " " + derives(p["premise"], p["scope"]) + \
                " " + table + " " + checked_table(p["generators"]) + " " + child + ")"
        return "(.sharing " + state + sharing_fields(p) + " " + derives(p["premise"], p["scope"]) + " " + child + ")"
    if p["rule"] == "clash":
        f, g = "Symbol.c" + number(p["leftHead"]), "Symbol.c" + number(p["rightHead"])
        different = "(fun same => (of_decide_eq_true rfl : profile.code " + f + " ≠ profile.code " + g + \
            ") (congrArg (fun x => profile.code x.2) same))"
        return "(.clash (sig := Sig) " + common + "Symbol.c" + number(p["leftHead"]) + \
            " Symbol.c" + number(p["rightHead"]) + " rfl rfl " + different + " " + \
            terms(p["leftArgs"]) + " " + terms(p["rightArgs"]) + " " + derives(p["premise"], p["scope"]) + ")"
    if p["rule"] == "occurs":
        return "(.occurs (sig := Sig) " + common + position(p["variable"]) + " " + term(p["rhs"]) + \
            " " + occurs_path(p["path"], proper=True) + " " + derives(p["premise"], p["scope"]) + ")"
    if p["rule"] in ("atom", "zero"):
        vector = "(" + finite_terms(p["terms"]) + " : Fin " + number(len(p["terms"])) + \
            " → Term Sig " + scope(p["scope"]) + " Tag.s" + number(p["sort"]) + ")"
        prefix = "(." + p["rule"] + " (sig := Sig) " + common + "Operator.acu " + \
            finite_values(p["coefficients"]) + " " + vector + " "
        if p["rule"] == "zero":
            child = complete(p["child"])
            if ACTIVE_COMPILER is not None:
                expected = "(ReplayState.prepend " + ACTIVE_COMPILER.snapshot(p) + " (zeroRequirements (sig := Sig) Operator.acu " + finite_values(p["coefficients"]) + " " + vector + "))"
                child = ACTIVE_COMPILER.successor(p["child"], expected, child, "zero")
            return prefix + derives(p["premise"], p["scope"]) + " " + child + ")"
        expected = None
        if ACTIVE_COMPILER is not None:
            source = ACTIVE_COMPILER.snapshot(p)
            atom = "(Term.app (sig := Sig) Symbol.c" + number(p["head"]) + " " + terms(p["args"], p["scope"]) + ")"
            expected = lambda j: "(ReplayState.prepend " + source + " (atomRequirements (sig := Sig) Operator.acu " + finite_values(p["coefficients"]) + " " + vector + " " + atom + " " + fin(j) + "))"
        return prefix + "Symbol.c" + number(p["head"]) + " rfl " + terms(p["args"]) + " " + \
            derives(p["premise"], p["scope"]) + " " + atom_children(p["coefficients"], p["children"], expected=expected) + ")"
    if p["rule"] == "nonempty":
        return "(.nonempty (sig := Sig) " + common + "Operator.acu Symbol.c" + number(p["head"]) + \
            " rfl " + terms(p["args"]) + " " + derives(p["premise"], p["scope"]) + ")"
    if p["rule"] == "purify":
        template = equations([p["template"]], [p["sort"]] + p["scope"])[1:-1]
        child = complete(p["child"])
        if ACTIVE_COMPILER is not None:
            rest = "(" + equations(p["before"], p["scope"]) + " ++ " + equations(p["after"], p["scope"]) + ")"
            expected = "(ReplayState.purify " + ACTIVE_COMPILER.snapshot(p) + " " + term(p["term"], p["scope"]) + " " + template + " " + rest + ")"
            child = ACTIVE_COMPILER.successor(p["child"], expected, child, "purify")
        return "(.purify (sig := Sig) (Γ := " + scope(p["scope"]) + ") (images := " + images + ") " + \
            term(p["term"], p["scope"]) + " " + template + " " + equations(p["before"], p["scope"]) + " " + equations(p["after"], p["scope"]) + \
            " " + child + ")"
    raise ValueError("unsupported complete rule")

def sound_row(es):
    return ".nil" if not es else "(.cons " + equality(es[0]) + " " + sound_row(es[1:]) + ")"

def system_sound(rows):
    return ".nil" if not rows else "(.cons " + sound_row(rows[0]) + " " + system_sound(rows[1:]) + ")"

def declaration(name):
    if type(name) is not str or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", name) is None:
        raise ValueError("invalid declaration identifier")
    return name

# Each exported equality node has determined endpoints. Computing those endpoints
# is syntax-directed proof assembly, NOT equality testing or unification search.
# Explicit local types avoid one giant metavariable problem in Lean. Identical
# rule subtrees are shared; the final proof is still the same small rule calculus.
ACTIVE_COMPILER = None

class ExplicitCompiler:
    def __init__(self, signature, inputs, proposed):
        self.inputs = inputs
        self.proposed = proposed
        self.zero = next(h["id"] for h in signature if h["role"] == "zero")
        self.add = next(h["id"] for h in signature if h["role"] == "add")
        self.records, self.memo = [], {}
        self.next_equality = 0
        self.data_memo = {}
        self.heads = {h["id"]: h for h in signature}
        self.term_memo = {}

    def term(self, t, context):
        """Share typed constructor DATA, without computing modulo equality.

        Context and sort are explicit so Lean need not recover them repeatedly
        from a dependent proof's endpoints. Every definition is kernel checked.
        """
        key = json.dumps([context, t], sort_keys=True)
        if key not in self.term_memo:
            if "var" in t:
                index = t["var"]
                number(index)
                if index >= len(context):
                    raise ValueError("term variable outside exported scope")
                sort = context[index]
                body = "(Term.var (sig := Sig) (Γ := " + scope(context) + ") " + position(index) + ")"
            else:
                head = self.heads[t["app"]]
                if len(t["args"]) != len(head["inputs"]):
                    raise ValueError("term constructor arity mismatch")
                sort = head["output"]
                body = "(Term.app (sig := Sig) (Γ := " + scope(context) + ") Symbol.c" + number(t["app"]) + " " + terms(t["args"], context) + ")"
            self.term_memo[key] = self.data("Term Sig " + scope(context) + " Tag.s" + number(sort), body)
        return self.term_memo[key]

    def completeness(self, p, body):
        """Name a closed replay node, keeping the original indexed rule type."""
        expected = "ReplayState.Certified profile " + self.proposed + " " + self.snapshot(p)
        name = "cert_complete_" + str(len(self.records))
        self.records.append({"name": name, "type": expected, "value": body, "rule": p["rule"]})
        return name

    def plus(self, a, b):
        return {"app": self.add, "args": [a, b]}

    def data(self, expected, body):
        key = (expected, body)
        if key not in self.data_memo:
            name = "cert_state_" + str(len(self.records))
            self.records.append({"name": name, "type": expected, "value": body, "kind": "data"})
            self.data_memo[key] = name
        return self.data_memo[key]

    def state(self, p):
        state = self.snapshot(p)
        # Keep the generated identifier separate from the projection. Lean's
        # syntax renamer sees `name.images` as ONE name, not a field application.
        return "(ReplayState.images " + state + ")", "(ReplayState.equations " + state + ")"

    def snapshot(self, p):
        """Typed before/after DATA. Substitution is computed and checked by Lean.

        PURIFY supplies a template instead of redundant source equations; the
        original equation is reconstructed with the existing Lean source function.
        No variable shifting or semantic computation is duplicated in Python.
        """
        context = scope(p["scope"])
        images = self.data("Terms Sig " + context + " " + scope(self.inputs), terms(p["images"], p["scope"]))
        if "eqs" in p:
            eqs = equations(p["eqs"], p["scope"])
        elif p["rule"] == "purify":
            template = equations([p["template"]], [p["sort"]] + p["scope"])[1:-1]
            eqs = "(" + equations(p["before"], p["scope"]) + " ++ Purification.source " + term(p["term"], p["scope"]) + " " + template + " :: " + equations(p["after"], p["scope"]) + ")"
        else:
            raise ValueError("replay state lacks equations")
        eqs = self.data("List (Problem Sig " + context + ")", eqs)
        return self.data("ReplayState Sig " + scope(self.inputs) + " " + context,
            "⟨" + images + ", " + eqs + "⟩")

    def successor(self, p, expected, child, rule):
        """Check one exact transition, then reuse the opaque child certificate.

        rfl asks Lean to compute the rule's syntactic transformation. A corrupted
        successor cannot pass; this is not an assumed producer-correctness lemma.
        """
        actual = self.snapshot(p)
        name = "cert_transition_" + str(len(self.records))
        self.records.append({"name": name, "type": expected + " = " + actual,
            "value": "rfl", "rule": rule + "_successor"})
        return "(ReplayState.accept " + expected + " " + actual + " " + name + " " + child + ")"

    def equality(self, e, context):
        if e["rule"] == "scoped":
            return self.equality(e["child"], e["scope"])
        context = e.get("scope") if context is None else context
        key = json.dumps([context, e], sort_keys=True)
        if key in self.memo:
            return self.memo[key][0]
        rule = e["rule"]
        child = lambda x: self.equality(x, context)
        endpoints = lambda x: self.memo[json.dumps([context, x], sort_keys=True)][1:]
        if rule == "refl":
            lhs = rhs = e["term"]
        elif rule in ("symm", "trans"):
            if rule == "symm":
                child(e["child"])
                rhs, lhs = endpoints(e["child"])
            else:
                child(e["left"]); child(e["right"])
                lhs, middle = endpoints(e["left"])
                other, rhs = endpoints(e["right"])
                if middle != other:
                    raise ValueError("equality trace has inconsistent transitivity endpoints")
                # Remove identity compositions by SYNTACTIC endpoint equality,
                # not ACU reasoning. The retained ordinary proof is still checked.
                if lhs == middle or middle == rhs:
                    retained = e["right"] if lhs == middle else e["left"]
                    name = child(retained)
                    self.memo[key] = (name, lhs, rhs)
                    return name
        elif rule == "congr":
            for a in e["args"]:
                child(a)
            lhs = {"app": e["head"], "args": [endpoints(a)[0] for a in e["args"]]}
            rhs = {"app": e["head"], "args": [endpoints(a)[1] for a in e["args"]]}
        elif rule == "unit":
            rhs = e["terms"][0]
            lhs = self.plus({"app": self.zero, "args": []}, rhs)
        elif rule == "comm":
            a, b = e["terms"]
            lhs, rhs = self.plus(a, b), self.plus(b, a)
        elif rule == "assoc":
            a, b, c = e["terms"]
            lhs, rhs = self.plus(self.plus(a, b), c), self.plus(a, self.plus(b, c))
        elif rule == "swap_right":
            a, b, c = e["terms"]
            lhs, rhs = self.plus(a, self.plus(b, c)), self.plus(b, self.plus(a, c))
        else:
            raise ValueError("unsupported explicit equality rule")
        body = nested_equality({"rule": "refl", "term": lhs}, context) if lhs == rhs else nested_equality(e, context)
        name = "cert_eq_" + str(self.next_equality)
        self.next_equality += 1
        expected = "Equality Sig " + scope(context) + " " + term(lhs, context) + " " + term(rhs, context)
        self.records.append({"name": name, "type": expected, "value": body})
        self.memo[key] = (name, lhs, rhs)
        return name

def sound(p):
    if p["rule"] == "sharing":
        return "(.sharing " + sharing_fields(p, True) + " .nil)"
    if p["rule"] == "equalities":
        return sound_row(p["equalities"])
    raise ValueError("unsupported soundness rule")

def compile_components(p):
    # These identifiers select DATA, not supporting certification lemmas.
    # The Lean consumer fixes its expected proposition independently of them.
    aggregate = {"system": "exact_system", "equation": "exact"}[p["aggregate"]]
    problem, answers = declaration(p["problem"]), declaration(p["answers"])
    global ACTIVE_COMPILER
    compiler = ExplicitCompiler(p["signature"], p["proof"]["scope"], answers) if p.get("signature") else None
    ACTIVE_COMPILER = compiler
    try:
        completeness = complete(p["proof"])
        sound_proof = system_sound(p["sound"]) if p["aggregate"] == "system" else sound(p["sound"])
        body = "Worklist." + aggregate + " registration (profile := profile) " + problem + " " + answers + \
            "\n  " + completeness + "\n  " + sound_proof
        if compiler is None:
            return [], body
        # Retain only nodes referenced by the aggregate, recursively. Discarded
        # identity subproofs must not cost another kernel declaration.
        wanted = set(re.findall(r"\bcert_(?:eq|state|complete|transition)_\d+\b", body))
        retained = []
        for record in reversed(compiler.records):
            if record["name"] in wanted:
                retained.append(record)
                wanted.update(re.findall(r"\bcert_(?:eq|state|complete|transition)_\d+\b", record["type"] + record["value"]))
        return list(reversed(retained)), body
    finally:
        ACTIVE_COMPILER = None

def compile_proof(p):
    steps, body = compile_components(p)
    return "".join("let " + s["name"] + " : " + s["type"] + " := " + s["value"] + "\n" for s in steps) + body

def compile_bundle(p):
    """Finite local proof DAG. Lean checks each ordinary rule application once.
    No user theorem/axiom is supplied by Python; step names are freshly renamed
    by Lean, and the independently fixed final goal is still checked there.
    """
    steps, body = compile_components(p)
    return {"format": "rule-bundle-v1", "steps": steps, "proof": body}

def run_checked(command, *, cwd, input_text=None, lean=False, allow_stale=False, env=None):
    """One child at a time. Never raise Lean limits to obtain a successful demo."""
    import subprocess
    import resource
    import os
    import signal
    import time
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (25, 25))
        if lean:
            resource.setrlimit(resource.RLIMIT_DATA, (768 * 1024**2, 768 * 1024**2))
    started = time.monotonic()
    child = subprocess.Popen(command, cwd=cwd, text=True, stdin=subprocess.PIPE,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=limits,
        start_new_session=True, env=env)
    try:
        output, errors = child.communicate(input_text, timeout=30)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        output, errors = child.communicate()
        raise RuntimeError("subprocess exceeded the 30s safety limit\n" + output + errors) from None
    messages = output + errors
    if allow_stale and child.returncode == 3:  # Lake's documented --no-build exit.
        return None
    if child.returncode or "Warning:" in messages or (lean and "sorryAx" in messages):
        status = (f"signal {signal.Signals(-child.returncode).name}"
                  if child.returncode < 0 else f"exit {child.returncode}")
        raise RuntimeError(f"subprocess failed ({status}, {time.monotonic() - started:.2f}s)\n" + messages)
    return messages

def precompile(root):
    """Cache the unchanged general proofs, not the problem certificate."""
    import time
    cache = root / ".lake/build/certification"
    cache.mkdir(parents=True, exist_ok=True)
    # Let Lake validate dependency traces; do not implement a second build cache.
    ready = run_checked(["lake", "--no-build", "--no-cache", "build",
        "+conPanna.Certification.Replay:olean"], cwd=root, lean=True, allow_stale=True)
    if ready is not None:
        print("Certification backend: cached (Lake validated dependencies)", flush=True)
        return cache
    # Existing project dependencies must already be built (as in normal Lake use).
    # Explicit steps prevent independent backend modules compiling concurrently.
    for name in ("Core", "Sharing", "Enumeration", "Frontend", "Replay"):
        start = time.monotonic()
        # Lake creates .ilean and dependency traces needed by the editor.
        # --old avoids unrelated transitive rebuilds in this experiment.
        # The Certification library itself fixes -j1 -M512 in lakefile.toml.
        run_checked(["lake", "--old", "--no-cache", "build",
            f"+conPanna.Certification.{name}:olean"], cwd=root, lean=True)
        print(f"{name}: ready in {time.monotonic() - start:.2f}s", flush=True)
    return cache

def maude_run(root, commands, *, source="certification.maude"):
    import os
    import shutil
    executable = os.environ.get("CONPANNA_MAUDE") or shutil.which("maude")
    if not executable:
        raise RuntimeError("Set CONPANNA_MAUDE or put maude on PATH")
    return run_checked([executable, "-no-banner", "-no-advise", "-no-wrap",
        str(root / source)], cwd=root,
        input_text=commands + "\nquit\n")

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

def maude_term(t):
    if "var" in t:
        return "v(" + number(t["var"]) + ")"
    return "a(" + number(t["app"]) + "," + maude_terms(t["args"]) + ")"

def maude_terms(ts):
    return "nilT" if not ts else "t(" + maude_term(ts[0]) + "," + maude_terms(ts[1:]) + ")"

def maude_context(xs):
    return "nilC" if not xs else "c(" + number(xs[0]) + "," + maude_context(xs[1:]) + ")"

def maude_equations(es):
    if not es:
        return "nilE"
    e = es[0]
    return "e(eqn(" + number(e["sort"]) + "," + maude_term(e["left"]) + "," + \
        maude_term(e["right"]) + ")," + maude_equations(es[1:]) + ")"

def maude_heads(hs):
    if not hs:
        return "nilH"
    h = hs[0]
    if h["role"] not in ("free", "zero", "add"):
        raise ValueError("unknown constructor role")
    return "head(" + number(h["id"]) + "," + number(h["output"]) + "," + \
        maude_context(h["inputs"]) + "," + json.dumps(h["role"]) + "," + maude_heads(hs[1:]) + ")"

def maude_answers(xs):
    return "nilA" if not xs else "answer(" + maude_context(xs[0]["parameters"]) + "," + \
        maude_terms(xs[0]["images"]) + "," + maude_answers(xs[1:]) + ")"

def validate_request(request):
    """Fail early on malformed sorted DATA; never change E or the fixed Sigma.

    Native answers must lose unused parameters BEFORE the semantic goal is fixed.
    Removing an unused existential afterwards is not valid for an empty sort.
    Generated Lean profiles enforce this signature contract too; these checks
    make wrapper failures readable and prevent malformed data reaching Maude.
    The signature-less historical test format is retained, not certified here.
    """
    signature = request.get("signature")
    if not signature:
        return
    heads = {}
    for h in signature:
        number(h["id"]); number(h["output"])
        for s in h["inputs"]:
            number(s)
        if h["id"] in heads:
            raise ValueError("duplicate constructor code in signature")
        if h["role"] not in ("free", "zero", "add"):
            raise ValueError("unsupported constructor role")
        heads[h["id"]] = h
    zeros = [h for h in signature if h["role"] == "zero"]
    adds = [h for h in signature if h["role"] == "add"]
    if len(zeros) != 1 or len(adds) != 1:
        raise ValueError("certification contract requires exactly one ACU operator and unit")
    bag = adds[0]["output"]
    if zeros[0]["output"] != bag or zeros[0]["inputs"] or adds[0]["inputs"] != [bag, bag]:
        raise ValueError("ACU operator/unit have incompatible sorts or arities")
    atoms = [h for h in signature if h["output"] == bag and h["role"] == "free"]
    if len(atoms) != 1 or len(atoms[0]["inputs"]) != 1:
        raise ValueError("bag sort requires exactly one unary singleton constructor")
    blocked = {bag}
    while True:
        grown = blocked | {h["output"] for h in signature if blocked.intersection(h["inputs"])}
        if grown == blocked:
            break
        blocked = grown
    if atoms[0]["inputs"][0] in blocked:
        raise ValueError("singleton payload may not contain the bag sort")

    def sorted_term(t, context, expected, used):
        if type(t) is not dict:
            raise ValueError("expected constructor term data")
        if set(t) == {"var"}:
            index = t["var"]
            number(index)
            if index >= len(context):
                raise ValueError("term variable outside exported scope")
            if context[index] != expected:
                raise ValueError("term variable has the wrong sort")
            used.add(index)
            return
        if set(t) != {"app", "args"}:
            raise ValueError("unsupported term data")
        number(t["app"])
        h = heads.get(t["app"])
        if h is None:
            raise ValueError("unknown constructor code")
        if h["output"] != expected:
            raise ValueError("constructor term has the wrong sort")
        if type(t["args"]) is not list or len(t["args"]) != len(h["inputs"]):
            raise ValueError("term constructor arity mismatch")
        for arg, sort in zip(t["args"], h["inputs"]):
            sorted_term(arg, context, sort, used)

    inputs = request["scope"]
    for s in inputs:
        number(s)
    for e in request["eqs"]:
        number(e["sort"])
        sorted_term(e["left"], inputs, e["sort"], set())
        sorted_term(e["right"], inputs, e["sort"], set())
    for answer in request["proposed"]:
        parameters = answer["parameters"]
        for s in parameters:
            number(s)
        if len(answer["images"]) != len(inputs):
            raise ValueError("answer must contain every original input image")
        used = set()
        for image, sort in zip(answer["images"], inputs):
            sorted_term(image, parameters, sort, used)
        if used != set(range(len(parameters))):
            raise ValueError("normalize unused answer parameters before fixing the semantic certificate goal")

def certify(root, request):
    """Fixed E/B/Sigma in; rule evidence out. No new answer or verifier process.

    The producer executes free, singleton/zero, purification, sharing, and
    whole-vector factor rules. It fails closed when evidence cannot be completed.
    The unbounded scheduling argument is documented in CERTIFICATION.md §7.4;
    it is an informal audit, not a formal search theorem or a safety-cap guarantee.
    Lean independently checks the whole original request, not this shape test.
    """
    if request["aggregate"] != "system":
        raise ValueError("producer currently accepts equation systems")
    validate_request(request)
    problem, answers = declaration(request["problem"]), declaration(request["answers"])
    proposed = request["proposed"]
    scope = request["scope"]
    command = "rew in CERTIFICATION-PRODUCER : certify(" + maude_heads(request.get("signature") or []) + "," + maude_context(scope) + "," + \
        maude_terms([{"var": i} for i in range(len(scope))]) + "," + \
        maude_equations(request["eqs"]) + "," + maude_answers(proposed) + ") ."
    emitted = maude_run(root, command)
    match = re.search(r'result State: result\(("(?:[^"\\]|\\.)*")\)', emitted)
    if not match:
        raise ValueError("certifier could not close the supplied answer family (unsupported or incorrect); no proof returned")
    trace = json.loads(json.loads(match.group(1)))
    trace.update(aggregate="system", problem=problem, answers=answers, signature=request.get("signature"))
    return trace

def demo(root):
    import os
    import time
    cache = precompile(root)
    if os.environ.get("CONPANNA_CERT_STRESS") == "1":
        # A separate consumer reuses the SAME producer/compiler/checker. Do not
        # cumulatively spend its CPU budget checking every other certificate first.
        print("Checking fixed balance problem/answer only; no native unify", flush=True)
        start = time.monotonic()
        checked = run_checked(["lake", "env", "lean", "-j1", "-M512",
            "examples/certification-balance.lean"], cwd=root, lean=True)
        print(checked.rstrip())
        print(f"Balance consumer: {time.monotonic() - start:.2f}s")
        print("CERTIFIED: soundness and completeness; no sorry")
        return
    start = time.monotonic()
    native = maude_run(root, "unify in BAKERY-DEMO-NATIVE : "
        "P:Bag =? Q:Bag /\\ Q:Bag =? singleton(wait(N:Ticket)) .",
        source="examples/certification-demo.maude")
    answer = native_demo_answer(native)
    print("Native answer: (n, P, Q) := (N, [wait(N)], [wait(N)])")
    trace = certify(root, {"aggregate": "system", "problem": "bindSystem", "answers": "bindAnswers",
        "scope": [0, 2, 2], "eqs": [
            {"sort": 2, "left": {"var": 1}, "right": {"var": 2}},
            {"sort": 2, "left": {"var": 2}, "right": answer[1]}],
        "proposed": [{"parameters": [0], "images": answer}]})
    print(f"Legacy binding control trace: {trace['proof']['rule']} -> "
        f"{trace['proof']['child']['rule']} -> {trace['proof']['child']['child']['rule']}")
    (cache / "demo.trace.json").write_text(json.dumps(trace, indent=2) + "\n")
    proof_path = cache / "demo.proof.json"
    proof_path.write_text(json.dumps(compile_bundle(trace)) + "\n")
    print(f"Maude + Python: {time.monotonic() - start:.3f}s")
    start = time.monotonic()
    # Check THIS produced certificate, not a separately regenerated first proof.
    # The remaining examples still exercise the independent regression suite.
    env = dict(os.environ, CONPANNA_CERTIFICATE=str(proof_path))
    print("Checking supplied binding certificate plus the regression certificates", flush=True)
    checked = run_checked(["lake", "env", "lean", "-j1", "-M512",
        "examples/certification-demo.lean"], cwd=root, lean=True, env=env)
    print(checked.rstrip())
    print(f"Lean consumer: {time.monotonic() - start:.2f}s (no backend recompilation)")
    print("CERTIFIED: soundness and completeness; no sorry")
    print("Inspect: examples/certification-demo.lean; .lake/build/certification/demo.trace.json")

def main():
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="precompile the general certificate library")
    parser.add_argument("--demo", action="store_true", help="run Maude -> Python -> Lean end to end")
    parser.add_argument("--certify", action="store_true", help="certify supplied answers; output proof only; never run unify or Lean")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if args.certify:
        print(json.dumps(compile_bundle(certify(root, json.load(sys.stdin)))))
    elif args.demo:
        demo(root)
    elif args.build:
        precompile(root)
    else:
        print(compile_proof(json.load(sys.stdin)))

if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError) as error:
        sys.exit(str(error))
