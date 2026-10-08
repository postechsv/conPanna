"""Standalone, untrusted constructor-unification certification coordinator.
Supply --ctor FILE --unify 'unify in MODULE : ... =? ... .' to run the engine.
Signature/variables are inferred; intermediate files go to this engine's .cache.
The constructor translator does no unification, search, or Lean syntax evaluation.
This engine assembles proof syntax but never launches Lean.
Rule templates are restricted. Lean independently fixes and checks the goals.
Not a general ACU search engine or a production certificate loader.
--certify takes an EXISTING problem/answer family. It never invokes native unify
or Lean. --coordinate obtains native answers first, then calls that same fixed-
answer certifier. Its stages can be run separately and inspected with --out.
Lean kernel checks and comparisons live in the separate test harness.
"""
import json
import re
import sys
from pathlib import Path

ENGINE_DIR = Path(__file__).resolve().parent

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
    if p["rule"] == "mutate":
        if len(p["terms"]) != 4:
            raise ValueError("mutation requires exactly four terms")
        parts = " ".join(term(x, p["scope"]) for x in p["terms"])
        child = complete(p["child"])
        if ACTIVE_COMPILER is not None:
            lifted = "(lift4 (sig := Sig) (Γ := " + scope(p["scope"]) + ") (s := Tag.s" + number(p["sort"]) + "))"
            expected = "(⟨Terms.subst " + images + " " + lifted + ", mutated (sig := Sig) Operator.acu " + parts + " " + eqs + "⟩ : ReplayState Sig " + scope(ACTIVE_COMPILER.inputs) + " " + scope([p["sort"]] * 4 + p["scope"]) + ")"
            child = ACTIVE_COMPILER.successor(p["child"], expected, child, "mutate")
        return "(.mutate (sig := Sig) " + common + "Operator.acu " + parts + " " + derives(p["premise"], p["scope"]) + " " + child + ")"
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

def run_checked(command, *, cwd, input_text=None, lean=False, allow_stale=False, env=None,
                bounded_memory=False):
    """One child at a time. Never raise Lean limits to obtain a successful demo."""
    import subprocess
    import resource
    import os
    import signal
    import time
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (25, 25))
        if lean or bounded_memory:
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


def maude_run(root, commands, *, source=None):
    import os
    import shutil
    executable = os.environ.get("CONPANNA_MAUDE") or shutil.which("maude")
    if not executable:
        raise RuntimeError("Set CONPANNA_MAUDE or put maude on PATH")
    source = ENGINE_DIR / "certification.maude" if source is None else root / source
    return run_checked([executable, "-no-banner", "-no-advise", "-no-wrap",
        str(source)], cwd=root,
        input_text=commands + "\nquit\n", bounded_memory=True)


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

def certification_query(request, module="CERTIFICATION-PRODUCER"):
    """The SAME fixed-answer command for standalone and coordinated requests."""
    arguments = maude_heads(request.get("signature") or []) + "," + maude_context(request["scope"]) + "," + \
        maude_terms([{"var": i} for i in range(len(request["scope"]))]) + "," + maude_equations(request["eqs"])
    return "rew in " + module + " : certify(" + arguments + "," + maude_answers(request["proposed"]) + ") ."

def parse_certificate_output(emitted, request):
    if "Warning:" in emitted:
        raise ValueError("Maude reported a warning; no certificate accepted")
    match = re.search(r'result State: result\(("(?:[^"\\]|\\.)*")\)', emitted)
    if not match:
        raise ValueError("certifier could not close the supplied answer family (unsupported or incorrect); no proof returned")
    trace = json.loads(json.loads(match.group(1)))
    trace.update(aggregate="system", problem=declaration(request["problem"]),
        answers=declaration(request["answers"]), signature=request.get("signature"))
    return trace

def producer_result(root, request, *, untargeted=False, metrics=None):
    """Shared driver; the diagnostic untargeted entry point receives NO Sigma."""
    import time
    problem, answers = declaration(request["problem"]), declaration(request["answers"])
    scope = request["scope"]
    arguments = maude_heads(request.get("signature") or []) + "," + maude_context(scope) + "," + \
        maude_terms([{"var": i} for i in range(len(scope))]) + "," + maude_equations(request["eqs"])
    if untargeted:
        command = "rew in CERTIFICATION-PRODUCER : unifyWithoutAnswers(" + arguments + ") ."
    else:
        command = certification_query(request)
    start = time.monotonic()
    emitted = maude_run(root, command)
    elapsed = time.monotonic() - start
    trace = parse_certificate_output(emitted, request)
    if metrics is not None:
        stats = re.search(r'rewrites: (\d+) in (\d+)ms cpu', emitted)
        metrics.update(wall_ms=round(elapsed * 1000, 3),
            rewrites=int(stats.group(1)) if stats else None,
            maude_cpu_ms=int(stats.group(2)) if stats else None)
    return trace

def certify(root, request, *, metrics=None):
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
    return producer_result(root, request, metrics=metrics)

def annotate_generated_sound(root, request, trace, *, metrics=None):
    """No search: ask Maude to format equality evidence for the GENERATED CSU."""
    import time
    command = "rew in CERTIFICATION-PRODUCER : soundEvidence(" + maude_heads(request["signature"]) + "," + \
        maude_equations(request["eqs"]) + "," + maude_answers(trace["generated"]) + ") ."
    start = time.monotonic()
    emitted = maude_run(root, command)
    match = re.search(r'result State: result\(("(?:[^"\\]|\\.)*")\)', emitted)
    if not match:
        raise ValueError("generated unifier soundness evidence could not be emitted")
    trace.update(json.loads(json.loads(match.group(1))))
    if metrics is not None:
        stats = re.search(r'rewrites: (\d+) in (\d+)ms cpu', emitted)
        metrics.update(sound_wall_ms=round((time.monotonic() - start) * 1000, 3),
            sound_rewrites=int(stats.group(1)) if stats else None,
            sound_cpu_ms=int(stats.group(2)) if stats else None)
    return trace

def untargeted_unify(root, request, *, metrics=None, with_sound=True):
    """Diagnostic calculus baseline, NOT production certification or native unify.

    Reject supplied answers instead of ignoring them silently. Maude runs the
    SAME exhaustive rules, then collects its solved leaves as a redundant CSU.
    Leaf numbering/output assembly is done in Maude, not Python proof search.
    No answer is known until that search has finished. Generated scopes retain
    unused passthrough variables: this comparison does not minimize its CSU.
    with_sound=False returns reference data/completeness evidence ONLY; it is
    not a checked exactness certificate until soundness is attached and checked.
    """
    if request["aggregate"] != "system" or request.get("proposed"):
        raise ValueError("untargeted baseline requires a system with NO supplied answers")
    validate_request(request)
    trace = producer_result(root, request, untargeted=True, metrics=metrics)
    return annotate_generated_sound(root, request, trace, metrics=metrics) if with_sound else trace


# Coordinator: native answer acquisition is OUTSIDE the fixed-Sigma calculus.
# All stages below are untrusted syntax/data handling; none invokes Lean.
def native_identifier(value):
    if type(value) is not str or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'-]*", value):
        raise ValueError("native export requires simple prefix identifiers")
    return value

class NativeInterface:
    """Many-sorted constructor-prefix interface, not a unification algorithm."""
    def __init__(self, request, *, terms_only=False):
        if request.get("aggregate") != "system" or (not request.get("eqs") and not terms_only):
            raise ValueError("coordinator requires a nonempty equation system")
        if request.get("proposed"):
            raise ValueError("answers already supplied: use --certify instead")
        if not isinstance(request.get("signature"), list) or not request["signature"]:
            raise ValueError("coordinator needs exported constructor metadata")
        validate_request(dict(request, proposed=[]))
        declaration(request["problem"])
        declaration(request["answers"])
        native = request["native"]
        self.module = native_identifier(native["module"])
        self.sorts = {}
        for code, name in native["sort_names"].items():
            if not re.fullmatch(r"0|[1-9][0-9]*", code):
                raise ValueError("invalid exported sort code")
            self.sorts[int(code)] = native_identifier(name)
        if len(set(self.sorts.values())) != len(self.sorts):
            raise ValueError("duplicate native sort name")
        self.sort_codes = {name: code for code, name in self.sorts.items()}
        self.heads = {h["id"]: h for h in request["signature"]}
        self.names = {}
        for code, name in native["constructor_names"].items():
            if not re.fullmatch(r"0|[1-9][0-9]*", code):
                raise ValueError("invalid exported constructor code")
            self.names[int(code)] = native_identifier(name)
        if set(self.heads) != set(self.names) or len(set(self.names.values())) != len(self.names):
            raise ValueError("constructor name map must be total and unambiguous")
        self.codes = {name: code for code, name in self.names.items()}
        for sort in request["scope"] + [s for h in self.heads.values() for s in h["inputs"] + [h["output"]]]:
            if sort not in self.sorts:
                raise ValueError("sort name map is incomplete")
        self.variables = [native_identifier(v) for v in native["variables"]]
        if len(self.variables) != len(request["scope"]) or len(set(self.variables)) != len(self.variables):
            raise ValueError("native variables must identify every original input once")
        if set(self.variables).intersection(self.codes):
            raise ValueError("native variable/constructor names collide")
        self.input_sorts = dict(zip(self.variables, request["scope"]))

    def term(self, t):
        if "var" in t:
            name = self.variables[t["var"]]
            return name + ":" + self.sorts[self.input_sorts[name]]
        return self.names[t["app"]] + ("(" + ",".join(self.term(a) for a in t["args"]) + ")" if t["args"] else "")

    def query(self, request):
        return "unify in " + self.module + " : " + " /\\ ".join(
            self.term(e["left"]) + " =? " + self.term(e["right"]) for e in request["eqs"]) + " ."

    def read_term(self, text):
        tokens = re.findall(r"[^\s(),:]+|[(),:]", text)
        index = 0
        def read():
            nonlocal index
            if index >= len(tokens):
                raise ValueError("truncated native constructor term")
            name = tokens[index]
            index += 1
            if name in "(),:":
                raise ValueError("expected a native constructor or variable")
            if index < len(tokens) and tokens[index] == ":":
                index += 1
                if index >= len(tokens) or tokens[index] not in self.sort_codes:
                    raise ValueError("unknown native variable sort")
                sort = self.sort_codes[tokens[index]]
                index += 1
                if name not in self.input_sorts and not re.fullmatch(r"[#%][0-9]+", name):
                    raise ValueError("unknown native variable")
                return ("var", name, sort)
            if name in self.input_sorts:
                return ("var", name, self.input_sorts[name])
            if name not in self.codes:
                raise ValueError("unsupported native constructor syntax: " + name)
            args = []
            if index < len(tokens) and tokens[index] == "(":
                index += 1
                args.append(read())
                while index < len(tokens) and tokens[index] == ",":
                    index += 1
                    args.append(read())
                if index >= len(tokens) or tokens[index] != ")":
                    raise ValueError("malformed native constructor arguments")
                index += 1
            return ("app", self.codes[name], args)
        result = read()
        if index != len(tokens):
            raise ValueError("trailing native term syntax")
        return result

    def encode_term(self, raw, expected, variable):
        """Shared typed constructor lowering for input terms and answer images."""
        kind, name, data = raw
        if kind == "var":
            if data != expected:
                raise ValueError("native variable has wrong sort")
            return variable(name, data)
        head = self.heads[name]
        if head["output"] != expected:
            raise ValueError("native constructor has wrong sort")
        if head["role"] == "add" and len(data) > 2:
            args = [self.encode_term(a, expected, variable) for a in data]
            result = args[-1]
            for a in reversed(args[:-1]):
                result = {"app": name, "args": [a, result]}
            return result
        if len(data) != len(head["inputs"]):
            raise ValueError("native constructor arity mismatch")
        return {"app": name, "args": [self.encode_term(a, s, variable)
            for a, s in zip(data, head["inputs"])]}

    def answer(self, bindings):
        parameters, slots = [], {}
        def translate(raw, expected, visiting=frozenset()):
            def variable(name, sort):
                if name in self.input_sorts and self.input_sorts[name] != sort:
                    raise ValueError("native variable has wrong sort")
                bound = bindings.get(name)
                if bound is not None and bound != ("var", name, sort):
                    if name in visiting:
                        raise ValueError("cyclic native substitution")
                    return translate(bound, sort, visiting | {name})
                key = (name, sort)
                if key not in slots:
                    slots[key] = len(parameters)
                    parameters.append(sort)
                return {"var": slots[key]}
            return self.encode_term(raw, expected, variable)
        # Unmentioned original variables pass through; fresh slots are scoped
        # PER ANSWER and shared across ALL images. Only occurring slots survive.
        images = [translate(("var", v, self.input_sorts[v]), self.input_sorts[v]) for v in self.variables]
        return {"parameters": parameters, "images": images}

    def answers(self, output):
        if "Warning:" in output or len(re.findall(r"^unify in ", output, re.M)) > 1:
            raise ValueError("native transcript is not one successful query")
        blocks, current = [], None
        for line in output.splitlines():
            line = line.strip()
            heading = re.fullmatch(r"Unifier ([0-9]+)", line)
            if heading:
                if int(heading[1]) != len(blocks) + 1:
                    raise ValueError("unexpected native unifier numbering")
                current = {}
                blocks.append(current)
            elif " --> " in line:
                if current is None:
                    raise ValueError("native binding outside a unifier block")
                domain, image = line.split(" --> ", 1)
                variable = self.read_term(domain)
                if variable[0] != "var" or variable[1] not in self.input_sorts or variable[2] != self.input_sorts[variable[1]]:
                    raise ValueError("unknown native substitution domain")
                if variable[1] in current:
                    raise ValueError("duplicate native substitution domain")
                current[variable[1]] = self.read_term(image)
        if "No unifier." in output:
            if blocks:
                raise ValueError("conflicting native answer transcript")
            return []
        if not blocks:
            raise ValueError("native output contained no unifier result")
        return [self.answer(bindings) for bindings in blocks]

def native_request(ctor, command):
    """Infer sorted syntax from a closed constructor module and ONE unify query.

    No model-specific names, unification or semantic proof search here. Sort and
    head codes follow declaration order; input slots follow sorted variable names.
    Extra equations/imports/subsorts/attributes are rejected, not silently ignored.
    """
    model = ctor.read_text()
    source = re.sub(r"(?m)(?:---|\*\*\*).*?$", "", model).strip()
    module = re.fullmatch(r"fmod\s+(\S+)\s+is\s+(.*?)\s+endfm", source, re.S)
    if not module:
        raise ValueError("constructor file must contain one closed fmod")
    module_name = native_identifier(module[1])
    sorts, constructors = [], []
    for statement in module[2].split("."):
        statement = statement.strip()
        if not statement:
            continue
        declaration_match = re.fullmatch(r"sorts?\s+(.+)", statement, re.S)
        if declaration_match:
            for name in declaration_match[1].split():
                name = native_identifier(name)
                if name in sorts:
                    raise ValueError("duplicate sort declaration")
                sorts.append(name)
            continue
        operator = re.fullmatch(r"op\s+(\S+)\s*:\s*(.*?)\s*->\s*(\S+)\s*\[([^\]]*)\]", statement, re.S)
        if not operator:
            raise ValueError("unsupported constructor declaration: " + statement)
        name = native_identifier(operator[1])
        inputs = [native_identifier(s) for s in operator[2].split()]
        output = native_identifier(operator[3])
        attrs = operator[4]
        units = re.findall(r"\bid:\s*([^\s]+)", attrs)
        attributes = re.sub(r"\bid:\s*[^\s]+", "", attrs).split()
        if len(attributes) != len(set(attributes)):
            raise ValueError("duplicate constructor attribute")
        if set(attributes) == {"ctor"} and not units:
            role, unit = "free", None
        elif set(attributes) == {"ctor", "assoc", "comm"} and len(units) == 1:
            role, unit = "add", native_identifier(units[0])
        else:
            raise ValueError("only free constructors and one assoc/comm/id operator are supported")
        if any(h["name"] == name for h in constructors):
            raise ValueError("overloaded/duplicate constructor names are unsupported")
        constructors.append(dict(name=name, inputs=inputs, output=output, role=role, unit=unit))
    if not sorts or not constructors:
        raise ValueError("constructor module needs sort and constructor declarations")
    sort_codes = {name: i for i, name in enumerate(sorts)}
    heads = []
    for i, h in enumerate(constructors):
        if any(s not in sort_codes for s in h["inputs"] + [h["output"]]):
            raise ValueError("constructor refers to an undeclared sort")
        heads.append(dict(id=i, inputs=[sort_codes[s] for s in h["inputs"]],
            output=sort_codes[h["output"]], role=h["role"]))
    for h in constructors:
        if h["unit"] is not None:
            candidates = [i for i, k in enumerate(constructors) if k["name"] == h["unit"]]
            if len(candidates) != 1 or heads[candidates[0]]["role"] != "free":
                raise ValueError("ACU unit must be a declared free nullary constructor")
            heads[candidates[0]]["role"] = "zero"
    query = re.fullmatch(r"\s*unify\s+in\s+(\S+)\s*:\s*(.*?)\s*\.\s*", command, re.S)
    if not query or query[1] != module_name:
        raise ValueError("supply ONE unify in the declared constructor module")
    variables = {}
    for name, sort in re.findall(r"([A-Za-z_][A-Za-z_0-9'-]*)\s*:\s*([A-Za-z_][A-Za-z_0-9'-]*)", query[2]):
        if sort not in sort_codes:
            raise ValueError("query variable has undeclared sort")
        if name in variables and variables[name] != sort_codes[sort]:
            raise ValueError("same variable name used at different sorts")
        variables[name] = sort_codes[sort]
    ordered = sorted(variables)
    request = dict(aggregate="system", problem="inputProblem", answers="certifiedAnswers",
        signature=heads, scope=[variables[v] for v in ordered], eqs=[], native=dict(
            module=module_name, model=model, sort_names={str(i): s for i, s in enumerate(sorts)},
            constructor_names={str(i): h["name"] for i, h in enumerate(constructors)}, variables=ordered))
    interface = NativeInterface(request, terms_only=True)
    slots = {name: i for i, name in enumerate(ordered)}
    def variable(name, sort):
        if name not in variables or variables[name] != sort:
            raise ValueError("query contains a fresh or incorrectly typed variable")
        return {"var": slots[name]}
    for pair in query[2].split("/\\"):
        sides = pair.split("=?")
        if len(sides) != 2:
            raise ValueError("expected equations separated by /\\ with one =? per equation")
        left, right = (interface.read_term(side) for side in sides)
        sort = left[2] if left[0] == "var" else interface.heads[left[1]]["output"]
        request["eqs"].append(dict(sort=sort, left=interface.encode_term(left, sort, variable),
            right=interface.encode_term(right, sort, variable)))
    validate_request(dict(request, proposed=[]))
    return request

def save_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")

def load_json(path):
    return json.loads(path.read_text())

def maude_load(path):
    # Keep saved scripts literally replayable; no shell interpolation.
    path = str(path.resolve())
    if re.search(r"\s|[\"\n\r]", path):
        raise ValueError("prototype Maude scripts require paths without whitespace/quotes")
    return "load " + path

def prepare_native(root, request, out, ctor=None, *, replace=False):
    """Stage 1a: export a self-contained native script, with NO Maude call."""
    interface = NativeInterface(request)
    native = request["native"]
    if ctor is not None:
        model = ctor.read_text()
    elif "model" in native:
        model = native["model"]
    else:
        model = (root / native["source"]).read_text()
    out.mkdir(parents=True, exist_ok=True)
    saved = out / "00-request.json"
    exported = dict(request, native=dict(native, model=model))
    if saved.exists() and load_json(saved) != exported and not replace:
        raise ValueError("output directory belongs to another request; choose a fresh --out")
    # A sequential cache can be reused for another problem. Invalidate old proof
    # artifacts BEFORE starting so an interrupted run cannot expose an old result.
    for name in ("02-target.json", "03-trace.json", "04-proof.json", "result.json"):
        save_json(out / name, {"stage": "pending", "kernel_checked": False})
    save_json(saved, exported)
    (out / "ctor.maude").write_text(model)
    query = interface.query(request)
    (out / "01-native-query.maude").write_text(query + "\n")
    script = out / "01-native.maude"
    script.write_text(maude_load(out / "ctor.maude") + "\n" + query + "\nquit\n")
    save_json(out / "status.json", {"stage": "native-prepared", "kernel_checked": False})
    return script

def prepare_target(root, out, native_output):
    """Stage 1b: decode native answers, FREEZE Sigma, prepare targeted script."""
    exported = load_json(out / "00-request.json")
    (out / "01-native.stdout").write_text(native_output)
    save_json(out / "status.json", {"stage": "native-received", "kernel_checked": False})
    interface = NativeInterface(exported)
    target = {k: exported[k] for k in ("aggregate", "problem", "answers", "signature", "scope", "eqs")}
    target["proposed"] = interface.answers(native_output)
    validate_request(target)
    save_json(out / "02-target.json", target)
    wrapper = out / "wrapper.maude"
    (out / "certification.maude").write_text((ENGINE_DIR / "certification.maude").read_text())
    template = (ENGINE_DIR / "wrapper.maude").read_text()
    renaming = ", ".join("sort " + name + " to NativeSort" + str(code)
        for code, name in interface.sorts.items())
    wrapper.write_text(template.replace("@NATIVE_MODULE@", interface.module)
        .replace("@SORT_RENAMING@", renaming))
    query = certification_query(target, "CERTIFICATION-QUERY")
    (out / "02-target-query.maude").write_text(query + "\n")
    script = out / "02-target.maude"
    script.write_text(maude_load(wrapper) + "\n" + query + "\nquit\n")
    save_json(out / "status.json", {"stage": "target-prepared", "kernel_checked": False,
        "answers": len(target["proposed"])})
    return target, script

def compile_target(out, target_output):
    """Stage 2b: assemble proof for the FIXED target; NO Maude or Lean call."""
    (out / "02-target.stdout").write_text(target_output)
    save_json(out / "status.json", {"stage": "trace-received", "kernel_checked": False})
    target = load_json(out / "02-target.json")
    validate_request(target)
    trace = parse_certificate_output(target_output, target)
    bundle = compile_bundle(trace)
    save_json(out / "03-trace.json", trace)
    save_json(out / "04-proof.json", bundle)
    answer_value = "[" + ", ".join("{ parameters := " + scope(a["parameters"]) +
        ", images := " + terms(a["images"]) + " }" for a in target["proposed"]) + "]"
    result = {"format": "coordinated-certificate-v1", "request": target,
        "answer_value": answer_value, "certificate": bundle}
    save_json(out / "result.json", result)
    save_json(out / "status.json", {"stage": "proof-assembled", "kernel_checked": False,
        "answers": len(target["proposed"])})
    return result

def coordinate(root, request, out, ctor=None, *, replace=False):
    """ONE Lean/Python exchange, TWO sequential Maude calls; never launch Lean."""
    native_script = prepare_native(root, request, out, ctor, replace=replace)
    print("Native unification: " + str(native_script), file=sys.stderr, flush=True)
    native_output = maude_run(out.resolve(), "", source=native_script.resolve())
    target, target_script = prepare_target(root, out, native_output)
    print("Fixed " + str(len(target["proposed"])) + " native answers; targeted certification: " +
        str(target_script), file=sys.stderr, flush=True)
    target_output = maude_run(out.resolve(), "", source=target_script.resolve())
    result = compile_target(out, target_output)
    print("Proof assembled for current Lean session; NOT kernel-checked by Python", file=sys.stderr, flush=True)
    return result

def main():
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify", action="store_true", help="certify supplied answers; output proof only; never run unify or Lean")
    stages = parser.add_mutually_exclusive_group()
    stages.add_argument("--coordinate", action="store_true", help="native unify then fixed-answer certification; never run Lean")
    stages.add_argument("--prepare-native", action="store_true", help="write native input script only; no processes")
    stages.add_argument("--parse-native", type=Path, help="parse saved native stdout and prepare the targeted script; no processes")
    stages.add_argument("--compile-trace", type=Path, help="compile saved targeted stdout to Lean-ready proof; no processes")
    parser.add_argument("--request", type=Path, help="coordinator request JSON (otherwise stdin)")
    parser.add_argument("--ctor", type=Path, help="closed constructor-only fmod; used with --unify for the standalone frontend")
    parser.add_argument("--unify", help="one native unify command; infers the request from --ctor without JSON input")
    parser.add_argument("--out", type=Path, help="working cache directory (default: certifier/.cache)")
    args = parser.parse_args()
    root = ENGINE_DIR.parent  # Base for legacy typed requests with relative model paths.
    if args.unify is not None:
        if args.ctor is None or args.request is not None or args.certify or args.parse_native or args.compile_trace:
            parser.error("--unify requires --ctor and cannot be mixed with JSON input or other modes")
        if not args.prepare_native:
            args.coordinate = True
    coordinating = args.coordinate or args.prepare_native or args.parse_native or args.compile_trace
    if coordinating:
        if args.certify:
            parser.error("coordinator stages cannot be mixed with existing modes")
        args.out = args.out or ENGINE_DIR / ".cache"
        if args.coordinate or args.prepare_native:
            request = native_request(args.ctor, args.unify) if args.unify is not None else \
                load_json(args.request) if args.request else json.load(sys.stdin)
            result = coordinate(root, request, args.out, args.ctor, replace=args.unify is not None) if args.coordinate else \
                {"native_script": str(prepare_native(root, request, args.out, args.ctor, replace=args.unify is not None))}
        elif args.parse_native:
            target, script = prepare_target(root, args.out, args.parse_native.read_text())
            result = {"answers": len(target["proposed"]), "target_script": str(script)}
        else:
            assembled = compile_target(args.out, args.compile_trace.read_text())
            result = {"answers": len(assembled["request"]["proposed"]),
                "proof_file": str(args.out / "04-proof.json"),
                "result_file": str(args.out / "result.json"), "kernel_checked": False}
        print(json.dumps(result))
    elif args.certify:
        print(json.dumps(compile_bundle(certify(root, json.load(sys.stdin)))))
    else:
        print(compile_proof(json.load(sys.stdin)))

if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, KeyError, OSError) as error:
        sys.exit(str(error))
