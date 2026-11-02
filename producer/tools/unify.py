#!/usr/bin/env python3
"""Unifiers and their completeness certificates, for the Lean tactic `maude_unify`.

  python3 producer/tools/unify.py request.json > reply.json

Request: {"model": "producer/.cache/ctor-<hash>.maude", "certify": true,
          "problems": [{"lhs": T, "rhs": T, "vars": [{"name": X, "sort": S}, ...]}, ...]}
Reply:   {"unifiers": [[{"X": T, ...}, ...], ...], "udf": [text, ...]}

A term T is {"var": name, "sort": S} or {"op": name, "sort": S, "args": [T, ...]}. For each
problem, one run of the instrumented Maude computes Maude's filtered unifiers (from its
trace, in Maude's own variable names) and their completeness certificate, a UDF derivation
(trace_to_udf.py). Untrusted: Lean checks the certificate.
"""
import json, os, sys


def render(t):
    """A JSON term as a Maude meta-term."""
    if "var" in t:
        return f"'{t['var']}:{t['sort']}"
    if not t["args"]:
        return f"'{t['op']}.{t['sort']}"
    return f"'{t['op']}[" + ", ".join(render(a) for a in t["args"]) + "]"


def term_json(t):
    """A term of trace_to_udf as a JSON term."""
    import trace_to_udf as tu
    if isinstance(t, tu.V):
        return {"var": t.name, "sort": t.sort}
    return {"op": t.op, "args": [term_json(a) for a in t.args]}


def certify(req):
    import trace_to_udf as tu
    unifiers, udfs = [], []
    for p in req["problems"]:
        context = [tu.V(v["name"], v["sort"]) for v in p.get("vars", [])]
        text, st = tu.extract(os.path.abspath(req["model"]), "CTOR", [(render(p["lhs"]), render(p["rhs"]))],
                              context=context, canonical=True)
        if st["covered"] < st["leaves"]:
            raise SystemExit(f"unify.py: a leaf of the derivation is not covered\n\n{text}")
        unifiers.append([{x.name: term_json(t) for x, t in a.items()} for a in st["answer_terms"]])
        udfs.append(text)
    json.dump({"unifiers": unifiers, "udf": udfs}, sys.stdout)


def main():
    req = json.load(open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin)
    certify(req)


if __name__ == "__main__":
    main()
