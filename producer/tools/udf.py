#!/usr/bin/env python3
"""A UDF derivation (documentation/derivation-format.md) for given unifiers: the entry of
the Lean tactic `udf_certify`.

  python3 producer/tools/udf.py request.json > reply.json

The request is `certify.py`'s (the dumped model, the problem's variables and their
nesting, lhs, rhs, and the answers). The instrumented Maude unifies, and its trace is
extracted into a derivation whose leaves are covered by the given answers
(trace_to_udf.py). Reply: {"udf": text}. If a leaf is covered by no answer, the answers
are not complete, and it exits with that leaf. Untrusted: Lean checks the derivation.
"""
import json, os, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import trace_to_udf as tu  # noqa: E402
from unify import render  # noqa: E402


def term(t):
    """A JSON term (unify.py) as a term of trace_to_udf."""
    if "var" in t:
        return tu.V(t["var"], t["sort"])
    return tu.A(t["op"], tuple(term(a) for a in t.get("args", [])))


def main():
    req = json.load(open(sys.argv[1]))
    model = pathlib.Path(os.path.abspath(req["model"]))
    sorts = {v["name"]: v["sort"] for v in req["vars"]}
    answers = [{tu.V(x, sorts[x]): term(t) for x, t in a["sub"].items()} for a in req["answers"]]
    text, st = tu.extract(str(model), "CTOR", [(render(req["lhs"]), render(req["rhs"]))], answers,
                          [tu.V(x, s) for x, s in sorts.items()])
    if st["covered"] < st["leaves"]:
        leaf = next(line for line in text.splitlines() if " leaf " in line)
        raise SystemExit(f"udf.py: the unifiers are not complete: no answer covers {leaf}\n\n{text}")
    json.dump({"udf": text}, sys.stdout)


if __name__ == "__main__":
    main()
