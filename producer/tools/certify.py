#!/usr/bin/env python3
"""Certify completeness of given unifiers: Maude derivation, then a Lean proof script.

  python3 producer/tools/certify.py request.json > reply.json

The entry of the Lean tactic `maude_certify_comp`. Request (terms as in unify.py):
  {"model": ".../ctor.maude",
   "vars": [{"name": "X1", "sort": "Nat"}, ...],   the problem's variables
   "shape": [["X1", ["X2", "X3"]], ["X4", "X5"]],  their nesting in the Lean context
   "lhs": T, "rhs": T,
   "answers": [{"sub": {"X1": T, ...}, "binder": shape over "#1", "#2", ...}, ...]}
Reply: {"script": tactic text}, a proof of `complete P U` for the goal Lean has put in
literal form. If no derivation exists (an answer is missing), it exits with the
uncovered leaf. Untrusted: Lean checks the script.
"""
import json, os, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import compile as comp  # noqa: E402
import derive  # noqa: E402
from unify import render  # noqa: E402


def main():
    req = json.load(open(sys.argv[1]))
    model = pathlib.Path(os.path.abspath(req["model"]))
    table = json.load(open(model.with_name("ctor.json")))
    sorts = {v["name"]: v["sort"] for v in req["vars"]}
    bags = " &b ".join(f"bag('{s}, '{u}, '{z}.{s})" for s, u, z in table["bags"]) or "noBag"
    tl = ", ".join(f"'{v['name']}:{v['sort']}" for v in req["vars"])
    answers = " :: ".join(
        "(" + (" ; ".join(f"'{x}:{sorts[x]} <- {render(t)}" for x, t in a["sub"].items()) or "none") + ")"
        for a in req["answers"]) or "noAns"
    request = model.with_name("certify-request.maude")
    request.write_text(f"load {model}\nselect SHOW .\n"
                       f"red certifyWith('CTOR, {bags}, 'tup, ({tl}),\n"
                       f"  {render(req['lhs'])},\n  {render(req['rhs'])},\n  {answers}) .\n")
    text = derive.run_maude(request)
    model.with_name("certify.deriv").write_text(text)
    stuck = [l.strip() for l in text.splitlines() if "STUCK" in l]
    if stuck:
        raise SystemExit(f"certify.py: the unifiers are not complete: {stuck[0]}\n\n{text}")
    _, root = comp.parse_derivation(text)

    q = lambda s: s + "?" if isinstance(s, str) else [q(x) for x in s]  # Maude X1 is X1? in derivations
    c = comp.Compiler({"ops": table["ops"], "vars": [v["name"] + "?" for v in req["vars"]],
                       "shape": q(req["shape"]), "unfold": [], "script": True,
                       "answer_binders": [a["binder"] for a in req["answers"]]})
    c.binders = [[f"U{b[1:]}!" for b in comp.leaves(a["binder"])] for a in req["answers"]]
    c.emit(0, "rw [← start_iff]")
    eqs = root.judgment[1]
    if len(eqs) > 1:
        c.emit(0, "-- decomp of the tuple equation into the system")
        c.emit(0, f"refine decomp ({c.lam(c.initial, c.conj(eqs))})")
        c.emit(2, f"(fun {c.pat(c.initial)} h => by {c.free()}) ?_")
    c.node(root, c.initial, 0, at_start=len(eqs) == 1)
    json.dump({"script": "\n".join(c.out)}, sys.stdout)


if __name__ == "__main__":
    main()
