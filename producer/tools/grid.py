#!/usr/bin/env python3
"""Certify a generated grid of small problems end to end, to find shapes the step
tactics do not handle before an example does.

  python3 producer/tools/grid.py              # 40 flat + 40 nested problems, seed 1
  python3 producer/tools/grid.py --n 20 --seed 7 --jobs 4

Problems are drawn (deterministically, from the seed) over one signature: elements
a, b, c in bags (sort Bag, variables X, Y, Z), boxes box(bag) in bags of boxes (sort
Boxes, variables R, S). Flat problems equate two bags of elements; nested ones two bags
of boxes. Each problem is derived by Maude, compiled and checked by Lean, as in demo.py.
Files are written to producer/tests/grid/ (not tracked). Untrusted, like the producer.
"""
import argparse, pathlib, random, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parents[2]
TOOLS = ROOT / "producer" / "tools"
OUT = ROOT / "producer" / "tests" / "grid"
sys.path.insert(0, str(TOOLS))
import derive  # noqa: E402

BAG_VARS, BOX_VARS, ELEMS = ["X", "Y", "Z"], ["R", "S"], ["a", "b", "c"]
SORT = {**{v: "Bag" for v in BAG_VARS}, **{v: "Boxes" for v in BOX_VARS}}

# terms: ("var", name) | ("elem", name) | ("box", [atoms]); a side is a list of atoms


def flat_side(rng):
    return [rng.choice([("var", rng.choice(BAG_VARS)), ("elem", rng.choice(ELEMS))])
            for _ in range(rng.randint(1, 3))]


def nested_side(rng):
    side = [("box", flat_side(rng)[:2]) for _ in range(rng.randint(1, 2))]
    if rng.random() < .6:
        side.append(("var", rng.choice(BOX_VARS)))
    return side


def variables(sides):
    seen = []
    def walk(t):
        if t[0] == "var" and t[1] not in seen:
            seen.append(t[1])
        if t[0] == "box":
            for s in t[1]:
                walk(s)
    for side in sides:
        for t in side:
            walk(t)
    return seen


def maude(side, nested):
    def atom(t):
        if t[0] == "var":
            return f"'{t[1]}:{SORT[t[1]]}"
        if t[0] == "elem":
            return f"'{t[1]}.Elem"
        return f"'`{{_`}}[{maude(t[1], False)}]"
    args = [atom(t) for t in side]
    return args[0] if len(args) == 1 else ("'_|_" if nested else "'__") + "[" + ", ".join(args) + "]"


def lean(side):
    def atom(t):
        if t[0] == "var":
            return f"{t[1]}?"
        if t[0] == "elem":
            return f"{{Elem.{t[1]}}}"
        return f"{{Box.box ({lean(t[1])})}}"
    return " + ".join(atom(t) for t in side)


def problems(n, seed):
    rng, out, seen = random.Random(seed), [], set()
    for nested in (False, True):
        k = 0
        while k < n:
            lhs, rhs = (nested_side(rng), nested_side(rng)) if nested else (flat_side(rng), flat_side(rng))
            key = (repr(lhs), repr(rhs))
            vs = variables([lhs, rhs])
            if key in seen or not vs or len(vs) > 4:
                continue
            seen.add(key)
            out.append((f"{'n' if nested else 'f'}{k:02d}", nested, lhs, rhs, vs))
            k += 1
    return out


def write(case):
    name, nested, lhs, rhs, vs = case
    sorts = [SORT[v] for v in vs]
    (OUT / f"{name}.maude").write_text(
        f"***( {lean(lhs)} =? {lean(rhs)} )\nload models.maude\nselect SHOW .\n"
        f"red certify('GRID, bag('Bag, '__, 'none.Bag) &b bag('Boxes, '_|_, 'nil.Boxes), 'tup,\n"
        f"  ({', '.join(f'{chr(39)}{v}:{SORT[v]}' for v in vs)}),\n"
        f"  {maude(lhs, nested)}, {maude(rhs, nested)}) .\n")
    ctx = " × ".join(sorts)
    pat = vs[0] + "?" if len(vs) == 1 else "(" + ", ".join(v + "?" for v in vs) + ")"
    header = ('{\n  "namespace": "Grid.' + name.upper() + '",\n  "context": "' + ctx + '",\n'
              '  "vars": [' + ", ".join(f'"{v}?"' for v in vs) + '],\n'
              '  "ops": {"a": "Elem.a", "b": "Elem.b", "c": "Elem.c", "{_}": "Box.box"}\n}')
    (OUT / f"{name}.claim.lean").write_text(f"""import conPanna.Unification.Certification.Tactics

/-! Grid problem: {lean(lhs)} =? {lean(rhs)}. -/

/- certify
{header}
-/

open Unification Certification

namespace Grid.{name.upper()}

inductive Elem where
  | a
  | b
  | c

abbrev Bag := ACU Elem

inductive Box where
  | box (b : Bag)

abbrev Boxes := ACU Box

def problem : Problem {"Boxes" if nested else "Bag"} ({ctx}) :=
  .bind fun {pat} => ({lean(lhs)}, {lean(rhs)})
""")
    return sorts


def models(signatures):
    tups = "\n".join(f"  op tup : {' '.join(s)} -> Tup [ctor] ." for s in sorted(signatures))
    (OUT / "models.maude").write_text(f"""fmod GRID is
  sorts Elem Bag Box Boxes Tup .
  subsort Elem < Bag .
  subsort Box < Boxes .
  ops a b c : -> Elem [ctor] .
  op none : -> Bag [ctor] .
  op __ : Bag Bag -> Bag [ctor assoc comm id: none] .
  op {{_}} : Bag -> Box [ctor] .
  op nil : -> Boxes [ctor] .
  op _|_ : Boxes Boxes -> Boxes [ctor assoc comm id: nil] .
{tups}
endfm
""")


def check(name):
    """Derive, compile and check one problem: (name, verdict, detail)."""
    try:
        text = derive.run_maude(OUT / f"{name}.maude")
    except BaseException as e:  # Maude error
        return name, "maude", str(e).splitlines()[0][:200]
    (OUT / f"{name}.deriv").write_text(text)
    if "STUCK" in text:
        return name, "stuck", next(l.strip() for l in text.splitlines() if "STUCK" in l)
    r = subprocess.run([sys.executable, str(TOOLS / "compile.py"), str(OUT / f"{name}.claim.lean"),
                        str(OUT / f"{name}.deriv")], cwd=ROOT, capture_output=True, text=True)
    if r.returncode:
        return name, "compile", (r.stdout + r.stderr).strip().splitlines()[-1][:200]
    try:
        r = subprocess.run(["lake", "env", "lean", str(OUT / f"{name}.lean")], cwd=ROOT,
                           capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return name, "timeout", "Lean took over 600 s"
    errors = [l for l in (r.stdout + r.stderr).splitlines() if ": error" in l]
    if r.returncode or errors:
        return name, "lean", (errors[0] if errors else r.stderr.strip()[:200])
    return name, "ok", ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=40, help="problems per family")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=4)
    a = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    for f in OUT.glob("*"):
        f.unlink()
    cases = problems(a.n, a.seed)
    models({tuple(write(c)) for c in cases})
    with ThreadPoolExecutor(a.jobs) as pool:
        results = list(pool.map(check, [c[0] for c in cases]))
    for name, verdict, detail in results:
        if verdict != "ok":
            print(f"{name}: {verdict}: {detail}")
    counts = {}
    for _, verdict, _ in results:
        counts[verdict] = counts.get(verdict, 0) + 1
    print("summary:", ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))


if __name__ == "__main__":
    main()
