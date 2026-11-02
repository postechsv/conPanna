#!/usr/bin/env python3
"""Rebuild Maude's unification search tree from its unification trace.

  python3 producer/tools/trace_tree.py model.maude Module 'lhs-meta' 'rhs-meta'
      # runs the instrumented Maude (maude/build.sh) on  lhs =? rhs  and prints the tree

The instrumented Maude prints one event per inference step when MAUDE_UNIFICATION_TRACE
is set (maude/src/Core/unificationTrace.hh). Unification is a depth-first backtracking
search whose only choice points are ACU subproblems: each one prints its system and
basis, then one `acu-select` per alternative, then `acu-exhausted`. So the flat event
stream determines the tree: a frame per ACU subproblem, a branch per selection, the free
steps (decomp, bind, ...) attached to the branch they happen in, a leaf per `unifier`.
Untrusted, like the rest of the producer.
"""
import os, pathlib, re, subprocess, sys
from dataclasses import dataclass, field

ROOT = pathlib.Path(__file__).resolve().parents[2]
MAUDE = ROOT / "maude" / "Opt" / "src" / "Main" / "maude"
MAUDE_LIB = ROOT / "maude" / "src" / "Main"

ALL_UNIFIERS = """
fmod TRACE-ALL-UNIFIERS is
  protecting META-LEVEL .
  sort UList .
  subsort UnificationPair < UList .
  op nil : -> UList [ctor] .
  op _;;_ : UList UList -> UList [ctor assoc id: nil] .
  op all : Module UnificationProblem Nat -> UList .
  op all : Module UnificationProblem Nat UnificationPair? -> UList .
  var M : Module . var P : UnificationProblem . var N : Nat . var UP : UnificationPair .
  eq all(M, P, N) = all(M, P, N, metaUnify(M, P, 0, N)) .
  eq all(M, P, N, noUnifier) = nil .
  eq all(M, P, N, UP) = UP ;; all(M, P, s N) .
endfm
"""


@dataclass
class Branch:
    selection: list                       # basis element indices, e.g. ["#7", "#6", "#2"]
    events: list = field(default_factory=list)   # (kind, text) and nested Frames, in order
    leaves: int = 0                       # unifiers found directly here

    def nr_leaves(self):
        return self.leaves + sum(x.nr_leaves() for x in self.events if isinstance(x, Frame))


@dataclass
class Frame:
    ident: str
    system: str
    basis: str = ""
    branches: list = field(default_factory=list)
    exhausted: bool = False

    def nr_leaves(self):
        return sum(b.nr_leaves() for b in self.branches)


def run(model, module, lhs, rhs):
    """Unify with the instrumented Maude: (trace text, number of unifiers)."""
    script = (f"load {pathlib.Path(model).resolve()}\n{ALL_UNIFIERS}\n"
              f"red all(upModule('{module}, false), {lhs} =? {rhs}, 0) .\nquit\n")
    env = dict(os.environ, MAUDE_UNIFICATION_TRACE="1", MAUDE_LIB=str(MAUDE_LIB))
    r = subprocess.run([str(MAUDE), "-no-banner", "-no-wrap", "-no-advise"], input=script,
                       capture_output=True, text=True, env=env, check=True)
    if "Warning" in r.stdout:
        raise SystemExit("trace_tree.py: Maude warnings:\n" + r.stdout)
    m = re.search(r"result (UList|UnificationPair): (.*?)(?:\n={5,}|\nBye|\Z)", r.stdout, re.S)
    # each unifier is a pair  {substitution, n} : count the pairs' closing  , n}
    nr = 0 if not m else len(re.findall(r",\s*\d+\s*\}", m.group(2)))
    return r.stderr, nr


def events(trace):
    for line in trace.splitlines():
        if line.startswith("@u "):
            kind, _, rest = line[3:].partition(" ")
            yield kind, rest


def build(trace):
    """The search tree: a root branch holding the steps before the first choice."""
    root = Branch([])
    cursor = root
    stack = []                            # open frames, innermost last
    parent = {}                           # id(frame) -> branch it hangs from
    for kind, rest in events(trace):
        ident = rest.split()[0] if rest else ""
        if kind == "acu-system":
            f = Frame(ident, rest[len(ident) + 1:])
            cursor.events.append(f)
            parent[id(f)] = cursor
            stack.append(f)
        elif kind == "acu-basis":
            stack[-1].basis = rest[len(ident) + 1:]
        elif kind == "acu-select":
            while stack and stack[-1].ident != ident:
                stack.pop()               # an inner subproblem that ended without exhausting
            b = Branch(rest.split()[1:])
            stack[-1].branches.append(b)
            cursor = b
        elif kind in ("acu-exhausted", "acu-nocover"):
            while stack and stack[-1].ident != ident:
                stack.pop()
            if stack:
                f = stack.pop()
                f.exhausted = True
                cursor = parent[id(f)]
        elif kind == "unifier":
            cursor.leaves += 1
        else:
            cursor.events.append((kind, rest))
    return root


def show(branch, depth=0, out=None):
    out = [] if out is None else out
    pad = "  " * depth
    for x in branch.events:
        if isinstance(x, Frame):
            out.append(f"{pad}ACU {x.system[:110]}")
            out.append(f"{pad}  basis {x.basis[:110]}")
            for b in x.branches:
                sel = " ".join(b.selection) or "(empty)"
                out.append(f"{pad}  select {sel}: {b.nr_leaves()} unifier(s)")
                show(b, depth + 2, out)
        elif x[0] in ("decomp", "clash", "occurs", "ground", "acu-select-fail"):
            out.append(f"{pad}{x[0]} {x[1][:110]}")
    if branch.leaves:
        out.append(f"{pad}unifier" + (f" x{branch.leaves}" if branch.leaves > 1 else ""))
    return out


def check(trace, nr_unifiers):
    """The tree accounts for every unifier, and every selection reports its effect."""
    root = build(trace)
    selections = assigned = 0
    stack = [root]
    while stack:
        b = stack.pop()
        for x in b.events:
            if isinstance(x, Frame):
                for c in x.branches:
                    selections += 1
                    assigned += any(e[0] == "acu-assign" for e in c.events if not isinstance(e, Frame))
                    stack.append(c)
    return root, root.nr_leaves() == nr_unifiers, selections, assigned


def main():
    model, module, lhs, rhs = sys.argv[1:5]
    trace, nr = run(model, module, lhs, rhs)
    root, ok, sels, assigned = check(trace, nr)
    print("\n".join(show(root)))
    print(f"\nunifiers: Maude {nr}, tree leaves {root.nr_leaves()} -> {'ok' if ok else 'MISMATCH'}; "
          f"selections {sels}, with assignments {assigned}")


if __name__ == "__main__":
    main()
