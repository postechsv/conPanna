#!/usr/bin/env python3
"""Compute all unifiers of each problem with Maude, in the dumped module CTOR.

  python3 producer/tools/unify.py request.json > reply.json     (or the request on stdin)

Request: {"model": "producer/.cache/ctor.maude", "problems": [{"lhs": T, "rhs": T}, ...]}
Reply:   {"unifiers": [[{"X": T, ...}, ...], ...]}   one list of substitutions per problem

A term T is {"var": name, "sort": S} or {"op": name, "sort": S, "args": [T, ...]}.
In replies, only variables and constants carry a sort (Maude's meta-level output
does not annotate applications). Fresh variables are Maude's #1, #2, ...
Untrusted: the unifiers are data; Lean certifies them separately.
"""
import json, os, re, subprocess, sys

ALL_UNIFIERS = """
fmod ALL-UNIFIERS is
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


def render(t):
    """A JSON term as a Maude meta-term."""
    if "var" in t:
        return f"'{t['var']}:{t['sort']}"
    if not t["args"]:
        return f"'{t['op']}.{t['sort']}"
    return f"'{t['op']}[" + ", ".join(render(a) for a in t["args"]) + "]"


TOKEN = re.compile(r"\s*('[^\[\],;{}\s]+|\[|\]|,|;;|;|\{|\}|<-|\(nil\)\.UList|\d+)")


def tokens(s):
    pos, out = 0, []
    while pos < len(s.rstrip()):
        m = TOKEN.match(s, pos)
        if not m:
            raise SystemExit(f"unify.py: cannot parse Maude output at: {s[pos:pos + 40]!r}")
        out.append(m.group(1))
        pos = m.end()
    return out


def parse(s):
    """Maude's  UList  result as a list of substitutions."""
    ts, i = tokens(s), 0

    def term():
        nonlocal i
        q = ts[i][1:]; i += 1
        if i < len(ts) and ts[i] == "[":
            i += 1
            args = [term()]
            while ts[i] == ",":
                i += 1
                args.append(term())
            i += 1  # ]
            return {"op": q, "args": args}
        if ":" in q:
            name, sort = q.rsplit(":", 1)
            return {"var": name, "sort": sort}
        op, sort = q.rsplit(".", 1)
        return {"op": op, "sort": sort, "args": []}

    if ts == ["(nil).UList"]:
        return []
    subs = []
    while i < len(ts):
        i += 1  # {
        sub = {}
        while ts[i] != ",":
            name = ts[i][1:].rsplit(":", 1)[0]; i += 2  # var <-
            sub[name] = term()
            if ts[i] == ";":
                i += 1
        i += 3  # , n }
        subs.append(sub)
        if i < len(ts) and ts[i] == ";;":
            i += 1
    return subs


def main():
    req = json.load(open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin)
    script = f"load {os.path.abspath(req['model'])}\n{ALL_UNIFIERS}\n"
    for p in req["problems"]:
        script += f"red all(upModule('CTOR, false), {render(p['lhs'])} =? {render(p['rhs'])}, 0) .\n"
    run = subprocess.run(["maude", "-no-banner", "-no-wrap", "-no-advise"], input=script + "quit\n",
                         capture_output=True, text=True, check=True)
    out = run.stdout
    if "Warning" in run.stderr + out:
        raise SystemExit("unify.py: Maude warnings:\n" + run.stderr + out)
    results = re.findall(r"result (?:UList|UnificationPair): (.*?)(?=\n={5,}|\nBye|\Z)", out, re.S)
    if len(results) != len(req["problems"]):
        raise SystemExit("unify.py: unexpected Maude output:\n" + out)
    json.dump({"unifiers": [parse(r) for r in results]}, sys.stdout)


if __name__ == "__main__":
    main()
