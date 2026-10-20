#!/usr/bin/env python3
"""Compute all matches of each pattern against a subject with Maude, in the dumped module CTOR.

  python3 producer/tools/match.py request.json > reply.json     (or the request on stdin)

Request: {"model": "producer/.cache/ctor-<hash>.maude", "problems": [{"pattern": T, "subject": T}, ...]}
Reply:   {"matches": [[{"Y": T, ...}, ...], ...]}   one list of substitutions per problem

Only the pattern's variables are instantiated; the subject's variables stay fixed (Maude's
`metaMatch` treats them as constants). Terms as in unify.py, whose parser this reuses.
Untrusted: Lean checks the instantiated state equation itself.
"""
import json, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from unify import render, subst_at, tokens  # noqa: E402

ALL_MATCHES = """
fmod ALL-MATCHES is
  protecting META-LEVEL .
  sort SList .
  subsort Substitution < SList .
  op noMatches : -> SList [ctor] .
  op _;;_ : SList SList -> SList [ctor assoc id: noMatches] .
  op all : Module Term Term Nat -> SList .
  op all : Module Term Term Nat Substitution? -> SList .
  var M : Module . vars P S : Term . var N : Nat . var SB : Substitution .
  eq all(M, P, S, N) = all(M, P, S, N, metaMatch(M, P, S, nil, N)) .
  eq all(M, P, S, N, noMatch) = noMatches .
  eq all(M, P, S, N, SB) = SB ;; all(M, P, S, s N) .
endfm
"""


def parse(s):
    """Maude's  SList  result as a list of substitutions."""
    if s.strip() in ("noMatches", "(noMatches).SList"):
        return []
    ts = [t for t in tokens(s) if t not in ("(", ")")]  # several matches are parenthesized
    i = 0
    subs = []
    while i < len(ts):
        sub, i = subst_at(ts, i, {";;"})
        subs.append(sub)
        if i < len(ts) and ts[i] == ";;":
            i += 1
    return subs


def main():
    req = json.load(open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin)
    script = f"load {os.path.abspath(req['model'])}\n{ALL_MATCHES}\n"
    for p in req["problems"]:
        script += f"red all(upModule('CTOR, false), {render(p['pattern'])}, {render(p['subject'])}, 0) .\n"
    run = subprocess.run(["maude", "-no-banner", "-no-wrap", "-no-advise"], input=script + "quit\n",
                         capture_output=True, text=True, check=True)
    out = run.stdout
    if "Warning" in run.stderr + out:
        raise SystemExit("match.py: Maude warnings:\n" + run.stderr + out)
    results = re.findall(r"result (?:SList|Substitution): (.*?)(?=\n={5,}|\nBye|\Z)", out, re.S)
    if len(results) != len(req["problems"]):
        raise SystemExit("match.py: unexpected Maude output:\n" + out)
    json.dump({"matches": [parse(r) for r in results]}, sys.stdout)


if __name__ == "__main__":
    main()
