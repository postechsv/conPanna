#!/usr/bin/env python3
"""Convert a UDF certificate to a Lean `Cert` literal (doability test of reflection).

  python3 udf2lean.py CERT.udf NAME > out.lean
"""
import re, sys


def parse(text):
    text = re.sub(r";[^\n]*", "", text)
    toks = re.findall(r"\(|\)|[^\s()]+", text)
    pos = 0

    def item():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t != "(":
            return t
        out = []
        while toks[pos] != ")":
            out.append(item())
        pos += 1
        return out

    out = []
    while pos < len(toks):
        out.append(item())
    return out


def main():
    forms = parse(open(sys.argv[1]).read())
    name = sys.argv[2]
    ops, acus, ident, names = {}, {}, {}, {}

    def var(n):
        return names.setdefault(n, len(names))

    for f in forms:
        if f[0] == "signature":
            for d in f[1:]:
                if d[0] == "op":
                    ops[d[1]] = len(ops)
                elif d[0] == "acu":
                    acus[d[1]] = len(acus)
                    ident[d[3]] = d[1]
                elif d[0] == "var":
                    var(d[1])
    probvars = list(names.values())

    def term(t):
        if isinstance(t, str):
            if t in ident:
                return f"(.acu {acus[ident[t]]} [])"
            if t in ops:
                return f"(.app {ops[t]} [])"
            return f"(.var {var(t)})"
        args = ", ".join(term(a) for a in t[1:])
        if t[0] in acus:
            return f"(.acu {acus[t[0]]} [{args}])"
        return f"(.app {ops[t[0]]} [{args}])"

    def kw(st, k):
        return st[st.index(k) + 1]

    problem, answers, anames, steps = [], [], {}, {}
    for f in forms:
        if f[0] == "problem":
            problem = [f"({term(e[1])}, {term(e[2])})" for e in f[1:]]
        elif f[0] == "answers":
            for u in f[1:]:
                anames[u[1]] = len(answers)
                answers.append("[" + ", ".join(f"({var(b[1])}, {term(b[2])})" for b in u[3:]) + "]")
        elif f[0] == "step":
            steps[f[1]] = f
    ids = {s: i for i, s in enumerate(steps)}
    out = []
    for s, st in steps.items():
        rule = st[2]
        ps = [ids[p] for p in kw(st, ":premises")]
        if rule in ("delete", "decomp"):
            out.append(f".{rule} {kw(st, ':eq')} {ps[0]}")
        elif rule in ("clash", "ground"):
            out.append(f".{rule} {kw(st, ':eq')}")
        elif rule == "elim":
            out.append(f".elim {kw(st, ':eq')} {var(kw(st, ':var'))} {ps[0]}")
        elif rule == "cover":
            w = ", ".join(f"({var(a)}, {term(b)})" for a, b in kw(st, ":witness"))
            out.append(f".cover {anames[kw(st, ':answer')]} [{w}]")
        elif rule == "acu-solve":
            unk = ", ".join(term(u) for u in kw(st, ":unknowns"))
            alien = ", ".join("true" if b == "1" else "false" for b in kw(st, ":bounds"))
            rows = ", ".join("[" + ", ".join(f"({c} : Int)" for c in r) + "]" for r in kw(st, ":rows"))
            basis = ", ".join("[" + ", ".join(v) + "]" for v in kw(st, ":basis"))
            sels = ", ".join(f"([{', '.join(sl[1])}], [{', '.join(str(var(z)) for z in sl[3])}])"
                             for sl in kw(st, ":selections"))
            out.append(f".acu {acus[kw(st, ':op')]} [{', '.join(kw(st, ':eqs'))}] [{unk}] [{alien}] "
                       f"[{rows}] [{basis}] [{sels}] {ps}")
        else:
            raise SystemExit(f"rule {rule} not supported")
    print(f"def {name} : Cert where\n  problem := [{', '.join(problem)}]\n  vars := {probvars}\n"
          f"  answers := [{', '.join(answers)}]\n  steps := [\n    " + ",\n    ".join(out) + "]\n")


if __name__ == "__main__":
    main()
