#!/usr/bin/env python3
"""Regression test of the producer: extract a UDF derivation for every test problem.

  python3 producer/tools/test_udf.py [dir ...]      # default: every directory of producer/tests

A problem is a file `NAME.maude` next to the model `models.maude`, stating
`red certify('MODULE, …, lhs, rhs) .` (a system: `eqn(lhs, rhs) ;; …` as its last
argument); only the module and the equations are read. For each, trace_to_udf.py runs the
instrumented Maude and extracts the derivation; the problem passes when every leaf is a
unifier and is covered by one of Maude's filtered unifiers. Lean is not involved.
"""
import pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import trace_to_udf  # noqa: E402

TESTS = HERE.parent / "tests"


def split_top(s):
    """Split at commas outside brackets (backquote escapes a character)."""
    out, depth, cur, esc = [], 0, "", False
    for ch in s:
        if esc or ch == "`":
            esc = not esc
            cur += ch
            continue
        if ch in "([":
            depth += 1
        if ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
            continue
        cur += ch
    return out + [cur.strip()]


def problem(text):
    """(module, [(lhs, rhs), ...]) of a request, or None."""
    m = re.search(r"red certify\((.*)\)\s*\.\s*$", text, re.S)
    if not m:
        return None
    args = split_top(m.group(1))
    module = args[0].lstrip("'")
    if args[-1].startswith("eqn("):
        eqs = [split_top(re.match(r"eqn\((.*)\)$", e.strip(), re.S).group(1)) for e in args[-1].split(";;")]
        return module, [tuple(e) for e in eqs]
    return module, [(args[-2], args[-1])]


def main():
    dirs = [pathlib.Path(d) for d in sys.argv[1:]] or sorted(p for p in TESTS.iterdir() if p.is_dir())
    total, failed, leaves, from_trace = 0, [], 0, 0
    for d in dirs:
        for req in sorted(d.glob("*.maude")):
            if req.name == "models.maude":
                continue
            p = problem(req.read_text())
            if not p:
                continue
            total += 1
            name = f"{d.name}/{req.stem}"
            try:
                _, st = trace_to_udf.extract(str((d / "models.maude").resolve()), *p)
                leaves += st["leaves"]
                from_trace += st["from_trace"]
                if not st["leaves"] == st["unifiers"] == st["covered"]:
                    failed.append((name, {k: v for k, v in st.items() if k != "answer_terms"}))
            except Exception as e:
                failed.append((name, f"{type(e).__name__}: {str(e)[:150]}"))
    print(f"{total} problems, {total - len(failed)} ok; witnesses from the trace: {from_trace} of {leaves} leaves")
    for name, why in failed:
        print("  FAIL", name, why)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
