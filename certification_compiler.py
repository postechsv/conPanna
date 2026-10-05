"""Untrusted rule-data compiler, with a resource-limited Maude/Lean demo wrapper.
The constructor translator does no unification, search, or Lean syntax evaluation.
--build caches general Lean proofs; --demo runs an explicit experimental pipeline.
Rule templates are restricted. Lean independently fixes and checks the goals.
Not a general ACU search engine or a production certificate loader.
"""
import json
import re
import sys

def number(x):
    if type(x) is not int or x < 0:
        raise ValueError("expected natural number")
    return str(x)

def scope(xs):
    return "[" + ", ".join("Tag.s" + number(x) for x in xs) + "]"

def position(x):
    x = int(number(x))
    return ".here" if x == 0 else "(.there " + position(x - 1) + ")"

def term(t):
    if "var" in t:
        return "(Term.var (sig := Sig) " + position(t["var"]) + ")"
    return "(Term.app (sig := Sig) Symbol.c" + number(t["app"]) + " " + terms(t["args"]) + ")"

def terms(ts):
    return ".nil" if not ts else "(.cons " + term(ts[0]) + " " + terms(ts[1:]) + ")"

def equations(es):
    return "[" + ", ".join("(equation (s := Tag.s" + number(e["sort"]) + ") "
        + term(e["left"]) + " " + term(e["right"]) + ")" for e in es) + "]"

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

def fact(f):
    if f == "rfl":
        return "rfl"
    if type(f) is dict and "or" in f and f["or"] in ("left", "right"):
        return "(Or.in" + ("l" if f["or"] == "left" else "r") + " rfl)"
    raise ValueError("unsupported finite fact")

def equality(e, context=None):
    if e["rule"] == "refl":
        return "(Equality.refl (sig := Sig) (Γ := " + scope(e["scope"] if context is None else context) + ") " + term(e["term"]) + ")"
    raise ValueError("unsupported equality rule")

def derives(d, context=None):
    if d["rule"] == "hyp":
        return "(.hyp " + fin(d["index"]) + ")"
    if d["rule"] == "axiom":
        return "(.axiom " + equality(d["equality"], context) + ")"
    raise ValueError("unsupported derivation rule")

def derives_args(ds, context):
    return ".nil" if not ds else "(.cons " + derives(ds[0], context) + " " + derives_args(ds[1:], context) + ")"

def slots(xs):
    return ".nil" if not xs else "(." + ("take" if xs[0] else "skip") + " " + slots(xs[1:]) + ")"

def sharing_fields(p, sound=False):
    counts = p["counts"]
    left, right = p["left"], p["right"]
    disjoint = [{"or": "left" if a == 0 else "right"} for a, b in zip(left, right)]
    if not all(a == 0 or b == 0 for a, b in zip(left, right)):
        raise ValueError("non-disjoint sharing")
    context_arg = "inputs" if sound else "Γ"
    return "(sig := Sig) (s := Tag.s" + number(p["sort"]) + ") (" + context_arg + " := " + scope(p["scope"]) + ") " +         "(n := " + number(len(left)) + ") (rows := " + number(len(p["rows"])) + ") (cols := " + number(len(p["cols"])) + ") " +         ("profile " if sound else "") + "Operator.acu " + slots(p["slots"]) + " " +         finite_values(left) + " " + finite_values(right) + " " + finite_values(p["rows"]) + " " + finite_values(p["cols"]) + " " +         finite_proofs(counts[0]) + " " + finite_proofs(counts[1]) + " " + finite_proofs(disjoint)

def complete(p):
    common = "" if p["rule"] == "sharing" else "(Γ := " + scope(p["scope"]) + ") (images := " + terms(p["images"]) + ") (eqs := " + equations(p["eqs"]) + ") "
    if p["rule"] == "bind":
        removal = "(" + position(p["remove"]) + " : Binding.Removal Tag.s" + number(p["sort"]) +             " " + scope(p["scope"]) + " " + scope(p["after"]) + ")"
        return "(.bind (sig := Sig) " + common + "(Δ := " + scope(p["after"]) + ") " + removal + " " +             term(p["replacement"]) + " " + derives(p["premise"], p["scope"]) + " " + complete(p["child"]) + ")"
    if p["rule"] == "cover":
        return "(.cover (sig := Sig) " + common + fin(p["index"]) + " " + terms(p["beta"]) + " " + derives_args(p["derived"], p["scope"]) + ")"
    if p["rule"] == "sharing":
        return "(.sharing " + sharing_fields(p) + " " + derives(p["premise"]) + " " + complete(p["child"]) + ")"
    raise ValueError("unsupported complete rule")

def sound_row(es):
    return ".nil" if not es else "(.cons " + equality(es[0]) + " " + sound_row(es[1:]) + ")"

def system_sound(rows):
    return ".nil" if not rows else "(.cons " + sound_row(rows[0]) + " " + system_sound(rows[1:]) + ")"

def declaration(name):
    if type(name) is not str or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", name) is None:
        raise ValueError("invalid declaration identifier")
    return name

def sound(p):
    if p["rule"] == "sharing":
        return "(.sharing " + sharing_fields(p, True) + " .nil)"
    if p["rule"] == "equalities":
        return sound_row(p["equalities"])
    raise ValueError("unsupported soundness rule")

def compile_proof(p):
    # These identifiers select DATA, not supporting certification lemmas.
    # The Lean consumer fixes its expected proposition independently of them.
    aggregate = {"system": "exact_system", "equation": "exact"}[p["aggregate"]]
    problem, answers = declaration(p["problem"]), declaration(p["answers"])
    sound_proof = system_sound(p["sound"]) if p["aggregate"] == "system" else sound(p["sound"])
    return "Worklist." + aggregate + " registration (profile := profile) " + problem + " " + answers +         "\n  " + complete(p["proof"]) + "\n  " + sound_proof

def run_checked(command, *, cwd, input_text=None, lean=False, allow_stale=False):
    """One child at a time. Never raise Lean limits to obtain a successful demo."""
    import subprocess
    import resource
    import os
    import signal
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (25, 25))
        if lean:
            resource.setrlimit(resource.RLIMIT_DATA, (768 * 1024**2, 768 * 1024**2))
    child = subprocess.Popen(command, cwd=cwd, text=True, stdin=subprocess.PIPE,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=limits,
        start_new_session=True)
    try:
        output, errors = child.communicate(input_text, timeout=30)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        child.communicate()
        raise RuntimeError("subprocess exceeded the 30s safety limit") from None
    messages = output + errors
    if allow_stale and child.returncode == 3:  # Lake's documented --no-build exit.
        return None
    if child.returncode or "Warning:" in messages or (lean and "sorryAx" in messages):
        raise RuntimeError(messages or f"subprocess failed: {child.returncode}")
    return output

def precompile(root):
    """Cache the unchanged general proofs, not the problem certificate."""
    import time
    cache = root / ".lake/build/certification"
    cache.mkdir(parents=True, exist_ok=True)
    # Let Lake validate dependency traces; do not implement a second build cache.
    ready = run_checked(["lake", "--no-build", "--no-cache", "build",
        "+conPanna.Certification.Replay:olean"], cwd=root, lean=True, allow_stale=True)
    if ready is not None:
        print("Certification backend: cached (Lake validated dependencies)", flush=True)
        return cache
    # Existing project dependencies must already be built (as in normal Lake use).
    # Explicit steps prevent independent backend modules compiling concurrently.
    for name in ("Core", "Sharing", "Enumeration", "Replay"):
        start = time.monotonic()
        # Lake creates .ilean and dependency traces needed by the editor.
        # --old avoids unrelated transitive rebuilds in this experiment.
        # The Certification library itself fixes -j1 -M512 in lakefile.toml.
        run_checked(["lake", "--old", "--no-cache", "build",
            f"+conPanna.Certification.{name}:olean"], cwd=root, lean=True)
        print(f"{name}: ready in {time.monotonic() - start:.2f}s", flush=True)
    return cache

def maude_run(root, commands):
    import os
    import shutil
    executable = os.environ.get("CONPANNA_MAUDE") or shutil.which("maude")
    if not executable:
        raise RuntimeError("Set CONPANNA_MAUDE or put maude on PATH")
    return run_checked([executable, "-no-banner", "-no-advise", "-no-wrap",
        str(root / "examples/certification-demo.maude")], cwd=root,
        input_text=commands + "\nquit\n")

def native_demo_answer(output):
    """Fixed DEMO grammar; unknown/multiple answers fail, never silently certify."""
    if len(re.findall(r"^Unifier \d+$", output, re.MULTILINE)) != 1:
        raise ValueError("demo expects exactly one proposed native unifier")
    pairs = re.findall(r"^(P:Bag|Q:Bag|N:Ticket) --> (.+)$", output, re.MULTILINE)
    bindings = dict(pairs)
    if len(pairs) != 3 or len(bindings) != 3:
        raise ValueError("unexpected native answer variables")
    parameter = bindings["N:Ticket"]
    if not re.fullmatch(r"#\d+:Ticket", parameter):
        raise ValueError("unexpected native ticket parameter")
    expected = f"singleton(wait({parameter}))"
    if bindings["P:Bag"] != expected or bindings["Q:Bag"] != expected:
        raise ValueError("native answer is outside this demo's input contract")
    # Transparent signature map: ticket=s0, bag=s2, wait=c3, singleton=c6.
    atom = {"app": 6, "args": [{"app": 3, "args": [{"var": 0}]}]}
    return [{"var": 0}, atom, atom]

def maude_term(t):
    if "var" in t:
        return "v(" + number(t["var"]) + ")"
    return "a(" + number(t["app"]) + "," + maude_terms(t["args"]) + ")"

def maude_terms(ts):
    return "nilT" if not ts else "t(" + maude_term(ts[0]) + "," + maude_terms(ts[1:]) + ")"

def demo(root):
    import time
    cache = precompile(root)
    start = time.monotonic()
    native = maude_run(root, "unify in BAKERY-DEMO-NATIVE : "
        "P:Bag =? Q:Bag /\\ Q:Bag =? singleton(wait(N:Ticket)) .")
    answer = native_demo_answer(native)
    print("Native answer: (n, P, Q) := (N, [wait(N)], [wait(N)])")
    command = "rew in BAKERY-DEMO-CERTIFIER : certify(" + \
        "c(0,c(2,c(2,nilC))),t(v(0),t(v(1),t(v(2),nilT)))," + \
        "e(eqn(2,v(1),v(2)),e(eqn(2,v(2),a(6,t(a(3,t(v(0),nilT)),nilT))),nilE))," + \
        "c(0,nilC)," + maude_terms(answer) + ") ."
    emitted = maude_run(root, command)
    match = re.search(r'result State: result\(("(?:[^"\\]|\\.)*")\)', emitted)
    if not match:
        raise ValueError("Maude did not close the certification derivation")
    trace = json.loads(json.loads(match.group(1)))
    print(f"Maude rule trace: {trace['proof']['rule']} -> "
        f"{trace['proof']['child']['rule']} -> {trace['proof']['child']['child']['rule']}")
    (cache / "demo.trace.json").write_text(json.dumps(trace, indent=2) + "\n")
    proof = compile_proof(trace)
    (cache / "demo.proof.lean").write_text(proof + "\n")
    print(f"Maude + Python: {time.monotonic() - start:.3f}s")
    start = time.monotonic()
    checked = run_checked(["lake", "env", "lean", "-j1", "-M512",
        "examples/certification-demo.lean"], cwd=root, lean=True)
    print(checked.rstrip())
    print(f"Lean consumer: {time.monotonic() - start:.2f}s (no backend recompilation)")
    print("CERTIFIED: soundness and completeness; no sorry")
    print("Inspect: examples/certification-demo.lean; .lake/build/certification/demo.trace.json")

def main():
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="precompile the general certificate library")
    parser.add_argument("--demo", action="store_true", help="run Maude -> Python -> Lean end to end")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if args.demo:
        demo(root)
    elif args.build:
        precompile(root)
    else:
        print(compile_proof(json.load(sys.stdin)))

if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError) as error:
        sys.exit(str(error))
