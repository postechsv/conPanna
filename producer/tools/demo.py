#!/usr/bin/env python3
"""Run demos end to end: Maude derivation, compilation to Lean, and Lean's check.

  python3 producer/tools/demo.py mixed enter      # or: all
  python3 producer/tools/demo.py --dir producer/tests/pipeline all

For a demo NAME it uses DIR/NAME.maude (request) and NAME.claim.lean (the user's
claim), and writes NAME.deriv and NAME.lean. DIR defaults to producer/demo.
Run from the repository root.
"""
import pathlib, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parents[2]
DEMO = ROOT / "producer" / "demo"
TOOLS = ROOT / "producer" / "tools"


def step(title, cmd):
    t = time.time()
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    dt = time.time() - t
    return r, dt


def run(name, DEMO):
    print(f"== {name}")
    r, dt = step("derive", [sys.executable, str(TOOLS / "derive.py"), str(DEMO / f"{name}.maude")])
    if r.returncode:
        print(r.stdout + r.stderr); return False
    deriv = (DEMO / f"{name}.deriv").read_text()
    print(f"   Maude derivation  {dt:6.2f}s  -> {name}.deriv")
    stuck = [l.strip() for l in deriv.splitlines() if "STUCK" in l]
    if stuck:
        print(f"   no certificate: {stuck[0]}")
        return False
    claim = DEMO / f"{name}.claim.lean"
    if not claim.exists():
        print(f"   (no {claim.name}; nothing to compile)"); return True
    r, dt = step("compile", [sys.executable, str(TOOLS / "compile.py"), str(claim), str(DEMO / f"{name}.deriv")])
    if r.returncode:
        print(r.stdout + r.stderr); return False
    print(f"   compiled          {dt:6.2f}s  -> {name}.lean")
    r, dt = step("check", ["lake", "env", "lean", str(DEMO / f"{name}.lean")])
    errors = [l for l in (r.stdout + r.stderr).splitlines() if ": error" in l]
    if r.returncode or errors:
        print("\n".join(errors[:10]) or r.stdout + r.stderr); return False
    print(f"   Lean check        {dt:6.2f}s  ok")
    return True


def main():
    args = sys.argv[1:]
    demo = DEMO
    if args[:1] == ["--dir"]:
        demo, args = ROOT / args[1], args[2:]
    names = args or ["all"]
    if names == ["all"]:
        names = sorted(p.stem for p in demo.glob("*.maude") if p.stem != "models")
    results = {n: run(n, demo) for n in names}
    print("\n" + "  ".join(f"{n}: {'ok' if ok else 'no certificate'}" for n, ok in results.items()))


if __name__ == "__main__":
    main()
