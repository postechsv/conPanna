#!/usr/bin/env python3
"""Run the Maude producer on a request and write a readable derivation.

  python3 producer/tools/derive.py producer/demo/l137.maude   # writes producer/demo/l137.deriv

A request is a Maude file whose last command is  red certify(...) .  (see
producer/demo/*.maude). The derivation is the rendered result of that command.
Untrusted: Lean checks whatever is later compiled from it.
"""
import pathlib, re, subprocess, sys

import config

HERE = pathlib.Path(__file__).resolve().parent
MAUDE = "maude"


def run_maude(request: pathlib.Path) -> str:
    """Return the string result of the request's  red certify(...)  command. With the
    producer option filter_unifiers (tools/config.py) the request runs against Maude's
    filtered unifiers instead (certifyFiltered)."""
    text = request.read_text()
    if config.filter_unifiers() and "red certify(" in text:
        # a copy next to the request, so that its relative loads still resolve
        copy = request.with_name(f".filtered-{request.name}")
        copy.write_text(text.replace("red certify(", "red certifyFiltered("))
        try:
            return run_maude_file(copy)
        finally:
            copy.unlink()
    return run_maude_file(request)


def run_maude_file(request: pathlib.Path) -> str:
    script = f"load {HERE.parent / 'lib' / 'show.maude'}\nload {request.resolve()}\nquit\n"
    out = subprocess.run([MAUDE, "-no-banner", "-no-wrap"], input=script.encode(),
                         capture_output=True, check=True).stdout.decode("utf-8")
    warnings = re.findall(r"Warning.*", out)
    if warnings:
        raise SystemExit("Maude warnings:\n" + "\n".join(warnings))
    m = re.search(r'result String: "(.*)"\s*$', out.split("Bye")[0].strip(), re.S)
    if not m:
        raise SystemExit("no derivation in Maude output:\n" + out)
    raw = m.group(1)
    # Maude escapes newlines, quotes and non-ASCII bytes (∅ is \342\210\205).
    raw = re.sub(r"\\([0-7]{3})", lambda b: chr(int(b.group(1), 8)), raw)
    raw = raw.replace("\\n", "\n").replace('\\"', '"')
    return raw.encode("latin-1").decode("utf-8")


def main() -> None:
    for arg in sys.argv[1:]:
        request = pathlib.Path(arg)
        if "certify" not in request.read_text():
            continue  # not a request (e.g. a models file)
        text = run_maude(request)
        target = request.with_suffix(".deriv")
        target.write_text(text)
        print(f"== {target}\n{text}")


if __name__ == "__main__":
    main()
