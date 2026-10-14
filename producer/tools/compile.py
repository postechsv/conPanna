#!/usr/bin/env python3
"""Compile a derivation into a Lean certificate.

  python3 producer/tools/compile.py producer/demo/mixed.claim.lean producer/demo/mixed.deriv
      # writes producer/demo/mixed.lean

The claim file is the user's Lean file (model, problem) with a `/- certify {...} -/`
header giving the namespace, the Lean type of the original variables (`context`),
their order (`vars`) and the Lean counterparts of the Maude operators (`ops`; a
template with `{0}`, `{1}` is filled with the arguments). The compiler appends the
answers and a proof that applies one calculus rule per derivation line. It makes no
decisions: every rule and datum comes from the derivation, and the obligations are
closed by the fixed tactics of Certification/Tactics.lean. Untrusted: Lean checks
the output.

After each SOLVE the compiler unpacks the fresh block `Z : Fin k → ACU` into named
variables (`rename`), so every context is a flat tuple of names.
"""
import json
import pathlib
import re
import sys
from dataclasses import dataclass, field
from itertools import combinations

# ----------------------------------------------------------------------------- terms


@dataclass
class Var:
    name: str


@dataclass
class App:
    op: str
    args: list


@dataclass
class Sum:
    parts: list          # summands; an element summand is Elem


@dataclass
class Elem:
    term: object


EMPTY = Sum([])


class Parser:
    """Terms as printed by show.maude: prefix applications, bags `t + {a}`, `∅`."""

    def __init__(self, text):
        self.s, self.i = text, 0

    def peek(self, k=1):
        return self.s[self.i:self.i + k]

    def skip(self):
        while self.peek() == " ":
            self.i += 1

    def eat(self, tok):
        self.skip()
        if not self.s.startswith(tok, self.i):
            raise SyntaxError(f"expected {tok!r} at {self.s[self.i:]!r}")
        self.i += len(tok)

    def term(self):
        parts = [self.summand()]
        while self.s.startswith(" + ", self.i):
            self.i += 3
            parts.append(self.summand())
        return parts[0] if len(parts) == 1 and not isinstance(parts[0], Elem) else Sum(parts)

    def summand(self):
        self.skip()
        if self.peek() == "{":
            self.eat("{")
            t = self.term()
            self.eat("}")
            return Elem(t)
        return self.atom()

    def atom(self):
        self.skip()
        if self.peek() == "∅":
            self.i += 1
            return EMPTY
        if self.peek() == '"':
            j = self.s.index('"', self.i + 1)
            name, self.i = self.s[self.i + 1:j], j + 1
        else:
            m = re.compile(r"[A-Za-z0-9#%_'.!?-]+").match(self.s, self.i)
            if not m:
                raise SyntaxError(f"bad term at {self.s[self.i:]!r}")
            name, self.i = m.group(0), m.end()
        if self.peek() == "(":
            self.eat("(")
            args = [self.term()]
            while self.peek() == ",":
                self.eat(",")
                args.append(self.term())
            self.eat(")")
            return App(name, args)
        if is_var(name):
            return Var(name)
        return App(name, [])


def is_var(name):
    return name.endswith("?") or name.endswith("!") or re.fullmatch(r"Z\d+", name) is not None


def parse_term(text):
    p = Parser(text.strip())
    t = p.term()
    p.skip()
    if p.i != len(p.s):
        raise SyntaxError(f"trailing text {p.s[p.i:]!r}")
    return t


def split_top(text, sep):
    """Split at `sep` outside parentheses and braces."""
    out, depth, cur, i = [], 0, "", 0
    while i < len(text):
        if text.startswith(sep, i) and depth == 0:
            out.append(cur)
            cur, i = "", i + len(sep)
            continue
        c = text[i]
        depth += c in "({"
        depth -= c in ")}"
        cur += c
        i += 1
    out.append(cur)
    return [x.strip() for x in out if x.strip()]


def parse_eqs(text):
    return [] if text.strip() == "-" else [tuple(parse_term(x) for x in split_top(e, " = "))
                                            for e in split_top(text, "; ")]


def parse_sub(text):
    if text.strip() == "-":
        return {}
    return {b.split(" := ")[0].strip(): parse_term(b.split(" := ", 1)[1])
            for b in split_top(text, ", ")}


def free_vars(t, acc=None):
    acc = set() if acc is None else acc
    if isinstance(t, Var):
        acc.add(t.name)
    elif isinstance(t, App):
        for a in t.args:
            free_vars(a, acc)
    elif isinstance(t, Sum):
        for a in t.parts:
            free_vars(a, acc)
    elif isinstance(t, Elem):
        free_vars(t.term, acc)
    return acc


# ----------------------------------------------------------------------------- derivations


@dataclass
class Node:
    rule: str
    judgment: tuple = None          # (alpha, eqs, diseqs)
    data: dict = field(default_factory=dict)
    children: list = field(default_factory=list)


def indent_of(line):
    return (len(line) - len(line.lstrip(" "))) // 2


def parse_derivation(text):
    lines = text.splitlines()
    answers, k = [], lines.index("answers") + 1
    while not lines[k].startswith("derivation"):
        idx, sub = lines[k].strip().split(": ", 1)
        answers.append(parse_sub(sub))
        k += 1
    body = lines[k + 1:]
    node, _ = parse_seq(body, 0, 1)
    return answers, node


def parse_judgment(line):
    alpha, eqs, dis = [x.strip() for x in line.strip()[1:].split(" | ")]
    return parse_sub(alpha), parse_eqs(eqs), parse_eqs(dis.replace(" =/= ", " = "))


def parse_seq(lines, i, ind):
    judgment = parse_judgment(lines[i])
    rule_line = lines[i + 1].strip()
    word, _, rest = rule_line.partition(" ")
    i += 2
    if word in ("delete", "decomp", "elim"):
        child, i = parse_seq(lines, i, ind)
        data = {}
        if word == "elim":
            v, t = rest.split(" := ", 1)
            data = {"var": v, "term": parse_term(t)}
        return Node(word, judgment, data, [child]), i
    if word == "identify":
        a, b = split_top(rest, " ~ ")
        assert lines[i].strip() == "equal:"
        eq, i = parse_seq(lines, i + 1, ind + 2)
        assert lines[i].strip() == "distinct:"
        ne, i = parse_seq(lines, i + 1, ind + 2)
        return Node("identify", judgment, {"a": parse_term(a), "b": parse_term(b)}, [eq, ne]), i
    if word == "solve":
        info = dict(parse_solve_line(lines[i]) | parse_solve_line(lines[i + 1]))
        i += 2
        branches = []
        if lines[i].strip() == "no choice":
            i += 1
        else:
            while i < len(lines) and indent_of(lines[i]) == ind + 1 and lines[i].strip().startswith("branch "):
                head = lines[i].strip()[len("branch "):]
                pi, theta = head.split("]: ", 1)
                sub, i = parse_seq(lines, i + 1, ind + 2)
                branches.append((parse_vecs(pi + "]"), parse_sub(theta), sub))
        info["branches"] = branches
        return Node("solve", judgment, info, [b[2] for b in branches]), i
    if word == "cover":
        m = re.match(r"answer (\d+) with (.*)", rest)
        return Node("cover", judgment, {"answer": int(m.group(1)), "witness": parse_sub(m.group(2))}), i
    if word in ("clash", "occurs", "distinct"):
        return Node(word, judgment), i
    raise SystemExit(f"cannot compile rule line: {rule_line}")


def parse_vec(text):
    text = text.strip()[1:-1]
    return [int(x) for x in text.split(",")] if text else []


def parse_vecs(text):
    return [parse_vec(v) for v in re.findall(r"\([0-9,]*\)", text)]


def parse_solve_line(line):
    out = {}
    for part in [p.strip() for p in line.strip().split(" | ")]:
        key, _, val = part.partition(" ")
        if key == "vars":
            out["vars"] = [] if val == "-" else val.split()
        elif key == "aliens":
            out["aliens"] = [] if val == "-" else [parse_term(x) for x in split_top(val, " ")]
        elif key == "L":
            m = re.match(r"(\(.*?\)) R (\(.*?\)) La (\(.*?\)) Ra (\(.*?\))", val)
            out["L"], out["R"], out["La"], out["Ra"] = (parse_vec(m.group(j)) for j in range(1, 5))
        elif key == "compatible":
            out["compatible"] = [] if val == "-" else [tuple(map(int, p.split("~"))) for p in val.split()]
        elif key == "P":
            out["P"] = [] if val == "-" else [parse_vecs(c) for c in re.findall(r"\[[^\]]*\]", val)]
        elif key == "B":
            out["B"] = parse_vecs(val)
    return out


# ----------------------------------------------------------------------------- Lean output


def pattern(ctx, used=None):
    """A lambda pattern for a flat context; unused names become `_`."""
    names = [x if used is None or x in used else "_" for x in ctx]
    if not names:
        return "_"
    return names[0] if len(names) == 1 else "(" + ", ".join(names) + ")"


def tuple_term(items):
    if not items:
        return "()"
    return items[0] if len(items) == 1 else "(" + ", ".join(items) + ")"


class Compiler:
    """Contexts are flat lists of variable names (`X?`, `Z3`, ...)."""

    def __init__(self, cfg):
        self.cfg, self.ops = cfg, cfg.get("ops", {})
        self.out = []

    # terms -----------------------------------------------------------------
    def lean(self, t):
        if isinstance(t, Var):
            return t.name
        if isinstance(t, Sum):
            if not t.parts:
                return "∅"
            return " + ".join(self.lean(p) for p in t.parts)
        if isinstance(t, Elem):
            return "{" + self.lean(t.term) + "}"
        args = [self.lean(a) for a in t.args]
        lean_op = self.ops.get(t.op)
        if lean_op is None:
            raise SystemExit(f"no Lean name for Maude operator {t.op!r}; add it to ops")
        if "{0}" in lean_op:
            return lean_op.format(*[paren(a) for a in args])
        return " ".join([lean_op] + [paren(a) for a in args]) if args else lean_op

    def eq(self, e):
        return f"{self.lean(e[0])} = {self.lean(e[1])}"

    def conj(self, eqs):
        return " ∧ ".join(self.eq(e) for e in eqs) if eqs else "True"

    def lam(self, ctx, body):
        used = set(re.findall(r"[A-Za-z0-9_]+[?!]?", body))
        return f"fun {pattern(ctx, used)} => {body}"

    # output ----------------------------------------------------------------
    def emit(self, ind, text):
        for line in text.splitlines():
            self.out.append("  " * ind + line)

    def node(self, n, ctx, ind, at_start=False):
        a, eqs, dis = n.judgment
        alpha = ", ".join(f"{k} := {self.lean(t)}" for k, t in a.items()) or "-"
        self.emit(ind, f"-- ⊢ {alpha} | {'; '.join(self.eq(e) for e in eqs) or '-'}"
                       f" | {'; '.join(self.eq(e).replace(' = ', ' ≠ ') for e in dis) or '-'}")
        if n.rule in ("decomp", "delete"):
            nxt = n.children[0]
            self.emit(ind, f"-- {n.rule} {self.eq(eqs[0])}")
            self.emit(ind, f"refine decomp ({self.lam(ctx, self.conj(nxt.judgment[1]))})")
            self.emit(ind + 2, f"(fun {pattern(ctx)} h => by acu_free [problem]) ?_")
            self.node(nxt, ctx, ind)
        elif n.rule == "elim":
            v, t = n.data["var"], self.lean(n.data["term"])
            new = [x for x in ctx if x != v]
            nxt = n.children[0]
            self.emit(ind, f"-- elim {v} := {t}")
            self.emit(ind, f"refine elim (fun {pattern(new)} => {tuple_term([t if x == v else x for x in ctx])})")
            self.emit(ind + 2, f"({self.lam(new, self.conj(nxt.judgment[1]))})")
            self.emit(ind + 2, f"(fun {pattern(ctx)} h => ⟨{tuple_term(new)}, by acu_free [problem], "
                               f"by acu_free [problem]⟩) ?_")
            self.node(nxt, new, ind)
        elif n.rule == "identify":
            aa, bb = self.lean(n.data["a"]), self.lean(n.data["b"])
            self.emit(ind, f"-- identify {aa} ~ {bb}")
            self.emit(ind, f"refine identify ({self.lam(ctx, aa)}) ({self.lam(ctx, bb)}) ?_ ?_")
            self.emit(ind, "· -- equal:")
            self.node(n.children[0], ctx, ind + 1)
            self.emit(ind, "· -- distinct:")
            self.node(n.children[1], ctx, ind + 1)
        elif n.rule == "solve":
            self.solve(n, ctx, ind, at_start)
        elif n.rule == "cover":
            self.cover(n, ctx, ind)
        else:  # clash, occurs, distinct
            self.emit(ind, f"-- {n.rule}")
            self.emit(ind, f"exact clash fun {pattern(ctx)} h hD => by acu_free [problem]")

    def solve(self, n, ctx, ind, at_start):
        d = n.data
        eqs = n.judgment[1]
        solved, remaining = eqs[0], eqs[1:]
        bag = d["vars"]
        rest = [x for x in ctx if x not in bag]
        m = len(d["aliens"])
        vec = lambda xs: "![" + ", ".join(str(x) for x in xs) + "]"
        aliens = "![" + ", ".join(self.lean(a) for a in d["aliens"]) + "]"
        if d["compatible"]:
            cp = "fun c c' => " + " || ".join(f"(c == {i} && c' == {j}) || (c == {j} && c' == {i})"
                                             for i, j in d["compatible"])
        else:
            cp = "fun _ _ => false"
        P = "![" + ", ".join("[" + ", ".join(vec(p) for p in ps) + "]" for ps in d["P"]) + "]"
        B = "![" + ", ".join(vec(b) for b in d["B"]) + "]"
        compat = set(d["compatible"]) | {(j, i) for i, j in d["compatible"]}
        cliques = [list(g) for r in range(1, m + 1) for g in combinations(range(m), r)
                   if all((i, j) in compat for i, j in combinations(g, 2))]
        unfold = "try simp only [State.start, Problem.unifies, problem] at h; "
        if remaining:
            hE = f"⟨by {unfold}acu_side h.1, h.2, by acu_distinct⟩"
        else:
            hE = f"⟨by {unfold}acu_side h, trivial, by acu_distinct⟩"
        glue = tuple_term([f"V {bag.index(x)}" if x in bag else x for x in ctx])
        self.emit(ind, f"-- solve {self.eq(solved)}")
        self.emit(ind, f"refine solve (V := {self.lam(ctx, vec(bag))}) (rest := {self.lam(ctx, tuple_term(rest))})")
        self.emit(ind + 2, f"(glue := fun {pattern(rest)} V => {glue}) (hglue := fun _ => rfl)")
        self.emit(ind + 2, f"(a := {self.lam(rest, aliens)}) (L := {vec(d['L'])}) (R := {vec(d['R'])})"
                           f" (La := {vec(d['La'])}) (Ra := {vec(d['Ra'])})")
        self.emit(ind + 2, f"(E' := {self.lam(ctx, self.conj(remaining))}) (cp := {cp})")
        self.emit(ind + 2, f"(P := {P}) (B := {B})")
        self.emit(ind + 2, f"(fun {pattern(ctx)} h hD => {hE})")
        self.emit(ind + 2, "(by decide) (by decide) (by decide)")
        self.emit(ind + 2, f"(S2_of_list _ _ _ _ _ _ {cliques} (by decide) (by acu_cliques))"
                           f" (by acu_basis) ?_")
        branches = d["branches"]
        self.emit(ind, "intro π hπ; simp [choices] at hπ" + (
            "" if not branches else "; subst hπ" if len(branches) == 1
            else "; rcases hπ with " + " | ".join(["rfl"] * len(branches))))
        k = len(d["B"])
        fresh = sorted({int(x[1:]) for _, th, _ in branches for t in th.values()
                        for x in free_vars(t) if re.fullmatch(r"Z\d+", x)})
        if branches and len(fresh) != k:
            raise SystemExit(f"compile.py: expected {k} fresh variables, found {fresh}")
        names = [f"Z{j}" for j in fresh]
        inner = rest + names
        for pi, theta, sub in branches:
            sub_ind = ind + 1 if len(branches) > 1 else ind
            label = "branch " + " ".join("(" + ",".join(map(str, p)) + ")" for p in pi)
            self.emit(ind, f"· -- {label}" if len(branches) > 1 else f"-- {label}")
            # Lean bookkeeping: unpack the fresh block Z : Fin k → ACU into Z_i names.
            cases = ("fun i => i.elim0" if k == 0 else
                     "fun i => by fin_cases i; rfl" if k == 1 else "fun i => by fin_cases i <;> rfl")
            self.emit(sub_ind, f"refine rename (fun {pattern(inner)} => ({tuple_term(rest)}, {vec(names)}))")
            self.emit(sub_ind + 2, f"(fun ({pattern(rest)}, Z) => {tuple_term(rest + [f'Z {j}' for j in range(k)])})")
            self.emit(sub_ind + 2, f"(fun ({pattern(rest)}, Z) => Prod.ext rfl (funext {cases})) ?_")
            self.node(sub, inner, sub_ind)

    def cover(self, n, ctx, ind):
        i, w = n.data["answer"], n.data["witness"]
        binders = self.binders[i]
        wit = [self.lean(w[b]) for b in binders]
        self.emit(ind, f"-- cover answer {i} with " + ", ".join(f"{b} := {wit[j]}" for j, b in enumerate(binders)))
        wtext = tuple_term(wit) if wit else None
        proof = f"⟨{wtext}, by acu_cover⟩" if wtext else "by acu_cover"
        self.emit(ind, f"exact cover answer{i} (by simp [answers]) fun {pattern(ctx)} _ _ => {proof}")

    # answers ---------------------------------------------------------------
    def answers(self, answers):
        ctx_type, order = self.cfg["context"], self.cfg["vars"]
        self.binders, names = [], []
        for i, a in enumerate(answers):
            bs = sorted({x for t in a.values() for x in free_vars(t) if x.endswith("!")},
                        key=lambda x: int(x[1:-1]))
            self.binders.append(bs)
            body = ".subst ⟨" + ", ".join(self.lean(a[v]) for v in order) + "⟩"
            if bs:
                body = f".bind fun {bs[0] if len(bs) == 1 else '(' + ', '.join(bs) + ')'} => {body}"
            self.out.append(f"def answer{i} : Unifier ({ctx_type}) :=\n  {body}")
            names.append(f"answer{i}")
        self.out.append(f"def answers : UnifierSet ({ctx_type}) :=\n  [{', '.join(names)}]")


def paren(s):
    return s if re.fullmatch(r"[A-Za-z0-9_.?!']+|\(.*\)|\{.*\}", s) else f"({s})"


def main():
    claim_path, deriv_path = map(pathlib.Path, sys.argv[1:3])
    claim = claim_path.read_text()
    m = re.search(r"/- certify\s*(\{.*?\})\s*-/", claim, re.S)
    if not m:
        raise SystemExit("claim file has no /- certify {...} -/ header")
    cfg = json.loads(m.group(1))
    answers, root = parse_derivation(deriv_path.read_text())
    c = Compiler(cfg)
    c.out.append(f"/-! ## Generated from {deriv_path.name} by producer/tools/compile.py -/\n")
    c.answers(answers)
    c.out.append("")
    c.out.append("theorem complete : UnifierSet.Complete problem answers := by")
    c.emit(1, "rw [← start_iff]")
    ctx = list(cfg["vars"])
    eqs = root.judgment[1]
    if len(eqs) > 1:
        # The Lean claim states a system as one equation between tuples; split it.
        c.emit(1, "-- decomp of the tuple equation into the system")
        c.emit(1, f"refine decomp ({c.lam(ctx, c.conj(eqs))})")
        c.emit(3, f"(fun {pattern(ctx)} h => by acu_free [problem]) ?_")
    c.node(root, ctx, 1, at_start=len(eqs) == 1)
    c.out.append(f"\nend {cfg['namespace']}\n")
    target = deriv_path.with_suffix(".lean")
    target.write_text(claim.rstrip() + "\n\n" + "\n".join(c.out))
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
