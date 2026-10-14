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

Current limits: SOLVE must solve the last pending equation of the state, and its bag
variables must not be fresh variables of an earlier SOLVE.
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


class Ctx:
    """The Lean context of a state: a tree of variable names and fresh-variable blocks."""

    def __init__(self, items):
        self.items = items              # str (variable) | ("Z", block name, [indices]) | Ctx

    def pattern(self, used=None):
        parts = [item_pattern(x, used) for x in self.items]
        if not parts:
            return "_"
        return parts[0] if len(parts) == 1 else "(" + ", ".join(parts) + ")"

    def term(self):
        return self.pattern()

    def flat(self):
        out = []
        for x in self.items:
            out += x.flat() if isinstance(x, Ctx) else ([x] if isinstance(x, str) else [])
        return out

    def blocks(self):
        out = []
        for x in self.items:
            out += x.blocks() if isinstance(x, Ctx) else ([x] if isinstance(x, tuple) else [])
        return out

    def without(self, var):
        return Ctx([x.without(var) if isinstance(x, Ctx) else x for x in self.items if x != var])

    def replaced(self, var, text):
        return Ctx([x.replaced(var, text) if isinstance(x, Ctx) else (text if x == var else x)
                    for x in self.items])


def item_pattern(x, used):
    if isinstance(x, Ctx):
        return x.pattern(used)
    if isinstance(x, tuple):
        return x[1] if used is None or x[1] in used else "_"
    return x if used is None or x in used or x.startswith("(") else "_"


class Compiler:
    def __init__(self, cfg):
        self.cfg, self.ops = cfg, cfg.get("ops", {})
        self.out = []
        self.blocks = 0

    # terms -----------------------------------------------------------------
    def lean(self, t, ctx=None, named=False):
        if isinstance(t, Var):
            m = re.fullmatch(r"Z(\d+)", t.name)
            if m and not named and ctx is not None:
                for _, blk, idx in ctx.blocks():
                    if int(m.group(1)) in idx:
                        return f"{blk} {idx.index(int(m.group(1)))}"
            return t.name
        if isinstance(t, Sum):
            if not t.parts:
                return "∅"
            return " + ".join(self.lean(p, ctx, named) for p in t.parts)
        if isinstance(t, Elem):
            return "{" + self.lean(t.term, ctx, named) + "}"
        args = [self.lean(a, ctx, named) for a in t.args]
        lean_op = self.ops.get(t.op)
        if lean_op is None:
            raise SystemExit(f"no Lean name for Maude operator {t.op!r}; add it to ops")
        if "{0}" in lean_op:
            return lean_op.format(*[paren(a) for a in args])
        return " ".join([lean_op] + [paren(a) for a in args]) if args else lean_op

    def eq(self, e, ctx, named=False):
        return f"{self.lean(e[0], ctx, named)} = {self.lean(e[1], ctx, named)}"

    def conj(self, eqs, ctx):
        return " ∧ ".join(self.eq(e, ctx) for e in eqs) if eqs else "True"

    def lam(self, ctx, body, extra=""):
        used = set(re.findall(r"[A-Za-z0-9_]+[?!]?", body))
        return f"fun {ctx.pattern(used)}{extra} => {body}"

    # output ----------------------------------------------------------------
    def emit(self, ind, text):
        for line in text.splitlines():
            self.out.append("  " * ind + line)

    def node(self, n, ctx, ind, at_start=False):
        a, eqs, dis = n.judgment
        alpha = ", ".join(f"{k} := {self.lean(t, None, True)}" for k, t in a.items()) or "-"
        self.emit(ind, f"-- ⊢ {alpha} | {'; '.join(self.eq(e, None, True) for e in eqs) or '-'}"
                       f" | {'; '.join(self.eq(e, None, True).replace(' = ', ' ≠ ') for e in dis) or '-'}")
        if n.rule in ("decomp", "delete"):
            nxt = n.children[0]
            self.emit(ind, f"-- {n.rule} {self.eq(eqs[0], None, True)}")
            self.emit(ind, f"refine decomp ({self.lam(ctx, self.conj(nxt.judgment[1], ctx))})")
            self.emit(ind + 2, f"(fun {ctx.pattern()} h => by acu_free [problem]) ?_")
            self.node(nxt, ctx, ind)
        elif n.rule == "elim":
            v, t = n.data["var"], n.data["term"]
            new = ctx.without(v)
            nxt = n.children[0]
            self.emit(ind, f"-- elim {v} := {self.lean(t, None, True)}")
            self.emit(ind, f"refine elim (fun {new.pattern()} => {ctx.replaced(v, self.lean(t, new)).term()})")
            self.emit(ind + 2, f"({self.lam(new, self.conj(nxt.judgment[1], new))})")
            self.emit(ind + 2, f"(fun {ctx.pattern()} h => ⟨{new.term()}, by acu_free [problem], "
                               f"by acu_free [problem]⟩) ?_")
            self.node(nxt, new, ind)
        elif n.rule == "identify":
            aa, bb = self.lean(n.data["a"], ctx), self.lean(n.data["b"], ctx)
            self.emit(ind, f"-- identify {self.lean(n.data['a'], None, True)} ~ {self.lean(n.data['b'], None, True)}")
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
            self.emit(ind, f"exact clash fun {ctx.pattern()} h hD => by acu_free [problem]")

    def solve(self, n, ctx, ind, at_start):
        d = n.data
        eqs = n.judgment[1]
        if len(eqs) != 1:
            raise SystemExit("compile.py: SOLVE on a state with other pending equations is not supported yet")
        flat = ctx.flat()
        bag = d["vars"]
        if any(v not in flat for v in bag):
            raise SystemExit("compile.py: SOLVE on fresh variables of an earlier SOLVE is not supported yet")
        rest = Ctx([x for x in ctx.items if x not in bag]) if all(not isinstance(x, Ctx) for x in ctx.items) \
            else Ctx([x for x in ctx.items if x not in bag])
        m, k = len(d["aliens"]), len(d["B"])
        restp = rest.pattern() if rest.items else "_"
        restt = rest.term() if rest.items else "()"
        glue_items = Ctx([f"V {bag.index(x)}" if x in bag else x for x in ctx.items])
        vec = lambda xs: "![" + ", ".join(str(x) for x in xs) + "]"
        aliens = "![" + ", ".join(self.lean(a, rest) for a in d["aliens"]) + "]"
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
        unfold = "simp only [State.start, Problem.unifies, problem] at h; " if at_start else ""
        self.emit(ind, f"-- solve {self.eq(eqs[0], None, True)}")
        self.emit(ind, f"refine solve (V := fun {ctx.pattern()} => {vec(bag)})"
                       f" (rest := fun {ctx.pattern()} => {restt})")
        self.emit(ind + 2, f"(glue := fun {restp} V => {glue_items.term()}) (hglue := fun _ => rfl)")
        self.emit(ind + 2, f"(a := fun {restp} => {aliens}) (L := {vec(d['L'])}) (R := {vec(d['R'])})"
                           f" (La := {vec(d['La'])}) (Ra := {vec(d['Ra'])})")
        self.emit(ind + 2, f"(E' := fun _ => True) (cp := {cp})")
        self.emit(ind + 2, f"(P := {P}) (B := {B})")
        self.emit(ind + 2, f"(fun {ctx.pattern()} h hD => ⟨by {unfold}acu_side h, trivial, by acu_distinct⟩)")
        self.emit(ind + 2, "(by decide) (by decide) (by decide)")
        self.emit(ind + 2, f"(S2_of_list _ _ _ _ _ _ {cliques} (by decide) (by acu_cliques))"
                           f" (by acu_basis) ?_")
        branches = d["branches"]
        self.emit(ind, "intro π hπ; simp [choices] at hπ" + (
            "" if not branches else "; subst hπ" if len(branches) == 1
            else "; rcases hπ with " + " | ".join(["rfl"] * len(branches))))
        fresh = sorted({int(x[1:]) for _, th, _ in branches for t in th.values()
                        for x in free_vars(t) if re.fullmatch(r"Z\d+", x)})
        blk = "Z" + "'" * len(ctx.blocks())
        inner = Ctx([rest if len(rest.items) > 1 else (rest.items[0] if rest.items else "_"),
                     ("Z", blk, fresh)])
        for pi, theta, sub in branches:
            if len(branches) > 1:
                self.emit(ind, "· -- branch " + " ".join("(" + ",".join(map(str, p)) + ")" for p in pi))
                self.node(sub, inner, ind + 1)
            else:
                self.emit(ind, "-- branch " + " ".join("(" + ",".join(map(str, p)) + ")" for p in pi))
                self.node(sub, inner, ind)

    def cover(self, n, ctx, ind):
        i, w = n.data["answer"], n.data["witness"]
        binders = self.binders[i]
        wit = [self.lean(w[b], ctx, True) for b in binders]
        self.emit(ind, f"-- cover answer {i} with " + ", ".join(f"{b} := {wit[j]}" for j, b in enumerate(binders)))
        blocks = [b for b in ctx.blocks() if b[2]]
        wtext = "(" + ", ".join(wit) + ")" if len(wit) > 1 else (wit[0] if wit else None)
        if not blocks:
            proof = f"⟨{wtext}, by acu_cover⟩" if wtext else "by acu_cover"
            self.emit(ind, f"exact cover answer{i} (by simp [answers]) fun {ctx.pattern()} _ _ => {proof}")
            return
        self.emit(ind, f"exact cover answer{i} (by simp [answers]) fun {ctx.pattern()} _ _ => by")
        for _, blk, idx in blocks:
            names = [f"Z{j}" for j in idx]
            xs = " ".join(f"x{j}" for j in range(len(idx)))
            self.emit(ind + 1, f"obtain ⟨{', '.join(names)}, rfl⟩ : ∃ {xs}, {blk} = ![{', '.join(f'x{j}' for j in range(len(idx)))}] :=")
            cases = "fin_cases i <;> rfl" if len(idx) > 1 else "fin_cases i; rfl"
            self.emit(ind + 2, f"⟨{', '.join(f'{blk} {j}' for j in range(len(idx)))}, "
                               f"funext fun i => by {cases}⟩")
        self.emit(ind + 1, f"exact ⟨{wtext}, by acu_cover⟩" if wtext else "acu_cover")

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
    c.node(root, Ctx(list(cfg["vars"])), 1, at_start=True)
    c.out.append(f"\nend {cfg['namespace']}\n")
    target = deriv_path.with_suffix(".lean")
    target.write_text(claim.rstrip() + "\n\n" + "\n".join(c.out))
    print(f"wrote {target}")


if __name__ == "__main__":
    main()
