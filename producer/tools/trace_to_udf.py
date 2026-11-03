#!/usr/bin/env python3
"""Extract a UDF derivation (documentation/derivation-format.md) from Maude's unification trace.

  python3 producer/tools/trace_to_udf.py model.maude Module 'lhs-meta' 'rhs-meta' ...
      # prints the derivation of  lhs =? rhs /\\ ...  and checks its leaves

The derivation follows the calculus of the format. Its states and free steps (delete,
decomp, elim, clash, occurs) are recomputed here, which is syntactic; the arithmetic of
each acu-solve (basis and selections) is read from the matching ACU subproblem of Maude's
search tree (trace_tree.py). Maude's subproblems differ from the calculus's in three ways,
all undone here:
  - Maude names subterms by fresh variables (purification, p = s) and re-solves variables
    it bound earlier (X = t). Such a variable has a row defining it as a sum of the other
    unknowns; substituting the row away maps the solutions, and so the minimal ones, one
    to one. Columns left with no coefficient (an alien cancelled on both sides) are
    dropped with their unit vectors.
  - Maude renames: fresh variables of a selection, and reused variables. The map `ren`
    sends each Maude name to its term in the derivation.
  - Maude also takes non-maximal selections, which are skipped.
  - Maude's bindings are lazy: it does not substitute inside aliens, so one alien term may
    label several unknowns (each with its share of the occurrences).
Maude also leaves out basis vectors that merge aliens with different top symbols, and
decides ground equations directly (rule `ground`). The leaves form a complete set of
unifiers, possibly with instances of one another. Maude runs filtered unification
(metaVariantUnify ... filter): its answers are the unifiers its filter keeps, and each leaf
is closed by `cover` with the answer that kept it, the witness being the filter's matcher
(composed along evictions; trace events vunifier, vmatch, vevicted, vsurvivor, vfree).
Given answers instead (a user's unifier set) are matched against the leaves (metaMatch).
Untrusted: the derivation is checked by Lean.
"""
import re, sys
from fractions import Fraction
from itertools import product
from dataclasses import dataclass, field

import trace_tree

INF = 2147483647

# ----------------------------------------------------------------------------- terms


@dataclass(frozen=True)
class V:
    name: str
    sort: str


@dataclass(frozen=True)
class A:
    op: str
    args: tuple = ()


def unescape(s):
    return re.sub(r"`(.)", r"\1", s)


def parse_prefix(text):
    """A term printed by Maude with  mixfix off :  f(t, ...), X:S, c."""
    toks = re.findall(r"(?:`.|[^(),\s`])+|[(),]", text)
    pos = 0

    def term():
        nonlocal pos
        name = unescape(toks[pos]); pos += 1
        if pos < len(toks) and toks[pos] == "(":
            pos += 1
            args = [term()]
            while toks[pos] == ",":
                pos += 1
                args.append(term())
            pos += 1
            return A(name, tuple(args))
        if ":" in name and not name.startswith("'"):
            n, s = name.rsplit(":", 1)
            return V(n, s)
        return A(name)
    t = term()
    return t, toks[pos:]


def parse_meta(text):
    """A meta-term:  'f[t, ...], 'X:S, 'c.S ."""
    toks = re.findall(r"'(?:`.|[^\[\],\s`])+|[\[\],]", text)
    pos = 0

    def term():
        nonlocal pos
        q = unescape(toks[pos][1:]); pos += 1
        if pos < len(toks) and toks[pos] == "[":
            pos += 1
            args = [term()]
            while toks[pos] == ",":
                pos += 1
                args.append(term())
            pos += 1
            return A(q, tuple(args))
        if ":" in q:
            return V(*q.rsplit(":", 1))
        return A(q.rsplit(".", 1)[0])
    return term()


class Sig:
    """The module's operators, from  upModule  (prefix form)."""

    def __init__(self, model, module, out=None):
        """From Maude's output `out` holding  upModule('M, true) , or a run of its own."""
        if out is None:
            out, _ = trace_tree.maude(f"load {model}\n{Sig.command(module)}")
        m, _ = parse_prefix(re.split(r"\n={5,}|\nBye", out.split("result FModule:", 1)[1])[0])
        self.acu, self.ops, self.subsorts = {}, [], []    # acu: op -> (sort, identity)
        q = lambda a: a.op.lstrip("'")
        seq = lambda a: [x for x in (a.args if a.op in ("__", "_;_") else (a,)) if a.op != "nil"]
        for node in walk(m):
            if node.op == "op_:_->_[_]." :
                name, dom, cod, attrs = node.args
                attrs = seq(attrs)
                ids = [x for x in attrs if x.op == "id"]
                if {"assoc", "comm"} <= {x.op for x in attrs} and ids:
                    self.acu[q(name)] = (q(cod), q(ids[0].args[0]).rsplit(".", 1)[0])
                else:
                    self.ops.append((q(name), [q(x) for x in seq(dom)], q(cod)))
            elif node.op == "subsort_<_.":
                self.subsorts.append(tuple(q(x) for x in node.args))
        self.sort_op = {s: op for op, (s, _) in self.acu.items()}
        self.ident = {i: op for op, (_, i) in self.acu.items()}

    @staticmethod
    def command(module):
        return f"red in META-LEVEL : upModule('{module}, true) ."

    def var_op(self, v):
        return self.sort_op.get(v.sort.strip("[]"))

    def acu_op(self, t):
        """The ACU operator whose sort t has at the top, if t is a sum, an identity or a bag variable."""
        if isinstance(t, V):
            return self.var_op(t)
        return t.op if t.op in self.acu else self.ident.get(t.op) if not t.args else None

    def norm(self, t):
        """Flatten, drop identities, order arguments (the ACU normal form)."""
        if isinstance(t, V):
            return t
        args = [self.norm(a) for a in t.args]
        if t.op not in self.acu:
            return A(t.op, tuple(args))
        ident, flat = self.acu[t.op][1], []
        for a in args:
            if isinstance(a, A) and a.op == t.op:
                flat += a.args
            elif a != A(ident):
                flat.append(a)
        flat.sort(key=repr)
        return A(ident) if not flat else flat[0] if len(flat) == 1 else A(t.op, tuple(flat))

    def elems(self, t, op):
        """The summands of t as a sum of op."""
        if isinstance(t, A) and t.op == op:
            return list(t.args)
        return [] if t == A(self.acu[op][1]) else [t]


def walk(t):
    yield t
    if isinstance(t, A):
        for a in t.args:
            yield from walk(a)


def subst(t, s):
    if isinstance(t, V):
        return s.get(t, t)
    return A(t.op, tuple(subst(a, s) for a in t.args)) if t.args else t


def occurs(v, t):
    return any(x == v for x in walk(t))


def sexp(t):
    if isinstance(t, V):
        return t.name
    return t.op if not t.args else "(" + " ".join([t.op] + [sexp(a) for a in t.args]) + ")"


# ----------------------------------------------------------------------------- Maude subproblems


@dataclass
class System:
    op: str
    cols: list            # unknowns as Maude terms
    bounds: list
    rows: list
    basis: list           # (Maude index, vector)


def read_frame(frame):
    op, rest = frame.system.split(" ", 1)
    cols, bounds = [], []
    for m in re.finditer(r"\[\d+: (.*?) bound (\d+)( cover)?\]", rest):
        cols.append(parse_prefix(m.group(1))[0])
        bounds.append(int(m.group(2)))
    eqs = rest.split(" equations ", 1)[1]
    rows = [[int(x) for x in r.split(",")] for r in re.findall(r"\(([-\d,]+)\)", eqs)]
    rows = [r + [0] * (len(cols) - len(r)) for r in rows]      # Maude omits trailing zeros
    basis = [(int(i), [int(x) for x in v.split(",")]) for i, v in re.findall(r"#(\d+)\(([\d,]+)\)", frame.basis)]
    return System(unescape(op), cols, bounds, rows, basis)


def legal(vectors, bounds):
    """Selections covering each bound-1 unknown exactly once and holding every vector without one."""
    alien = [j for j, b in enumerate(bounds) if b == 1]
    free = [k for k, v in enumerate(vectors) if not any(v[j] for j in alien)]
    out = []

    def cover(sel, covered):
        todo = [j for j in alien if j not in covered]
        if not todo:
            out.append(sorted(sel + free))
            return
        for k, v in enumerate(vectors):
            hit = {j for j in alien if v[j]}
            if v[todo[0]] and not hit & covered:
                cover(sel + [k], covered | hit)
    cover([], set())
    return out


def split(count, U, bounds, basis):
    """The row of an equation (count: term -> occurrences, left minus right). The occurrences
    of an alien that labels several unknowns are split among them so that the basis solves
    the row."""
    row = [0] * len(U)
    labels = {}
    for j, u in enumerate(U):
        labels.setdefault(u, []).append(j)
    for u, js in labels.items():
        row[js[0]] = count.get(u, 0)
    shared = [(js, count.get(u, 0)) for u, js in labels.items() if len(js) > 1]
    choices = [[cs for cs in product(range(-abs(n) - 1, abs(n) + 2), repeat=len(js)) if sum(cs) == n]
               for js, n in shared]
    for pick in product(*choices):
        for (js, _), cs in zip(shared, pick):
            for j, c in zip(js, cs):
                row[j] = c
        if all(sum(a * b for a, b in zip(row, v)) == 0 for v in basis):
            return row
    raise ValueError("a vector of Maude's basis does not solve the calculus's row")


def rank(rows):
    m = [[Fraction(x) for x in r] for r in rows]
    r = 0
    for c in range(len(m[0]) if m else 0):
        p = next((i for i in range(r, len(m)) if m[i][c]), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c]:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


# ----------------------------------------------------------------------------- derivation


class Deriv:
    def __init__(self, sig, variables):
        self.sig, self.steps, self.leaves = sig, [], []
        self.used = {v.name for v in variables}
        self.originals = set(variables)
        self.nr_fresh = 0

    def fresh(self, op):
        while True:
            self.nr_fresh += 1
            name = f"Z{self.nr_fresh}"
            if name not in self.used:
                self.used.add(name)
                return V(name, self.sig.acu[op][0])

    def step(self, rule, args=""):
        sid = f"s{len(self.steps)}"
        self.steps.append([sid, rule, args, []])
        return self.steps[-1]

    def resolve(self, t, alpha, ren):
        """A Maude term in the current state's names."""
        s = {v: ren.get(v, alpha.get(v, v)) for v in walk(t) if isinstance(v, V)}
        return self.sig.norm(subst(t, s))

    def classify(self, l, r):
        sig = self.sig
        if l == r:
            return "delete", None
        if not any(isinstance(x, V) for t in (l, r) for x in walk(t)):
            return "ground", None                    # ground, and different modulo ACU
        for v, t in ((l, r), (r, l)):
            if isinstance(v, V):
                if not occurs(v, t) and (sig.var_op(v) or sig.acu_op(t) is None):
                    return "elim", v           # (an element variable is no sum)
                if sig.acu_op(t) and not occurs(v, t):
                    return "acu", sig.acu_op(t)
                op = sig.acu_op(t)
                if op is None or any(a != v and occurs(v, a) for a in sig.elems(t, op)):
                    return "occurs", None
                return "acu", op
        op = sig.acu_op(l) or sig.acu_op(r)
        if op:
            return "acu", op
        return ("decomp" if l.op == r.op and len(l.args) == len(r.args) else "clash"), None

    def derive(self, E, alpha, branch, pos, ren):
        """The step proving state ⟨alpha ; E⟩, following Maude's branch from event pos."""
        sig = self.sig
        if not E:
            st = self.step("leaf")
            self.leaves.append((alpha, st, self.leaf_id(branch, pos), ren))
            return st[0]
        kinds = [self.classify(l, r) for l, r in E]
        free = [i for i, (k, _) in enumerate(kinds) if k != "acu"]
        if free:
            i = free[0]
            k, v = kinds[i]
            l, r = E[i]
            rest = E[:i] + E[i + 1:]
            if k in ("clash", "occurs", "ground"):
                return self.step(k, f":eq {i}")[0]
            if k == "delete":
                st = self.step(k, f":eq {i}")
                st[3] = [self.derive(rest, alpha, branch, pos, ren)]
                return st[0]
            if k == "decomp":
                st = self.step(k, f":eq {i}")
                st[3] = [self.derive(list(zip(l.args, r.args)) + rest, alpha, branch, pos, ren)]
                return st[0]
            th = {v: r if v == l else l}
            st = self.step("elim", f":eq {i} :var {v.name}")
            E2, alpha2, ren2 = self.apply(th, rest, alpha, ren)
            st[3] = [self.derive(E2, alpha2, branch, pos, ren2)]
            return st[0]
        # ACU equations remain: the next Maude subproblem solves some of them
        if branch is None:
            raise ValueError("no Maude branch for a premise that needs an ACU step")
        while pos < len(branch.events) and not isinstance(branch.events[pos], trace_tree.Frame):
            kind, text = branch.events[pos]
            if kind == "bind":                       # p := t, t an alien: p labels t
                p, t = (parse_prefix(x)[0] for x in text.split(" := ", 1))
                if p not in self.originals and isinstance(t, A) and sig.acu_op(t) is None:
                    ren = {**ren, p: self.resolve(t, alpha, ren)}
            if kind == "acu-eq":                     # purification  s =? p
                lhs, rhs = (parse_prefix(x)[0] for x in text.split(" =? ", 1))
                for p, s in ((rhs, lhs), (lhs, rhs)):
                    if isinstance(p, V) and p not in self.originals and p not in ren:
                        ren = {**ren, p: self.resolve(s, alpha, ren)}
                        break
            pos += 1
        if pos == len(branch.events):
            raise ValueError("Maude has no subproblem for: " + "; ".join(f"{sexp(l)} = {sexp(r)}" for l, r in E))
        frame = branch.events[pos]
        return self.solve(frame, E, kinds, alpha, ren)

    def leaf_id(self, branch, pos):
        """The number of the unifier Maude finds at the end of this branch (filtered mode):
        after the steps already followed, through its own subproblems' maximal selections."""
        if branch is None:
            return None
        if branch.ids:
            return branch.ids[0]
        for f in branch.events[pos:]:
            if isinstance(f, trace_tree.Frame):
                sy = read_frame(f)
                by_sel = {tuple(sorted(int(x[1:]) for x in b.selection)): b for b in f.branches}
                for sel in sorted(legal([v for _, v in sy.basis], sy.bounds), key=len, reverse=True):
                    b = by_sel.get(tuple(sorted(sy.basis[k][0] for k in sel)))
                    if b is not None and (k := self.leaf_id(b, 0)) is not None:
                        return k
        return None

    def apply(self, th, E, alpha, ren):
        """The state and renaming after the substitution th."""
        n = lambda t: self.sig.norm(subst(t, th))
        return ([(n(l), n(r)) for l, r in E], {x: n(t) for x, t in alpha.items()},
                {x: n(t) for x, t in ren.items()})

    def solve(self, frame, E, kinds, alpha, ren):
        sig, sy = self.sig, read_frame(frame)
        cols = [self.resolve(c, alpha, ren) for c in sy.cols]
        # the ACU equations of this operator, and the bindings Maude re-solves with them
        eqs = [i for i, (k, x) in enumerate(kinds) if k == "acu" and x == sy.op
               or k == "elim" and sig.var_op(x) == sy.op
               and all(y in cols for side in E[i] for y in sig.elems(side, sy.op))]
        # our system: unknowns and rows of the equations of this operator
        counts = []
        for i in eqs:
            c = {}
            for side, sgn in ((E[i][0], 1), (E[i][1], -1)):
                for x in sig.elems(side, sy.op):
                    c[x] = c.get(x, 0) + sgn
            counts.append(c)
        ours = {x for c in counts for x, n in c.items() if n}
        # an alien cancelled here may still label two of Maude's unknowns (from two
        # equations, Maude's bindings being lazy): then it keeps them
        seen = {x for c in counts for x in c}
        # Maude's system in our names; eliminate its defined variables, drop empty columns
        shared = {c for c in seen if cols.count(c) > 1}
        keep = [j for j, c in enumerate(cols) if (c in ours or c in shared) and (not isinstance(sy.cols[j], V) or isinstance(c, V) or sy.bounds[j] == 1)]
        rows = [list(r) for r in sy.rows]
        gone, changed = set(), True
        while changed:
            changed = False
            for j in range(len(cols)):
                if j in keep or j in gone or sy.bounds[j] != INF:
                    continue
                for r in rows:
                    s = r[j]
                    if abs(s) == 1 and all(-s * r[x] >= 0 for x in range(len(r)) if x != j):
                        rows = [[a - q[j] * s * b for a, b in zip(q, r)] for q in rows if q is not r]
                        gone.add(j)
                        changed = True
                        break
        rows = [r for r in rows if any(r)]
        dropped = [j for j in range(len(cols)) if j not in keep and j not in gone]
        if any(r[j] for r in rows for j in dropped):
            raise ValueError(f"cannot reduce Maude's {sy.op} system to the calculus's")
        # an alien may label several unknowns (Maude's bindings are lazy); a bag variable not
        bags = [cols[j] for j in keep if sy.bounds[j] != 1]
        if len(set(bags)) != len(bags) or not ours <= {cols[j] for j in keep}:
            raise ValueError(f"Maude's {sy.op} system has other unknowns than the calculus's")
        vecs = [v for _, v in sy.basis]
        maude_sel = legal(vecs, sy.bounds)
        branches = {tuple(sorted(int(x[1:]) for x in b.selection)): b for b in frame.branches}

        def follow(k_sel, extra, r):
            """The Maude branch of a legal selection (positions in sy.basis), and the renaming r
            extended by its fresh variables: the k-th one stands for extra(k)."""
            b = branches.get(tuple(sorted(sy.basis[k][0] for k in k_sel)))
            r = dict(r)
            if b is not None:
                fresh = dict(re.match(r"#(\d+) := (.*)", e[1].split(" ", 1)[1]).groups()
                             for e in b.events if not isinstance(e, trace_tree.Frame) and e[0] == "acu-fresh")
                for k in k_sel:
                    if str(sy.basis[k][0]) in fresh:
                        r[parse_prefix(fresh[str(sy.basis[k][0])])[0]] = extra(k)
            return b, r

        def unit(k):
            v = vecs[k]
            nz = [j for j in range(len(cols)) if j not in gone and v[j]]
            if len(nz) != 1 or v[nz[0]] != 1:
                raise ValueError("a vector of Maude's basis does not reduce to a unit")
            return cols[nz[0]]

        if not keep:                                 # a subproblem of Maude's own making
            if rows or len(maude_sel) != 1:
                raise ValueError(f"Maude's {sy.op} subproblem has no counterpart in the calculus")
            b, r = follow(maude_sel[0], unit, ren)
            return self.derive(E, alpha, b, 0, r)
        # the acu-solve step, in Maude's column order
        U = [cols[j] for j in keep]
        bounds = [sy.bounds[j] for j in keep]
        bagvars = {u for u, b in zip(U, bounds) if b == INF}
        if any(occurs(x, u) for u, b in zip(U, bounds) if b == 1 for x in bagvars):
            raise ValueError("an alien contains a bag variable of its system (outside UDF 1)")
        mine = [k for k, v in enumerate(vecs) if any(v[j] for j in keep)]
        if any(vecs[k][j] for k in mine for j in dropped):
            raise ValueError("a vector of Maude's basis mixes kept and dropped unknowns")
        basis = [[vecs[k][j] for j in keep] for k in mine]
        rows_ours = [split(c, U, bounds, basis) for c in counts]
        reduced = [[r[j] for j in keep] for r in rows]
        if rank(rows_ours) != rank(rows_ours + reduced):
            raise ValueError(f"Maude's {sy.op} system is weaker than the calculus's")
        sels = [[mine.index(k) for k in s if k in mine] for s in maude_sel]
        assert sorted(map(sorted, sels)) == sorted(legal(basis, bounds)), "selections differ"
        st = self.step("acu-solve")
        sel_text, premises = [], []
        for s_maude, s in zip(maude_sel, sels):
            alien = [j for j, b in enumerate(bounds) if b == 1]
            Z, th, pending = {}, {}, []
            for p in s:
                aliens = [U[j] for j in alien if basis[p][j]]
                Z[p] = aliens[0] if aliens else self.fresh(sy.op)
                pending += [(u, aliens[0]) for u in aliens[1:]]
            for j, u in enumerate(U):
                if bounds[j] == INF:
                    th[u] = A(sy.op, tuple(Z[p] for p in s for _ in range(basis[p][j])))
            E2, alpha2, ren2 = self.apply(th, pending + [e for i, e in enumerate(E) if i not in eqs], alpha, ren)
            b, ren2 = follow(s_maude, lambda k: sig.norm(subst(Z[mine.index(k)] if k in mine else unit(k), th)), ren2)
            fresh = [Z[p].name for p in s if not any(basis[p][j] for j in alien)]
            sel_text.append(f"(sel ({' '.join(map(str, s))}) :fresh ({' '.join(fresh)}))")
            premises.append(self.derive(E2, alpha2, b, 0, ren2))
        bd = lambda b: "inf" if b == INF else str(b)
        st[2] = (f":op {sy.op} :eqs ({' '.join(map(str, eqs))})\n   :unknowns ({' '.join(map(sexp, U))})"
                 f"\n   :bounds ({' '.join(map(bd, bounds))})"
                 f"\n   :rows ({' '.join('(' + ' '.join(map(str, r)) + ')' for r in rows_ours)})"
                 f"\n   :basis ({' '.join('(' + ' '.join(map(str, v)) + ')' for v in basis)})"
                 f"\n   :selections ({' '.join(sel_text)})")
        st[3] = premises
        return st[0]


# ----------------------------------------------------------------------------- driver


FILTERED = trace_tree.ALL_UNIFIERS.replace("metaUnify(M, P, 0, N)", "metaVariantUnify(M, P, empty, '#, filter, N)")


def from_meta(t):
    """A meta-term as printed in prefix form ( _[_]('f, _,_(...)), 'X:S, 'c.S ) as a term."""
    if t.op == "_[_]":
        args = t.args[1].args if t.args[1].op == "_,_" else (t.args[1],)
        return A(t.args[0].op[1:], tuple(from_meta(a) for a in args))
    q = t.op[1:]
    return V(*q.rsplit(":", 1)) if ":" in q else A(q.rsplit(".", 1)[0])


def substitution(t):
    """A meta-level substitution ( _;_(_<-_(...), ...), or none ) as a dict."""
    binds = [] if "none" in t.op else t.args if t.op == "_;_" else (t,)
    return {from_meta(b.args[0]): from_meta(b.args[1]) for b in binds}


def results(out, sort):
    """Maude's results of the given sort; constants like (none).Substitution as atoms."""
    return [A(r) if r.startswith("(") else parse_prefix(r)[0] for r in re.findall(rf"result {sort}: (.*)", out)]


def filter_events(trace):
    """Maude's unifier filter (filtered mode): for each unifier it dropped, the unifier that
    subsumed it and the matcher (its variable names to terms over the dropped one's), and the
    survivors in answer order, and the answers: the survivors' bindings of the problem's
    variables, in Maude's own names (its printed output renames them)."""
    covers, survivors, matcher, answers, order, first = {}, [], {}, {}, [], None
    free, freed = {}, {}       # per unifier: its variables' names in the search
    for kind, rest in trace_tree.events(trace):
        if kind == "vfree":
            old, _, new = rest.split(" ", 2)
            freed[new.rsplit(":", 1)[0]] = old.rsplit(":", 1)[0] if ":" in old else old
        if kind == "vrename":
            ptr, orig, _ = rest.split(" ", 2)
            first = first or ptr
            if ptr == first:
                order.append(parse_prefix(orig)[0])
        elif kind == "vanswerbind":
            a, j, _, t = rest.split(" ", 3)
            answers.setdefault(int(a), {})[order[int(j)]] = parse_prefix(t)[0]
        if kind == "vmatch" and not rest.startswith("0x"):
            x, t = rest.split(" := ", 1)
            matcher[x.rsplit(":", 1)[0]] = parse_prefix(t)[0]
        elif kind in ("vsubsumed", "vevicted"):
            a, _, b = rest.split()
            covers[int(a)] = (int(b), matcher)
            matcher = {}
        elif kind == "vsurvivor":
            survivors.append(int(rest))
        elif kind == "vunifier":
            matcher = {}
            free[int(rest)], freed = freed, {}
    return covers, survivors, [answers[a] for a in sorted(answers)], free


def chain(covers, k):
    """The survivor covering unifier k, and the composed matcher from its variable names to
    terms over k's variables (None: k survived)."""
    beta = None
    while k in covers:
        k, mu = covers[k]
        if beta is not None:
            mu = {x: subst(t, {v: beta[v.name] for v in walk(t) if isinstance(v, V) and v.name in beta})
                  for x, t in mu.items()}
        beta = mu
    return k, beta


def extract(model, module, eqs, answers=None, context=(), canonical=False):
    """The UDF text and statistics: leaves, leaves that are unifiers, answers, leaves
    covered by an answer, and Maude's unfiltered count. The answers are the given ones
    (substitutions, dicts from variables to terms) or else Maude's filtered unifiers.
    `context` adds variables that occur in no equation (a leaf keeps them as they are).
    `canonical`: each answer's variables are named #1, #2, ... in the order of their names,
    as Lean's decoding of the answers binds them (maudeUnify.lean), so that the derivation
    is stated in the obligation's own names (Reflect/Tactic.lean)."""
    # one Maude run: the module, and the filtered unification with its trace
    trace, nr, out = trace_tree.run(model, module, eqs, filtered=True, before=Sig.command(module))
    sig = Sig(model, module, out)
    problem = [(sig.norm(parse_meta(l)), sig.norm(parse_meta(r))) for l, r in eqs]
    variables = sorted({x for e in problem for t in e for x in walk(t) if isinstance(x, V)}
                       | set(context), key=repr)
    d = Deriv(sig, variables)
    d.derive(problem, {v: v for v in variables}, trace_tree.build(trace), 0, {})
    sound = sum(all(sig.norm(subst(l, a)) == sig.norm(subst(r, a)) for l, r in problem)
                for a, *_ in d.leaves)
    # the answers: Maude's filtered unifiers (or the given ones); each leaf is closed by an
    # instance of one
    own = answers is None
    covers, survivors, traced, free = filter_events(trace)
    if own:
        # a variable in no equation is left as it is (Lean's decoding binds it so too)
        answers = [{**{v: v for v in variables}, **a} for a in traced]
    answers = [{x: sig.norm(t) for x, t in a.items()} for a in answers]
    names = [{y.name: (f"#{i + 1}" if canonical else y.name) for i, y in enumerate(sorted(
        {y for t in a.values() for y in walk(t) if isinstance(y, V)}, key=lambda y: y.name))}
        for a in answers]
    # own answers: the witnesses are Maude's matchers, read off the filter's trace
    covered = from_trace = 0
    if own:
        for alpha, st, k, ren in d.leaves:
            if k is not None:
                s_, beta = chain(covers, k)
                if s_ not in survivors:
                    continue
                candidates = [(survivors.index(s_), beta)]
            else:   # Maude answered without unifying (identical sides): each answer as is
                candidates = [(j, None) for j in range(len(answers))]
            for j, beta in candidates:
                ys = {y for t in answers[j].values() for y in walk(t) if isinstance(y, V)}
                # a term over unifier k's variables, in the derivation's names: through their
                # names in the search (vfree), then the derivation's renaming
                known = {v.name: v for v in list(ren) + list(alpha)}
                back = lambda t: d.resolve(subst(t, {v: known.get(free.get(k, {}).get(v.name, v.name), v)
                                                     for v in walk(t) if isinstance(v, V)}), alpha, ren)
                w = {y.name: back(beta[y.name] if beta and y.name in beta else y) for y in ys}
                inst = {y: w[y.name] for y in ys}
                if all(sig.norm(alpha[x]) == sig.norm(subst(answers[j].get(x, x), inst)) for x in variables):
                    ws = " ".join(f"({names[j][y]} {sexp(t)})" for y, t in sorted(w.items()))
                    st[1:3] = ["cover", f":answer a{j} :witness ({ws})"]
                    covered += 1
                    from_trace += 1
                    break
    consts = {n: c for n, dm, c in sig.ops if not dm} | {i: s for s, i in sig.acu.values()}
    esc = lambda n: re.sub(r"([{}\[\](), ])", r"`\1", n)

    def meta(t):
        if isinstance(t, V):
            return f"'{esc(t.name)}:{esc(t.sort)}"
        if not t.args:
            return f"'{esc(t.op)}.{consts[t.op]}"
        return f"'{esc(t.op)}[" + ", ".join(map(meta, t.args)) + "]"
    # match all variables at once, as one tuple (subject variables count as constants)
    tup = (f"fmod UDF-MATCH is including {module} . sort UdfTup .\n"
           f"  op udfTup : {' '.join(x.sort for x in variables)} -> UdfTup .\nendfm\nselect META-LEVEL .\n")
    script = ""
    open_leaves = [(alpha, st) for alpha, st, *_ in d.leaves if st[1] == "leaf"]
    for alpha, _ in open_leaves:
        for sigma in answers:
            pat = ", ".join(meta(sigma.get(x, x)) for x in variables)
            sub = ", ".join(meta(alpha[x]) for x in variables)
            script += f"red metaMatch(upModule('UDF-MATCH, false), 'udfTup[{pat}], 'udfTup[{sub}], nil, 0) .\n"
    out, _ = trace_tree.maude(f"load {model}\n{tup}{script}") if script else ("", "")
    matches = iter(results(out, r"(?:Substitution\??|Assignment)"))
    for alpha, st in open_leaves:
        ms = [next(matches) for _ in answers]
        j = next((j for j, m in enumerate(ms) if "noMatch" not in m.op), None)
        if j is not None:
            covered += 1
            w = " ".join(f"({x.name} {sexp(t)})" for x, t in substitution(ms[j]).items())
            st[1:3] = ["cover", f":answer a{j} :witness ({w})"]
    sorts = sorted({s for _, d_, c in sig.ops for s in d_ + [c]} | {s for s, _ in sig.acu.values()})
    lines = ["(udf 1)", "(signature"]
    lines += [f"  (sort {s})" for s in sorts]
    lines += [f"  (subsort {a} {b})" for a, b in sig.subsorts]
    lines += [f"  (op {n} ({' '.join(dm)}) {c})" for n, dm, c in sig.ops if n not in sig.ident]
    lines += [f"  (acu {op} {s} {i})" for op, (s, i) in sig.acu.items()]
    lines += [f"  (var {v.name} {v.sort})" for v in variables] + ["  )"]
    lines += ["(problem " + " ".join(f"(= {sexp(l)} {sexp(r)})" for l, r in problem) + ")", "(answers"]
    for j, sigma in enumerate(answers):
        binders = sorted({x for t in sigma.values() for x in walk(t) if isinstance(x, V)},
                         key=lambda x: x.name)
        named = {x: V(names[j][x.name], x.sort) for x in binders}
        lines.append(f"  (unifier a{j} (binders {' '.join(f'({named[x].name} {x.sort})' for x in binders)})"
                     + "".join(f" (bind {x.name} {sexp(subst(t, named))})" for x, t in sigma.items()) + ")")
    lines.append("  )")
    for sid, rule, args, prem in d.steps:
        lines.append(f"(step {sid} {rule}{' ' + args if args else ''} :premises ({' '.join(prem)}))")
    return "\n".join(lines), dict(leaves=len(d.leaves), unifiers=sound, answers=len(answers),
                                   covered=covered, from_trace=from_trace, maude=nr,
                                   answer_terms=answers)


def main():
    model, module, *sides = sys.argv[1:]
    text, stats = extract(model, module, list(zip(sides[::2], sides[1::2])))
    print(text)
    print("; " + ", ".join(f"{k} {v}" for k, v in stats.items() if k != "answer_terms"), file=sys.stderr)


if __name__ == "__main__":
    main()
