"""Exact B2 circuit size via SAT (Kissat), Kulikov-style encoding.

A B2 circuit: n inputs, s gates, each gate reads two distinct earlier wires
and applies any of the 16 binary Boolean functions. Output = last gate.
Repeated pins / unary gates are never needed for a minimum circuit of a
function depending on >= 2 inputs (a unary gate can be absorbed into its
readers or, at the output, into the gate it reads), so we omit them.

size(f) is the least s for which the CNF is satisfiable.
"""
import itertools, subprocess, sys, os, tempfile


class CNF:
    def __init__(self):
        self.nv = 0
        self.cl = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, c):
        self.cl.append(c)

    def solve(self, timeout=600):
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
            fh.write(f"p cnf {self.nv} {len(self.cl)}\n")
            for c in self.cl:
                fh.write(" ".join(map(str, c)) + " 0\n")
            path = fh.name
        try:
            r = subprocess.run(["kissat", "-q", f"--time={timeout}", path],
                               capture_output=True, text=True)
        finally:
            os.unlink(path)
        if r.returncode == 10:
            model = set()
            for line in r.stdout.splitlines():
                if line.startswith("v"):
                    model.update(int(t) for t in line.split()[1:] if t != "0")
            return True, model
        if r.returncode == 20:
            return False, None
        return None, None  # timeout / unknown


def circuit_exists(n, f, s, timeout=600):
    """f: list of 2^n bits, row t has input bit i = (t >> i) & 1."""
    T = 1 << n
    cnf = CNF()
    # value variables for gates; inputs are constants
    val = {}
    for g in range(n, n + s):
        for t in range(T):
            val[g, t] = cnf.var()

    def lit(w, t, b):
        """literal meaning 'wire w on row t equals b'; returns True/False for constants."""
        if w < n:
            return ((t >> w) & 1) == b
        v = val[w, t]
        return v if b else -v

    op = {}
    sel = {}
    for g in range(n, n + s):
        for p in (0, 1):
            for q in (0, 1):
                op[g, p, q] = cnf.var()
        pairs = list(itertools.combinations(range(g), 2))
        sv = [cnf.var() for _ in pairs]
        for (j, k), x in zip(pairs, sv):
            sel[g, j, k] = x
        cnf.add(sv)  # at least one
        for a, b in itertools.combinations(sv, 2):
            cnf.add([-a, -b])  # at most one (pairwise; fine at these sizes)
        # no degenerate ops: gate must depend on both args (minimum circuits
        # never need degenerate gates when f depends on >= 2 inputs)
        o00, o01, o10, o11 = op[g, 0, 0], op[g, 0, 1], op[g, 1, 0], op[g, 1, 1]
        # depends on first arg: exists q with op(0,q)!=op(1,q)
        # not (o00==o10 and o01==o11)
        # encode via aux
        for (a0, a1, b0, b1) in [(o00, o10, o01, o11), (o00, o01, o10, o11)]:
            d1, d2 = cnf.var(), cnf.var()
            # d1 -> a0 != a1 ; d2 -> b0 != b1 ; d1 or d2
            cnf.add([-d1, a0, a1]); cnf.add([-d1, -a0, -a1])
            cnf.add([-d2, b0, b1]); cnf.add([-d2, -b0, -b1])
            cnf.add([d1, d2])
        # normalize: op(0,0)=0 (negations pushed to readers / output)
        cnf.add([-o00])
        for (j, k), x in zip(pairs, sv):
            for t in range(T):
                for p in (0, 1):
                    for q in (0, 1):
                        lj, lk = lit(j, t, p), lit(k, t, q)
                        if lj is False or lk is False:
                            continue
                        prem = [-x]
                        if lj is not True:
                            prem.append(-lj)
                        if lk is not True:
                            prem.append(-lk)
                        o = op[g, p, q]
                        # val = op
                        cnf.add(prem + [-val[g, t], o])
                        cnf.add(prem + [val[g, t], -o])
    # every gate except the output is used
    for g in range(n, n + s - 1):
        users = [sel[h, j, k] for (h, j, k) in sel if h > g and (j == g or k == g)]
        cnf.add(users)
    out = n + s - 1
    # output computes f or its negation (negation is free to absorb since we
    # normalized op(0,0)=0); allow either by aux variable
    neg = cnf.var()
    for t in range(T):
        # val[out,t] xor neg == f[t]
        v = val[out, t]
        if f[t]:
            cnf.add([v, neg]); cnf.add([-v, -neg])
        else:
            cnf.add([-v, neg]); cnf.add([v, -neg])
    res, model = cnf.solve(timeout)
    if res is True:
        circ = []
        for g in range(n, n + s):
            for (h, j, k), x in sel.items():
                if h == g and x in model:
                    tt = "".join(str(int(op[g, p, q] in model)) for p in (0, 1) for q in (0, 1))
                    circ.append((g, j, k, tt))
        return True, (circ, neg in model)
    return res, None


def min_size(n, f, lo=1, hi=30, timeout=600):
    for s in range(lo, hi + 1):
        r, c = circuit_exists(n, f, s, timeout)
        if r is None:
            return None, s, None
        if r:
            return s, s, c
    return None, hi, None


def edge_fn(n, edges, extra=()):
    f = []
    for t in range(1 << n):
        x = [(t >> i) & 1 for i in range(n)]
        f.append(int(any(x[u] and x[v] for u, v in edges) or any(x[a] for a in extra)))
    return f


def tau(n, edges):
    best = n
    for m in range(1 << n):
        if all((m >> u) & 1 or (m >> v) & 1 for u, v in edges):
            best = min(best, bin(m).count("1"))
    return best
