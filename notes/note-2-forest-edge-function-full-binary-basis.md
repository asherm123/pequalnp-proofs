# Note 2: the edge function of a forest has the same exact size over the full binary basis

pequalnp.com, 2026-11-24. A draft for readers, not a checked row.

A follow-up to [Note 1](note-1-edge-function-exact-size.md). This is a hand proof plus SAT
checks. It is not machine-checked in Lean. One AI referee (a fresh Claude subagent) reviewed it, found no mathematical error and flagged wording gaps, which are fixed here. No human has reviewed it. No claim is
made about whether it is known. The scripts are in [note-2-scripts/](note-2-scripts/).

## Statement

For a graph G let f_G(x) = OR over edges uv of (x_u AND x_v). For a set A of extra
variables not in G let F(G,A) = f_G OR (OR of x_a, a in A). B2 = circuits of fan-in-two
gates computing any of the 16 binary Boolean functions; every gate counts, inputs are free.

**Theorem.** If G is a forest, A is disjoint from V(G), and |E(G)| + |A| >= 1, then

    C_B2(F(G,A)) = |A| + |E(G)| + tau(G) - 1,

where tau is the vertex cover number. In particular C_B2(f_G) = |E| + tau(G) - 1 for every
forest with an edge, for example C_B2(f_{P_n}) = n + floor(n/2) - 2.

This strengthens row (b) of Note 1 (L-meta-104: the same lower bound for AND/OR/NOT circuits
with NOT gates counted). Each AND/OR/NOT circuit is a B2 circuit of at most the same size,
so the B2 bound implies the De Morgan one. The converse does not hold.

## Upper bound

Take a minimum vertex cover T. Each t in T has an edge whose other endpoint is outside T,
otherwise T - t would be a cover. Assign each edge to one covering endpoint, so that each t
receives d_t >= 1 edges. The circuit OR_{t in T} (x_t AND OR of t's assigned neighbours)
uses sum (d_t - 1 + 1) + |T| - 1 = |E| + tau - 1 gates (AND/OR only). ORing in the |A|
extra variables costs |A| more gates when G has an edge. When G has no edge, OR of A costs
|A| - 1 gates, which again equals b.

## Lower bound

We use induction on the number of relevant variables. Functions are taken over any ambient
set of variables; irrelevant variables cost nothing, since inputs are free.
Write b(G,A) = |A| + |E| + tau(G) - 1.
Let C be a minimum B2 circuit for F = F(G,A). We use the standard facts about minimum
circuits of a function that depends on at least two variables:

- (M1) no gate reads the same wire twice, and every gate depends on both of its inputs;
- (M2) every gate except the output has at least one reader;
- (M3) every relevant variable has at least one reader.

Each gate is AND-type or XOR-type. An AND-type gate has, for each input, a constant that
makes its output constant. An XOR-type gate is a XOR b XOR k.

**Elimination.** Suppose a substitution is made (a variable becomes a constant, or a
variable on which the restricted function no longer depends is replaced by an existing wire
that comes before all of its readers, so no cycle arises). Propagate in topological order.
A gate is *eliminated* if, after propagation, it has a constant input, or both of its inputs
are (negated) copies of one wire. Such a gate computes a constant or a (negated) copy of one
wire, so it can be removed: its readers read that wire instead, and any negation is folded
into their truth tables. Chains of removed gates just compose these copies. If the output
gate is removed and becomes ¬(gate a), the negation is folded into a's truth table and into
a's other readers. It cannot be ¬(input variable), because F' is monotone and nonconstant in
every case below. So C(F') <= |C| - e, where F' is the restricted function and e is the
number of eliminated gates. Gates such as R_g in Case 3c, whose input becomes constant only
through propagation, are counted. To prove |C| >= b(G,A) it is enough
to find a substitution with b(G,A) - b(G',A') <= e. We call b(G,A) - b(G',A') the drop.

**Base cases.**
- |E| = 0 and |A| = 1: b = 0.
- G is a single edge and A is empty: b = 1, and one gate is needed.
- G is a path on three vertices and A is empty: b = 2, and F depends on 3 variables.
  (This case is also handled by Case 1, so it is listed only for clarity.)

**Step 0 (A is nonempty, not a base case).** Set x_a := 0 for some a in A. Then
F' = F(G, A - a), the drop is 1, and e >= 1 by (M3).

From now on A is empty, G is a forest with an edge, and G is not a base case. Take a longest
path in a tree component that has an edge. Let v be an endpoint and u its neighbour. Every
neighbour of u except at most one (call it w) is a leaf.

**Case 1: u has two leaf neighbours v and v'.** Set x_{v'} := 0. Then F' = f_{G-v'}. The
cover number does not change, because u still covers the leaf v and some minimum cover of
both graphs contains u. So the drop is 1 and e >= 1.

**Case 2: deg u = 1** (the component is the edge uv, and G has another edge). Set x_u := 1.
Then F' = x_v OR f_{G-u-v} = F(G-u-v, {v}). The drop is -1 + 1 + 1 = 1 (A gains v, one
edge is lost, tau falls by 1), and e >= 1.

**Case 3: deg u = 2**, with neighbours v (a leaf) and w. Here w is not a leaf, otherwise
Case 1 applies, so G - u still has an edge (from w). Two identities are used:
tau(G-u-v) = tau(G-u) = tau(G) - 1, because u lies in a minimum cover. Also
F|_{x_v=1} = x_u OR f_{G-u-v} = F(G-u-v, {u}), by absorption, so that substitution has drop
-1 + 2 + 1 = 2. F|_{x_v=0} = f_{G-v} has drop at most 2.

- *3a: x_v has at least 2 readers.* Set x_v := 1. Then e >= 2 and the drop is 2.
- *3b: x_v has one reader g, and g is AND-type with controlling constant c.* Set x_v := c.
  This makes g constant. Neither restriction of F is constant, so g is not the output, and
  by (M2) it has a reader h. So e >= 2 and the drop is at most 2.
- *3c: x_v has one reader g = x_v XOR y XOR k* (y is a wire that does not depend on x_v).
  Set x_u := 0. Then F' = f_{G-u}, in which v is isolated. Two edges are lost and tau falls
  by 1, so the drop is 3. Because F' does not depend on x_v, we may also replace x_v by the
  wire y; y comes before g, which is x_v's only reader. Now g reads y twice and is
  constant. g is not the output, because f_{G-u} is not constant, so its readers R_g
  (nonempty) also have a constant input. Hence e >= |readers(x_u) ∪ {g} ∪ R_g|, where
  g ∉ R_g. We need e >= 3:
  - If some reader of x_u lies outside {g} ∪ R_g, or |R_g| >= 2, then e >= 3.
  - Otherwise R_g = {h} and readers(x_u) ⊆ {g, h}. Use two inputs that set every variable
    except x_u, x_v to 0, either leaving x_w = 0 or setting x_w = 1. At these inputs F is
    x_u x_v and x_u respectively.
    * readers(x_u) = {g}: then y = x_u, and x_u, x_v reach the output only through
      g = x_u XOR x_v XOR k. But x_u x_v is not a function of x_u XOR x_v. Contradiction.
    * readers(x_u) = {g, h}: then h is a function of (x_u, x_v) alone, and it is their only
      route to the output. A single bit cannot determine both x_u x_v and x_u, since
      determining x_u forces h = ±x_u. Contradiction.
    * readers(x_u) = {h}: then h reads g, so g comes before h. Hence y depends on neither
      x_v (g is its only reader) nor x_u (otherwise x_u → h → … → y → g → h is a cycle).
      At the second input (x_w = 1, other variables 0), y is a constant b, and the output
      equals φ(h), where h = op'(x_u, x_v) := op(x_u, x_v XOR b XOR k) with k folded in. By
      (M1), op depends on its g-input, so there is a value a with op'(a, ·) nonconstant. At
      x_u = a, F = x_u = a is constant while h takes both values, so φ is constant. Then F
      cannot depend on x_u at this input, yet F = x_u there. Contradiction.

Every case has e >= the drop, and every substitution lowers the number of relevant
variables. The other cases (u with three or more neighbours) are covered by Case 1. This
completes the induction.

## Computer checks (SAT, Kissat)

Exact B2 minimum sizes were found with a Kulikov-style CNF encoding (`note-2-scripts/b2sat.py`). The
normalisations used are (M1), (M2), op(0,0) = 0 and a free output polarity, all valid for
minimum circuits. The encoding reproduces the known values OR_n = XOR_n = n - 1 for n = 3..5
and MAJ_3 = 4.

| graph | \|E\|+tau-1 | B2 minimum |
|---|---|---|
| P3, P4, P5, P6 | 2, 4, 5, 7 | 2, 4, 5, 7 |
| stars S3, S4 | 3, 4 | 3, 4 |
| C4 | 5 | 3 (the known exception) |
| C5 | 7 | 7 |
| C6 | 8 | 8 |
| P7 | 8 | 8 |
| spider (three legs of length 2) | 8 | 8 |

Every forest without isolated vertices on at most 6 vertices, up to isomorphism, was also
checked by solving "size |E|+tau-1 is possible" and "size |E|+tau-1-1 is impossible"
(`note-2-scripts/forests.py`; output in `note-2-scripts/forests.out`). All 19 such forests agree with |E|+tau-1, with no
mismatches.

## Limitations

- This is a hand proof. It is not a Lean proof against the repository's `BinaryCircuit`
  definitions. Its only review so far is by an AI referee, not by a person.
- It covers forests only. The long-thread and cycle classes of Note 1 (a) and (c) are not
  covered. C5 and C6 agree with |E|+tau-1 in B2 by computer, but these are only two data points.
- The bound is linear, at most about 1.5n, so it has no bearing on CircuitBreaker's 3.1n
  baseline or on superlinear lower bounds.
- Novelty is unknown. Gate elimination with XOR-type cases is standard, and the
  "replace an irrelevant variable by a wire" step is a known trick.
