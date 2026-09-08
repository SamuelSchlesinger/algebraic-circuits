# Unrestricted Boolean circuit lower-bound research

The objective remains a superlinear size lower bound for an explicit Boolean
function family, against circuits with arbitrary two-input Boolean gates,
unrestricted depth, and shared intermediate wires. Here "explicit" is taken
in the intended open-problem sense: a polynomial-time computable family.
Counting hard truth tables or proving a restricted-model lower bound does not
meet this objective. No such superlinear lower bound has been proved here.

The current investigation uses Fusion as an organizing framework. The new
result below rules out one witness class within that framework. It does not
rule out Fusion itself.

## A verified ceiling for canonical graph witnesses

Let `G` be a bipartite graph on `N` labels per side, and let `U` be its set of
nonedges. For a positive edge `e = (u,v)`, define

```
R_u = { (u,b) in U }
C_v = { (a,v) in U }
F_e(A) = [R_u subset A or C_v subset A].
```

When both `R_u` and `C_v` are nonempty, `F_e` is a nontrivial upward-closed
family and is above `e` for the row/column generators. These are the
canonical semi-filters used in Section 4.2 of
[Cavalar and Oliveira](https://arxiv.org/html/2503.14117v1#S4.SS2).
Their graph-cover framework makes a super-logarithmic lower bound on full
graph cover complexity a sufficient route to a superlinear Boolean circuit
bound. Their inequality-graph example uses canonical semi-filters.

**Theorem proved in this checkout.** For every graph on `N = 2^n` labels per
side, with `n > 0`, its canonical semi-filters have a pair cover of length at
most `32n`. The graph need not be explicit or satisfy any regularity condition.

Proof: choose independent fair bits `r_a` for each row label and `c_b` for
each column label, and form the pair

```
E = { (a,b) in U : r_a = 1 }
H = { (a,b) in U : c_b = 1 }.
```

Fix a canonical edge `(u,v)`. Choose nonedges `(u,b)` and `(a,v)`; positivity
of `(u,v)` gives `a != u` and `b != v`. The four events

```
r_u = 1, r_a = 0, c_v = 1, c_b = 0
```

have joint probability `1/16`. On this event, `R_u` is contained in `E`, and
`C_v` is contained in `H`. But `(u,b)` witnesses that `R_u` is not contained
in `H`, and `(a,v)` witnesses that `C_v` is not contained in `E`. Hence

```
F_e(E) = F_e(H) = 1,    F_e(E intersect H) = 0.
```

Thus a single sampled pair violates each fixed canonical filter with
probability at least `1/16`. With `t` independent pairs, the probability that
some canonical filter survives is at most `N^2 * (15/16)^t`. For `t = 32n`,
this is less than one, since

```
N^2 * (15/16)^(32n) = [4 * (15/16)^32]^n < 1.
```

The Lean proof uses finite cardinalities throughout. It injects all colorings
into successful colorings paired with the four overwritten bits, and then
counts sequences and applies a finite union bound. It does not assume the
local probability estimate or independence as external hypotheses.

Formal endpoints:

- `Algebraic.Fusion.Graph.canonicalFilter_above`
- `Algebraic.Fusion.Graph.not_preservesPair_of_hits`
- `Algebraic.Fusion.Graph.sixteen_mul_misses_le`
- `Algebraic.Fusion.Graph.exists_canonical_cover`
- `Algebraic.Fusion.Graph.canonical_coverComplexity_le`

The conclusion bounds `pairCoverComplexity` with `canonicalClass graph` as
the admissibility predicate. It does not bound the quantity with
`SemifilterClass.all`. A lower bound obtained solely by covering these
canonical graph witnesses therefore cannot establish the desired
superlinear circuit bound. No claim of historical novelty is made; the
literature search was targeted, not exhaustive.

## Why larger semi-filters matter

Consider the graph with the single edge `(1,0)` on two labels per side. Its
nonedges are

```
a = (0,0), b = (0,1), c = (1,1).
```

The canonical filter for `(1,0)` accepts a set iff it contains `a` or `c`.
The pair `E = {a,b}`, `H = {b,c}` violates that filter. However, the
semi-filter consisting of **all nonempty subsets** is also above `(1,0)` and
preserves the pair: its intersection `{b}` is nonempty. Consequently this
pair covers every canonical witness in this graph but fails to cover every
admissible witness. This example is only a separation of witness classes;
the graph itself has full cover complexity one, using `({a},{c})`.

The script `canonical_fusion_check.py` exhaustively checks all bipartite
graphs with one, two, or three labels per side. It checks the four-bit
implication and the local cardinality bound for each canonical edge, then
constructs a greedy canonical cover. It also closes the generator family
under the proposed pairs to look for a surviving larger semi-filter. For
the example above, it independently checks upward closure, nontriviality,
the above-edge condition, and preservation of every proposed pair.

Reproduction:

```
python3 research/canonical_fusion_check.py
```

The exact run checks 530 graphs and 1,304 canonical edges. Its finite checks
are a separate sanity check; the universal upper bound is the Lean theorem.

Validation on 2026-09-08: `lake build Algebraic AlgebraicTests --wfail`
passed (3,490 jobs), `lake test` passed, `lake lint` passed, and
`scripts/build_docs.sh` passed (7,277 documentation jobs). Axiom audits
of the finite-cover lemma and all six public graph-cover theorems report
only `propext`, `Classical.choice`, and `Quot.sound`. They use no `sorryAx`,
custom axiom, or native decision procedure.

## Remaining mathematical work

A viable graph-Fusion route must prove a super-logarithmic cover lower bound
using witnesses beyond these minimal row/column-generated filters. For a
proposed list of pairs, begin with the complementary row and column of an
edge, close upward, and adjoin `E intersect H` whenever both `E` and `H` are
accepted. If this process stabilizes without accepting the empty set, it
gives a surviving semi-filter. The missing theorem is that, for a suitable
explicit graph family, every list of `O(log N)` pairs leaves such a witness
for some edge, with an unbounded improvement over the constant in `O`.
The existing cyclic Fusion machinery already handles this closure principle;
the hard part is the quantitative obstruction for an explicit graph.

This ceiling is specific to the canonical graph specialization. It does not
justify abandoning the general static perspective emphasized in
[Wigderson's Fusion lecture](https://simons.berkeley.edu/talks/circuit-lower-bounds-more-fusion-method).
It identifies a precise witness restriction that must be removed in this
particular route.
