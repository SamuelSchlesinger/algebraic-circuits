# Three-input circuit-star geometry

The fixed [protocol](protocol.md) was recorded before the search. The complete
[dataset](n3.json) contains all 256 native shared-DAG circuit minima, witnesses,
SAT-search outcomes and encoding hashes, both constant-link filtrations, minimal
missing supports, augmented F2 Betti numbers, dual facets, and neighborhood
volumes. These finite circuit minima are experimental evidence. They are not
Lean-certified circuit lower bounds.

## Reproduce and check

The recorded run used Python 3.14.5, python-sat 1.9.dev4, and CaDiCaL 1.9.5
(`cadical195`). It completed in 6.398 seconds on the local workspace machine.
Timing is provenance, not a comparative performance claim.

```sh
python3 -m pip install 'python-sat==1.9.dev4'
python3 scripts/circuit_star_experiment.py --width 3 --output research/circuit-stars/n3.json
python3 scripts/check_circuit_star_experiment.py
```

The checker first enumerates two-input semantic DAG states independently of
the SAT encoding and compares every bounded SAT answer with those minima.
It then verifies source and CNF hashes, search records, every three-input
witness by direct bitwise evaluation, and every minimum-size lower query with
Glucose 4. Finally it recomputes all recorded geometry. These checks passed.
They share the three-input encoding and do not constitute kernel-checked UNSAT
certificates. Run Python normally, without `-O`, so assertions remain enabled.

All AND, OR, NOT, identity, and constant gates cost one. Earlier values can be
reused without limit; input and designated output wires are free. Each gate
chooses one instruction and every truth-table row is constrained. Equal binary
arguments reduce to identity. Padding with identity gates makes the fixed final
output encoding complete for circuits of size at most the budget, including
circuits whose output is an earlier wire. No input-negation or NPN quotient is
used. Truth-table bit `x` is the value on binary assignment `x`, with coordinate
zero the least significant bit.

The exact size histogram is:

| Native size | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Functions | 3 | 11 | 26 | 44 | 37 | 82 | 35 | 10 | 8 |

## The first obstruction invisible to the graph

At both constant centers, budget 5 is the first level with a minimal missing
face of cardinality greater than two. A common example is

```text
S = {001, 010, 100}, truth-table support mask 22.
```

At the zero center, the full corner is the exactly-one function. Its native
complexity is 7. Empty, singleton, and two-point subsets of this support have
complexities 1, 3, and 5 respectively. Thus all proper subsets form faces at
budget 5 while the triple does not. The full opposite corner around one also
has complexity 7 and every proper pattern is available at budget 5.

One seven-gate shared circuit for exactly-one is:

```text
a = y AND z
b = y OR z
c = x AND b
d = a OR c
e = NOT d
f = x OR b
output = e AND f
```

The OR value `b` is reused. This is a DAG computation, not a formula count.

The zero link has five minimal missing triples at this budget, with masks
`22, 104, 134, 146, 148`; the one link has `22, 41, 73, 97, 104`.
Each also has seven minimal missing pairs. Complete lists at every budget
are retained in the dataset, rather than selecting only the displayed example.

## How the links change

Both centers have the following face counts and reduced Betti numbers. Equal
counts do not mean their labeled face families are identical.

| Budget | Face counts, cardinalities 0 through 8 | Nonzero reduced Betti numbers over F2 |
| --- | --- | --- |
| 0 | 0,0,0,0,0,0,0,0,0 | none; void family |
| 1 | 1,0,0,0,0,0,0,0,0 | beta[-1]=1 |
| 2 | 1,1,0,0,0,0,0,0,0 | none |
| 3 | 1,8,12,0,0,0,0,0,0 | beta[1]=5 |
| 4 | 1,8,12,0,0,0,0,0,0 | beta[1]=5 |
| 5 | 1,8,21,18,3,0,0,0,0 | beta[2]=1 |
| 6 | 1,8,28,48,36,0,0,0,0 | beta[3]=9 |
| 7 | 1,8,28,53,56,30,4,0,0 | beta[4]=2 |
| 8 | 1,8,28,56,70,56,28,8,1 | none; full simplex |

The initial cube graph persists from budget 3 to 4. Later, its one-dimensional
cycles disappear and homology occurs in higher degrees. The Betti table alone
does not determine homotopy types or the maps between successive homology
groups. It therefore does not establish a wedge-of-spheres classification or
a persistence barcode.

The independently constructed Alexander dual has facets complementary to the
minimal missing faces. Its augmented boundary ranks verify the dual dimension
relation in every degree and at every budget, including the void and full
cases. Over F2 the homology and cohomology dimensions agree by matrix transpose
rank, which is the numerical convention used here. The new Lean duality theorem
is independent of this finite computation and concerns actual reduced homology
and cohomology quotients.

## Neighborhoods reveal information lost by the volume bound

The ambient truth-table cube has 256 vertices and dimension 8. Here are the
radius-one neighborhoods of the easy sets and the capped counting bound.

| Budget | Easy functions | Radius-one neighborhood | Capped union bound |
| --- | --- | --- | --- |
| 0 | 3 | 27 | 27 |
| 1 | 14 | 90 | 126 |
| 2 | 40 | 171 | 256 |
| 3 | 84 | 226 | 256 |
| 4 | 121 | 240 | 256 |
| 5 | 203 | 254 | 256 |
| 6 | 238 | 254 | 256 |
| 7 | 248 | 256 | 256 |
| 8 | 256 | 256 | 256 |

At budgets 5 and 6, the two vertices still outside the radius-one neighborhood
are parity and its complement, masks 150 and 105. Both have distance exactly
two to the easy set. The counting bound alone already allows a neighborhood
of the entire cube at budget 2, so it cannot detect these remaining holes.
This finite observation supplies no superlinear lower bound for parity as the
input width grows.

## Formal endpoints and remaining comparisons

The [library guide](../../docs/circuit-stars.md) records the proved general and
native obstruction criteria, encoder/decoder bounds and concrete repetition
and coordinate-subcube instances, XOR transport, approximation distance and
neighborhood bounds, and combinatorial and homological Alexander duality.

The homological theorem is over F2, on augmented finite simplicial chains. It
does not assume a comparison with singular homology or prove integral torsion
statements. The finite circuit minima and numerical Betti table above are not
imported as Lean axioms. The experiment suggests later classification targets;
the generic theorems provide tools for those targets without supplying a new
asymptotic explicit circuit lower bound.

The earlier graph-incidence cycle ranks and the new simplicial homology
quotients remain separate formal interfaces; their comparison is a further
library target. The general Alexander duality equivalence above is proved
without assuming that comparison.

## Validation of this development

The following completed successfully on Lean/Mathlib v4.33.1:

```sh
lake build Algebraic AlgebraicTests --wfail
lake test
lake lint
scripts/build_docs.sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_circuit_star_experiment.py
```

The geometry audit checks all 1,042 owned declarations, including private
helpers, against `propext`, `Classical.choice`, and `Quot.sound`. The downstream
tests include a nonzero triangle homology class, transpose-differential checks,
finite-dimensional homology/cohomology instances, augmented empty-face cases,
and native repetition, transport, obstruction, and distance interfaces. All
12 new generated module pages contain their principal declarations.

Documentation generation replayed warnings about equational-lemma extraction
in upstream Lean, Lake, and Mathlib declarations; the new module pages generated
successfully. The documentation remains a local artifact.
