# Constant stars in the circuit-complexity cube

Use `import Algebraic.CircuitGeometry` for the full development, or the
focused modules listed below. The cost `C(f)` counts every native De Morgan
gate, including constants, NOT, and identity gates. Input and output wires
are free, and circuits may share intermediate results.

The ambient cube has `2^n` coordinates, one for each input assignment.
For a constant `b` and a set `S` of input assignments, write

```text
corner_b(S)(x) = if x in S then !b else b
H_b(S)        = max_(T subset S) C(corner_b(T)).
```

The direction set `S` belongs to the link at budget `s` precisely when
`H_b(S) <= s`. It determines a cube of dimension `|S|` incident to `b`,
or a simplex of dimension `|S|-1` in the link. The empty direction set is
included in the combinatorial link when the center is admitted; the
Mathlib `PreAbstractSimplicialComplex` interface omits that empty face.

## Exact shape at budget n

For every `n > 0` and either constant center, Lean proves that the link at
budget `n` is exactly the input-cube graph `Q_n`:

- Every singleton direction is admitted.
- Two distinct directions span an edge exactly when their input
  assignments differ in one bit.
- No direction set of cardinality greater than two is admitted.

Thus the exact counts are

```text
link vertices = 2^n
link edges    = n * 2^(n-1)
cycle rank    = n * 2^(n-1) + 1 - 2^n.
```

For example, the links have 5 independent cycles at `n=3` and 17 at `n=4`.
`constantLinkCycleRank` is the dimension of an actual graph incidence
kernel over any field. Its proof uses an equivalence between the admitted
two-direction faces and canonical input-cube edges, followed by
rank-nullity. There are no square fillings in this one-dimensional link.
No comparison theorem with singular homology is assumed.

The closed star itself is contractible. `mem_closedStar_iff_exists_directions`
identifies its realization with the union of admitted incident cubes,
and `closedStar_starConvex` supplies the straight-line contraction through
Mathlib. These are the cubes of the cubical cone on the link. A separate
homeomorphism to a packaged cone type is not formalized.

The circuit lower bound behind the missing edges applies to shared DAGs.
A function supported at two nonadjacent assignments, or its complement,
depends essentially on every input and is not unate. A backward frontier
argument proves that a fully essential function computed with at most
`n-1` binary gates admits a read-once expression. At total size at most
`n`, this forces unateness. Consequently the two-exception functions cost
at least `n+1`. This proves that every nonadjacent pair is a minimal
missing face; it does not assume the original circuit is a formula.

## When the constant stars first meet

Let `M(n)` be maximum native circuit complexity on `n` inputs and `tau(n)`
the first budget where the two geometric closed stars intersect. Lean
proves that such an intersection exists exactly when there is a common
Boolean star vertex. The checked finite bounds are

```text
M(n)     <= 2*tau(n) + 2
tau(n+1) <= M(n) + 1.
```

For the first inequality, let `h` be a common vertex. Every function below
`h` is cheap, as is every function above it. Given arbitrary `f`, both
`a = f AND h` and `b = h OR NOT f` therefore cost at most the meeting
budget. The identity `f = a OR NOT b` uses two additional gates.

For the second inequality, the first input projection is a common vertex
at budget `M(n)+1`: every function below or above that projection is a
masked function on the other `n` inputs.

The existing Shannon counting and synthesis theorems yield the proved
asymptotic endpoint

```text
eventually:  2^n <= 4*n*tau(n)  and  n*tau(n) <= 32*2^n.
```

This is an integer formulation of `tau(n) = Theta(2^n/n)`. A native-cost
bridge shares the two constants, converting a standard-cost circuit into
a native circuit with only two additional gates. The proof therefore
does not silently change cost conventions.

Meanwhile, the constants already have a simple path at budget `n+1`.
Path connection and intersection of their entire incident stars occur on
very different scales. These results describe worst-case complexity;
they do not identify an explicit family with exponential circuit size.

## Birth profiles and structured supports

The birth function has the following checked properties:

```text
S subset T  implies  H_b(S) <= H_b(T)
H_b(S union {x}) <= H_b(S) + 2*n
H_b(S) <= 1 + 2*n*|S|
H_!b(S) <= H_b(S) + 1
H_b(all inputs) = M(n).
```

The complement inequality applies in both directions, giving a one-gate
interleaving of the two link filtrations. The cardinality bound supplies
a guaranteed simplex skeleton at every budget.

Every missing face contains a minimal missing face. For a minimal missing
face `S`, its opposite corner is hard, all proper exception patterns are
cheap, and `H_b(S) = C(corner_b(S))`. In particular, the birth of a
nonadjacent pair is exactly the complexity of its two-exception function.
The existence theorem alone does not give an efficient way to recognize
minimal missing faces at large budgets.

Large supports can nevertheless be cheap when they are structured. Fix
`k > 0` initial input bits and leave `d` bits free. The resulting support
has `2^d` assignments, and the library proves, for either center,

```text
H_b(inputSubcube fixed d) <= M(d) + k + 1 <= M(d) + 2*k.
```

Every exception pattern is a function on the `d` free inputs, combined
with a `k`-input mask. The halfcube `x_0=true` around zero, and the halfcube
`x_0=false` around one, have the sharper bound `M(d)+1`. These statements
provide reusable upper bounds against which
candidate hard supports can be compared. They do not classify all later
faces or supply a new asymptotic explicit lower bound.

## Focused API

| Module | Principal endpoints |
| --- | --- |
| `BooleanCube.Star`, `BooleanCube.Link` | `faceBirth`, `firstMeeting`, `linkComplex`, `exists_minimalMissing_subset` |
| `BooleanCube.StarRealization` | `mem_closedStar_iff_exists_directions`, `closedStar_contractible` |
| `Basis.DeMorgan.Star` | `mem_constantLink_iff`, `constantLinkGraph_eq_cube`, `pair_minimalMissing_iff` |
| `Basis.DeMorgan.StarCycles` | `constantLinkFaceCount_one`, `constantLinkFaceCount_two`, `constantLinkCycleRank_eq` |
| `Basis.DeMorgan.StarIntersection` | `maximumComplexity_le_twice_constantStarMeeting`, `constantStarMeeting_succ_le` |
| `Basis.DeMorgan.StarAsymptotics` | `eventually_constantStarMeeting_bounds`, `exists_constant_path` |
| `Basis.DeMorgan.StarBirth` | `constantFaceBirth_pair_eq`, `exists_minimal_hard_support`, `constantLink_subset_complement` |
| `Basis.DeMorgan.StarSubcube` | `card_inputSubcube`, `constantFaceBirth_inputSubcube_le` |

Module paths in this table have the prefix `Algebraic.`. The downstream
regressions are in `AlgebraicTests.CircuitStars`. The geometry axiom audit
also checks every declaration in the supporting star modules, including
private helpers, against the permitted axioms `propext`, `Classical.choice`,
and `Quot.sound`.
