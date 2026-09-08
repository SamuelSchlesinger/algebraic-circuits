# Geometry of circuit complexity

Use `import Algebraic.CircuitGeometry` for this development. The generic
cube results live under `Algebraic.BooleanCube`; the concrete gate-count
results live under `Algebraic.DeMorgan`.

For smaller dependencies, import `Algebraic.Basis.DeMorgan.Geometry` for
paths, `Algebraic.Basis.DeMorgan.Topology` for the continuous contraction,
or `Algebraic.Basis.DeMorgan.Boundary` for coarea and perimeter bounds.
Use `Algebraic.Basis.DeMorgan.Betti` for finite cubical homology and the
complexity-shell counting bound.
`Algebraic.Basis.DeMorgan.Witness` adds localized witnesses and target
reductions; `Algebraic.Basis.DeMorgan.Locality` bounds certificates whose
boundary evaluations ignore fixed truth-table coordinates outside a chosen set.
For exact constant links, their cycle ranks, face birth profiles, and the
exponential first-contact theorem, see [constant stars](circuit-stars.md).

## Model

For an input width `n`, a truth table is a vertex of the cube with `N = 2^n`
coordinates. Each coordinate is an input assignment. Hamming distance counts
disagreements without normalization. Write `C(f)` for `DeMorgan.complexity f`
and `A_s = {f : C(f) <= s}`.

The cost is the minimum number of internal gates in the native shared
De Morgan circuit language. NOT, AND, OR, constant, and identity gates all
count; designated output wires are free. The measure agrees with the
generic `Circuit.gateComplexity`.

The erasure, path, and circuit-topology theorems assume `n > 0`. At `n = 0`,
both scalar Boolean functions have cost one. The coarea and perimeter
theorems include this case.

## Thresholds and erasure

`inputRank` orders assignments with the first input bit most significant.
It is injective and has values below `2^n`. For every interior threshold
`0 < t < 2^n`, `thresholdExpression n t` computes `[inputRank(x) >= t]` with
at most `n-1` AND/OR gates. It uses no constant or NOT gates. Endpoint
thresholds use a single constant gate.

The prefix-erasure function is

```text
R_t(f)(x) = if inputRank(x) < t then false else f(x).
```

The checked cost bound is

```text
C(R_t(f)) <= C(f) + n.
```

At interior thresholds append the threshold test and one AND gate. At the
two ends simplify directly to `f` or the zero function. The bound therefore
counts the original shared circuit only once.

## Paths and distance

`BooleanCube.graph` has adjacency exactly `hammingDist left right = 1`.
`BooleanCube.Within cost budget walk` bounds the cost of every vertex in
the walk's support. The path theorems additionally prove `walk.IsPath`,
which excludes repeated vertices.

For `f,g in A_s` the library supplies:

```text
a simple path from f to g inside A_(s+n);
a simple path of length exactly d_H(f,g) inside A_(2*s+n+1).
```

The first path erases each endpoint to zero and removes loops from the
concatenation. It connects the vertices already in `A_s`; it does not assert
that every newly admitted vertex of `A_(s+n)` belongs to that component.

The second path has the sharper pair-specific budget

```text
C(f) + C(g) + n + 1.
```

It first moves from `f` to `f AND g` through

```text
f AND (g OR [inputRank(x) >= t]),
```

then reverses the analogous sweep from `g`. It changes each disagreement
exactly once and preserves all agreements. The generic theorem
`hammingDist_le_length` proves that this length is minimal even among walks
in the full cube.

## Cubical topology

`BooleanCube.cubical A` is a subset of the real unit cube. A point belongs
when every Boolean vertex of the smallest cube face containing that point
belongs to `A`. Thus an edge, square, or higher face is filled exactly when
all its vertices are allowed. In particular, this construction does not
take the convex hull of the allowed vertices.

`BooleanCube.Sublevel cost s` is this geometric realization for a cost
sublevel. The main continuous-map theorem is

```text
K_s -> K_(s+n) is null-homotopic.
```

The proof continuously erases one coordinate at a time. Each intermediate
face has vertices of the form `R_t(f)` or `R_(t+1)(f)`, so the same gate
bound controls the whole homotopy. This is a single coherent contraction
of the inclusion, rather than independent choices of vertex paths.

The generic theorem accepts any injective, bounded coordinate ranking and
any cost satisfying `cost(R_t(f)) <= cost(f)+k`. Its conclusion is the
sublevel contraction with overhead `k`. An explicit zero-vertex premise
ensures that the target is nonempty even if the source is empty.

The cubical construction is the standard vertex-induced filtration; see
the lower-star discussion in
[Leygonie and Henselman-Petrusek (2024)](https://doi.org/10.1007/s41468-024-00165-w).
The circuit cost bounds and coherent erasure are supplied by the present
Lean development.

## Homology and persistence

The homology modules use Mathlib's actual singular homology functor,
with arbitrary coefficient objects in a preadditive category admitting
the required coproducts and homology.

The formal results show that a null-homotopic map acts as a constant in
every homology degree, and acts as zero in every positive degree.
Specializing the contraction gives

```text
H_k(K_s) -> H_k(K_(s+n)) is zero for k > 0.
```

Degree-zero connectivity is also proved directly by the graph path
theorem. The larger sublevel may contain newly born components or homology
classes; the conclusion concerns the image of the earlier sublevel.

In the usual reduced persistent-homology interpretation over a field,
these results imply that every interval has length at most `n`. This
repository does not define a barcode data structure or formalize the
interval-decomposition theorem. Its formal endpoints are the actual
continuous null-homotopy, graph paths, and singular homology maps.

## Finite cubical Betti numbers and complexity shells

The finite counting development uses the standard oriented cubical chain
complex over a coefficient ring. Its basis faces are vectors with entries
`some false`, `some true`, or `none`, with `none` indicating a free
coordinate. The chain module in degree `k` is spanned by the admitted faces
with exactly `k` free coordinates. The differential uses the product
orientation, and `Chains.boundary_boundary` proves that it squares to zero.

`Chains.Homology` is the quotient of cycles by boundaries. Over any field
`F`, `CubicalHomology.betti F A k` is its finite vector-space dimension.
`Face.mem_cubical_iff_exists_face` proves that the union of the admitted
closed faces is exactly the previously defined geometric `cubical A`.
The comparison isomorphism between this finite cubical homology and
Mathlib's singular homology is not formalized here. The numerical theorem
below is proved directly for cubical homology, without assuming that
comparison or any unproved topological theorem.

Let `beta_k(A_s;F)` denote this cubical Betti number, `N = 2^n`, and
`Shell_s = {f : s < C(f) <= s+n}`. For every field `F`, `n > 0`, and `k > 0`,
the checked theorem is

```text
beta_k(A_s;F) <= binomial(N,k+1) * |Shell_s|.
```

The proof has three finite steps:

1. The prism operator satisfies `d*h + h*d = id - augmentation`.
   Each face in its support is one dimension higher, and every vertex of
   that face is a prefix erasure of an original vertex. Thus the existing
   concrete erasure circuits put every positive-degree cycle's filling
   inside budget `s+n`.
2. Mathlib's rank-nullity and quotient-dimension theorems show that the old
   Betti number is at most the number of newly admitted `(k+1)`-faces.
   The generic result is `CubicalHomology.betti_le_card_new_faces`.
3. Each new face contains a new vertex. Its free-coordinate set and any
   contained vertex determine it uniquely. This gives the exact incidence
   bound of `binomial(N,k+1)` faces per new vertex.

`DeMorgan.inputIndexEquiv` identifies input assignments with their numerical
truth-table indices. `DeMorgan.truthTableEquiv` transports vectors back to
Boolean functions, and its shell-cardinality proof ensures that the final
right-hand side counts the original Boolean functions exactly once.

The public endpoint is `DeMorgan.cubicalBetti_le_choose_mul_shell`.
`AlgebraicTests.CubicalBetti` includes an explicit six-edge cycle in a cube
with opposite corners removed, proves it is not a boundary over the
rationals, and thereby certifies a positive first Betti number. It also
checks positive-degree vanishing for full cubes, zero-coordinate behavior,
and the generic-field shell theorem.

## Localized witnesses and the explicitness gap

For a chain `z`, `Chains.vertices` lists the vertices of its nonzero faces.
`Chains.erasureVertices` lists their prefix erasures, with thresholds between
zero and the ambient cube dimension `N`. The list has at most
`(N+1) * |vertices(z)|` entries before removing duplicates.

For a positive-degree cycle in `K_s` which does not bound there, the theorem
`DeMorgan.exists_shell_function_of_cycle` proves

```text
some g in erasureFunctions(z) satisfies s < C(g) <= s+n.
```

The list is determined by the cycle, rather than by a search through all
Boolean functions. Its hard member need not be efficiently identifiable.
The cycle's nonbounding property is an explicit premise.

`DeMorgan.complexity_add_overhead_gt_of_cycle` transfers the witness to a
specified function `f`: if every candidate `g` either has a certified
`C(g) <= s` or satisfies `C(g) <= C(f)+r`, then `s < C(f)+r`. Reductions
and nonbounding are still required; this theorem does not construct them.

A reusable way to certify nonbounding is
`Chains.not_mem_boundaries_of_cochain`. It accepts a linear cochain `phi`
which detects the proposed cycle and vanishes on the boundaries of every
admitted face in the next degree. The existing six-cycle regression checks
this interface and the extraction of a missing vertex together.

## A restriction on local cochain certificates

Let `Q` be a set of truth-table coordinates, and let `q = |Q|`.
`Face.truncate Q F` preserves the free coordinates of `F`, preserves its
fixed coordinates in `Q`, and sets all other fixed coordinates to false.
It has the same dimension as `F`. Each vertex of a truncated `(k+1)`-face
has at most `q+k+1` true truth-table entries.

The existing point-update circuits therefore give the exact bound

```text
C(v) <= 1 + 2*n*(q+k+1)
```

for every vertex `v` of such a truncated face. Now suppose a degree-`k`
cochain `phi`, with `k > 0`, satisfies both of the following conditions:

1. `phi(boundary F) = 0` for every `(k+1)`-face admitted at budget `s`.
2. `phi(boundary (truncate Q F)) = phi(boundary F)` for every `(k+1)`-face.

If `s >= 1 + 2*n*(q+k+1)`, every truncated face is admitted. Condition 2
then forces `phi` to vanish on every face boundary in the entire cube.
The full-cube contraction implies that it detects no positive-degree cycle.
Equivalently, `DeMorgan.budget_lt_of_local_cochain` proves that a detecting
certificate satisfying these conditions must have

```text
s < 1 + 2*n*(q+k+1).
```

This applies to the precise truncation invariance in condition 2. It is not
a limitation on arbitrary cochains, on all locally described algorithms, or
on all topological lower-bound methods. The coordinate set is a set of
truth-table entries, not a set of the function's input variables. For fixed
`q` and `k`, this class of certificates only reaches linear thresholds in `n`.

The current attempt establishes witness extraction, target transfer, and
this locality restriction. It has not produced a new explicit circuit
lower bound or a nonbounding certificate that scales to unrestricted
circuits. Exhaustively excluding small circuits would already prove the
corresponding finite lower bound and would not resolve that missing step.

## Boundaries and coarea

Every unoriented cube edge is stored once, by its endpoint whose changing
coordinate is false and that coordinate's index. For any natural-valued
cost and any upper bound `M` on it, Lean proves

```text
sum_(0 <= s < M) |edgeBoundary(A_s)|
  = sum_(cube edges {f,g}) abs(cost(f)-cost(g)).
```

An edge with costs `a <= b` crosses exactly the thresholds `a,...,b-1`.
`maximumCost` supplies a canonical finite upper bound. The exact cube edge
count is proved, including the zero-coordinate cube.

For circuit complexity this yields

```text
sum_s |edgeBoundary(A_s)| <= 2*n * N * 2^(N-1),  N = 2^n.
```

The boundary-band theorem also places the lower and upper endpoints of
each crossing edge within `2*n` gates of its threshold. This uses the
existing Lipschitz theorem; it does not identify the whole complexity band
with the boundary.

## Principal API

| Purpose | Theorem |
| --- | --- |
| Generic shortest prefix sweep | `BooleanCube.exists_patch_walk` |
| Generic coherent contraction | `BooleanCube.inclusion_nullhomotopic` |
| Generic coarea | `BooleanCube.sum_edgeBoundary_eq` |
| Threshold circuit size | `DeMorgan.thresholdExpression_gateCount_le` |
| Circuit prefix-erasure cost | `DeMorgan.complexity_erase_le` |
| Connectivity with additive overhead | `DeMorgan.exists_connecting_path_of_complexity_le` |
| Optimal-length path | `DeMorgan.exists_geodesic_of_complexity_le` |
| Continuous circuit-sublevel contraction | `DeMorgan.sublevel_inclusion_nullhomotopic` |
| Positive-degree homology maps | `DeMorgan.sublevel_homologyMap_eq_zero` |
| Exact circuit coarea | `DeMorgan.complexity_coarea` |
| Total circuit perimeter | `DeMorgan.complexity_totalBoundary_le` |
| Finite cubical chain contraction | `Chains.boundary_prism_add_prism_boundary` |
| Betti bound by new faces | `CubicalHomology.betti_le_card_new_faces` |
| Betti bound by new functions | `DeMorgan.cubicalBetti_le_choose_mul_shell` |
| Localized shell function | `DeMorgan.exists_shell_function_of_cycle` |
| Transfer to an explicit target | `DeMorgan.complexity_add_overhead_gt_of_cycle` |
| Nonbounding cochain certificate | `Chains.not_mem_boundaries_of_cochain` |
| Limit for truncation-invariant certificates | `DeMorgan.budget_lt_of_local_cochain` |

The public regression suite is `AlgebraicTests.CircuitGeometry`. It checks
the cost conventions, exact path lengths, zero-coordinate cases, and the
absence of a square interior when a corner is missing. It also audits every
declaration in the new library modules, including private helpers, and
rejects dependencies on any axiom other than `propext`, `Classical.choice`,
and `Quot.sound`.
