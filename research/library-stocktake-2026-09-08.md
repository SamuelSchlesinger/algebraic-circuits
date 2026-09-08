# Library stocktake and cleanup, 2026-09-08

The library has a substantial body of worthwhile circuit-complexity
formalization. The main problem is allocating further research effort and
presenting results at their actual strength. Wholesale removal of restricted
or classical lower bounds would discard much of its value.

The standard for this review follows the clarified project objective:
historically important lower bounds are valuable in their own right,
including restricted models. New techniques need a credible mechanism for
advancing a specified frontier. Correct definitions, a green build, or a
successful rephrasing of an old argument do not establish that mechanism.

This is a review of the research portfolio, public theorem statements,
selected proof dependencies, documentation, and build boundaries. It is not
a line-by-line mathematical audit of every proof or an exhaustive novelty
survey. Following the review, the user authorized the cuts recorded below.
The completed historical and restricted-model lower bounds are retained.

**Pre-cleanup snapshot and verification.** The reviewed HEAD is `185a2e9`. There are 515 tracked Lean
modules under `Algebraic/`, containing 122,947 physical source lines. These
counts exclude tests, generated files, dependencies, the root `Algebraic.lean`
facade, and the untracked DNF draft.

| Source tree | Modules | Source lines | Share of source lines |
| --- | ---: | ---: | ---: |
| `MassProduction/` | 209 | 50,063 | 40.7% |
| `LowerBound/Fusion/`, including its facade | 115 | 30,930 | 25.2% |
| `LowerBound/AC0/` | 42 | 13,325 | 10.8% |
| Remaining tracked library | 149 | 28,629 | 23.3% |

Size indicates maintenance exposure, not mathematical merit. The mass
production umbrella reaches every module in that subtree except
`RoutingAssembly.lean`, which is explicitly a compatibility facade. Its size
is therefore mostly an actual theorem dependency chain, not a collection of
disconnected experiments. The focused `Algebraic.Core` closure is 14 local
modules and 2,515 source lines, excluding Mathlib.

`lake build Algebraic AlgebraicTests --wfail` passed, reporting 3,902 jobs.
A fresh axiom check on 14 representative endpoints listed below reported
only `propext`, `Classical.choice`, and `Quot.sound`. The existing geometry
audit also passed for its 1,042 owned declarations. These checks establish
compilation and the checked axiom boundary, not novelty or significance.
Those were the checks on the pre-cleanup snapshot. Post-cleanup validation
is recorded separately below.

**Results that clearly earn their place.**

| Area | Concrete result and scope | Recommendation |
| --- | --- | --- |
| Shared circuit foundations | Programs preserve sharing; outputs may designate inputs or earlier gates; substitutions and translations carry semantic and cost guarantees. [Core](../Algebraic/Core.lean) | Keep as the stable foundation. Generality is serving multiple completed methods. |
| Fan-in and gate elimination | Essential-input size/depth bounds; parity requires at least `3(n-1)` AND/OR gates in De Morgan circuits, with NOT and constants free under `binaryCost`. [Parity theorem](../Algebraic/LowerBound/GateElimination/DeMorganXor.lean) | Keep. These are actual lower bounds with the basis-specific elimination step discharged. |
| Shannon counting | Factorial-improved finite census and coefficient-one almost-all lower bounds for fixed finite bases. [Shannon](../Algebraic/LowerBound/Counting/Shannon.lean) | Keep. Non-explicitness is part of this theorem's scope, not a reason to reject it. |
| Circuit size hierarchy | `SIZE(n^a)` is strictly contained in `SIZE(n^b)` for `1 <= a < b`, using point updates and counting. [Hierarchy guide](../docs/circuit-hierarchy.md) | Keep. This is an important use of the early truth-table geometry. |
| AC0 | The `(5pt)^s` switching bound, circuit depth reduction, quantitative parity bounds, and nonuniform parity separation. Raw shared DAGs allow arbitrary internal NOT placement, with explicit logical resource measures. [Theory map](../docs/ac0-theory-map.md) | Keep as a flagship historical development. It has a complete route from its main combinatorial lemma to circuit lower bounds. |
| Boolean monotone clique | For `w >= 16`, more than `w^w` gates for `w^4`-CLIQUE on `w^20` vertices, in the binary constant-free monotone shared model. [Endpoint](../Algebraic/LowerBound/Monotone/Clique/Exponential.lean) | Keep. This is a concrete finite specialization of Razborov's approximation method. |
| Monotone arithmetic separation | Clique-support polynomials over nonnegative rationals require at least `choose(v,k)-1` additions; arbitrary named nonnegative rational constants, including zero, are allowed. [Endpoint](../Algebraic/LowerBound/Fusion/Arithmetic/Progress/Separated/Clique/NNRat.lean) | Keep. This branch closes a real lower-bound argument in its stated model. Its placement under Fusion should not cause it to be dismissed as speculation. |
| Hessian rank | `ceil(rank(Hessian)/2)` multiplication lower bound with arbitrary field constants and cancellation. [Endpoint](../Algebraic/LowerBound/Fusion/Arithmetic/Interaction/Hessian.lean) | Keep as a classical arithmetic method. Its basic `n`-by-`n` rank measure has a linear ceiling; extending the API alone cannot change that ceiling. |
| Waring and rectangle/rank methods | The squarefree monomial in `2n` variables requires at least `centralBinom(n)` power terms over characteristic-zero fields; the diagonal needs one admissible rectangle per entry. [Waring](../Algebraic/LowerBound/Fusion/SumOfTerms/Waring.lean), [rectangles](../Algebraic/LowerBound/Fusion/SumOfTerms/Rectangle.lean) | Keep the concrete restricted-model results and their necessary rank/coverage tools. Count terms or admissible rectangles explicitly; do not report these as general multiplication bounds. |
| General and cyclic Fusion | Circuit-to-cover extraction; exact equality between full pair-cover complexity and binary cyclic AND complexity for finite set problems whose generators cover the ambient space. [Completeness](../Algebraic/LowerBound/Fusion/Cyclic/Complete.lean) | Keep. This is an established framework and a substantive characterization. The cyclic computational model must remain explicit. |
| Canonical graph witness ceiling | All canonical row/column witnesses admit a cover of length at most `32n` when each graph side has `2^n` labels. [Result and separation example](boolean-fusion.md) | Keep as a useful negative result. Stop searching for a super-logarithmic lower bound using only that witness class. |
| Mass production and synthesis | Complete circuit constructions, including Uhlig-range coefficient-one mass production and the proved real-rate coefficient `1/(1-gamma)+epsilon` for fixed `gamma<1`. [Public statements](../Algebraic/MassProduction.lean), [real-rate theorem](../Algebraic/MassProduction/Nonuniform/RealTheorem.lean) | Keep as a substantial synthesis component. These are upper bounds, but they provide benchmarks and expose failures of naive direct-sum intuitions. Historical attribution and any novelty of the strengthened range/coefficient are separate from the checked proof. |

The source correspondence for switching is supported by
[Hastad's thesis](https://people.kth.se/~johanh/thesis.pdf) and
[Thapen's notes](https://arxiv.org/abs/2202.05651).
The circuit hierarchy is stated explicitly as Theorem 6.1 of
[ECCC TR25-045](https://eccc.weizmann.ac.il/report/2025/045/download).
The modern cover/cyclic Fusion correspondence is the subject of
[Cavalar and Oliveira](https://arxiv.org/abs/2503.14117).
These references support the classification; this review does not claim
historical priority for the library's formulations or exact constants.

**Applied cuts.**

- Removed 43 library modules in the later truth-table geometry branch:
  star births and intersections, cubical sublevels and boundaries, homology,
  Betti bounds, and Alexander duality. Removed the `Algebraic.CircuitGeometry`
  facade, four dedicated test modules, the geometry guides, and the star
  experiments. The committed development remains available at `185a2e9`.
- Preserved [point updates and Hamming Lipschitz complexity](../Algebraic/Basis/DeMorgan/Complexity.lean),
  the [hierarchy theorem](../Algebraic/LowerBound/Hierarchy.lean), and the
  direct [support/read-once bounds](../Algebraic/Basis/DeMorgan/TightCircuit.lean).
  Extracted expression and AND/OR/NOT/XOR complexity bounds and input rewiring
  into [Operations.lean](../Algebraic/Basis/DeMorgan/Operations.lean).
  [Masks](../Algebraic/Basis/DeMorgan/Mask.lean),
  [pair-indicator bounds](../Algebraic/Basis/DeMorgan/PairIndicator.lean),
  numerical threshold circuits, and shared-constant compilation remain
  usable without the retired topology. `BooleanCube.Neighbors` now defines
  the input-cube graph directly.
- Removed the untracked DNF-star draft, its bipartite-cover helper, and its
  experiment and note. The draft parity file did not compile and was never
  part of the public build. A future formalization of the classical DNF
  parity bound can use the existing AC0 normal-form infrastructure directly.
- Moved the noncommutative recurrence and its examples into
  [standalone research material](noncommutative/README.md), removing its
  public facade and test import. The missing circuit-to-rank reduction is
  documented explicitly. The numerical estimate remains independently
  checkable.
- Removed nine conditional modules below
  `Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular`:
  `Support`, `Block`, `Cover`, `Cover.Occurrence`, `Cover.Exponential`,
  `Profile.Occurrence`, `Profile.Support`, `Profile.Block`, and `Profile.Cover`.
  Their facade imports and the conditional cover-budget regression were
  removed. These branches were not dependencies of the completed Hessian,
  Waring, or concrete arithmetic applications.

The surviving arithmetic interaction machinery includes the generic rank
certificates, Hessian results, polynomial coefficient and quotient methods,
concrete multi-output bounds, and the degree/decomposition tools used by
Waring restriction and compilation. In particular,
`Rectangular.Profile.Decomposition` is retained because the binary Waring
compiler uses it. Import reachability alone was not the removal criterion:
completed theorem endpoints remain worthwhile even when no other module
imports them.

**Why the speculative branches were cut.** Face birth is
`H(S) = max_{T subset S} C(1_T)`. At the full direction set it equals maximum
circuit complexity, even though the full opposite corner is constant one.
A large birth value therefore does not make that corner hard. Minimal
missingness adds the required implication, but independently establishing
it remains the difficult part. This development supplied no scalable
criterion yielding a new lower bound for a specified target. The cut is a
research-priority decision, not an impossibility theorem about geometry.

The removed rectangle-cover endpoint assumed a cover budget at every
retained multiplication occurrence and concluded
`centralBinom(n) <= multiplicationCost * coverBudget`. Its target, a product
of `2n` variables, has a circuit using `2n-1` multiplications. Thus the
exponential quantity can force a large local cover budget on an easy
circuit. Hessian and Waring earn their place because their local estimates
are proved from the stated circuit or term model.

**Documentation and validation.** Public imports and README links now point
to the retained results. The stale integration warning in `HighRate.lean`
now points to the completed real-rate mass-production theorem. The original
AC0 milestone logs remain historical documentation.

The main library now contains 462 Lean modules and 115,610 physical source
lines, down from 515 modules and 122,947 lines. These counts exclude tests,
the root facade, dependencies, and research files.

The post-cleanup checks passed:

- `lake build Algebraic AlgebraicTests --wfail` (3,498 jobs), `lake test`,
  and `lake lint` (no findings).
- `lake env lean research/noncommutative/DescendingChain.lean`.
- A fresh full-public-import audit of 14 retained lower-bound and synthesis
  endpoints found only the standard logical axioms and confirmed that all
  58 removed library/draft modules are absent from the imported environment.
- `scripts/build_docs.sh` (7,062 jobs). doc-gen4 replayed upstream equation
  extraction warnings, but site generation completed successfully. The
  generated Algebraic module set exactly matches the public import closure;
  removed modules have no pages, navigation entries, or search entries.
- Local Markdown links, public Lean imports, shell syntax, and whitespace
  checks passed.

The documentation script now clears generated HTML and per-module search
data before rebuilding, and regenerates the bibliography output. This
prevents doc-gen4's incremental merge from restoring deleted modules while
preserving the cached documentation database and extraction markers.

The focused `AlgebraicTests.NativeDeMorgan` suite checks the extracted
operations, shared-constant costs, thresholds, support/read-once bounds, and
adjacent versus nonadjacent exceptional inputs for both output values. Its
axiom audit passed for all 264 declarations owned by the nine retained or
extracted modules, including private helpers. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed.
