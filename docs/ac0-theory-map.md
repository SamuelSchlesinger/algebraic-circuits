# AC0 theory map

This document records the source correspondence and trust boundary for the
nonuniform constant-depth circuit development. It is a roadmap, not evidence
that unchecked milestones have been proved.

## Source convention

The quantitative endpoint follows Johan Hastad,
[*Computational Limitations for Small-Depth Circuits*](https://people.kth.se/~johanh/thesis.pdf)
(MIT Press, 1986), Chapter 5, Theorem 5.1, and the closely related STOC paper
[*Almost Optimal Lower Bounds for Small Depth Circuits*](https://doi.org/10.1145/12130.12132)
(1986).

The source model has arbitrary-fan-in AND and OR gates, negations only at input
literals, depth equal to the number of gate levels on a longest input-output
path, and size equal to the number of AND/OR gates. General negations can be
pushed to inputs with at most a factor-two size increase. The source theorem
rules out depth-`k` parity circuits of size
`2^((1/10)^(k-1) * n^(1/(k-1)))`

for `n > n0 ^ k`, for an absolute constant `n0`. The Lean development will use
an exact natural-number inequality underneath this real-exponent notation and
derive a source-facing corollary only after rounding has been proved.

The switching endpoint is the decision-tree form of Hastad's switching lemma,
stated explicitly in the introduction of
[*Criticality of AC0-Formulae*](https://eccc.weizmann.ac.il/report/2022/182/):
for a width-`t` DNF under a `p`-random restriction, the probability that the
restricted function has decision-tree depth at least `s` is at most
`(5 * p * t)^s` (the complementary CNF statement follows by negation). Exact
probability and small-`p` side conditions will remain visible in the finite
theorem.

The distinguished DNF decision tree follows the standard dynamic canonical
construction: restrict the full ordered DNF at the current path, choose the
first surviving term, query all of its live variables in input-coordinate
order, and repeat after the resulting path assignment. This is deliberately
not an optimal-tree computation. The formal switching event is the depth of
this concrete tree; semantic correctness then relates it to ordinary
existential decision-tree depth.

The injective probability calculation follows the weighted presentation in
Neil Thapen's
[*Notes on switching lemmas*](https://arxiv.org/abs/2202.05651), Section 1,
which adapts the Razborov--Beame encoding proof to independently sampled
restrictions. The trusted Lean statement is kept division-free: if an
injection extends every bad restriction by exactly `s` formerly live
coordinates, then
`((1 - p) / 2)^s * Pr[bad] <= |advice| * p^s`.

## Existing-library convention audit

- `Circuit sigma n g m` is a shared, topologically ordered DAG with `g`
  internal gates and free designated output wires.
- `Circuit.size` is exactly `g`.
- Inputs have depth zero; every internal operation, including a unary NOT if it
  is represented as a gate, adds one to depth.
- `InputSubstitution` already gives semantic substitution and single-variable
  fixing, while `DeMorgan.ProgramRestriction` performs basis-specific partial
  evaluation for the binary De Morgan basis.
- The Hastad model therefore needs its own arbitrary-fan-in basis and a
  negation-normal representation. Internal NOT gates cannot silently be made
  free or depthless in the generic circuit model.

## Milestones

| Milestone | Formal endpoint | Status |
| --- | --- | --- |
| Families | Nonuniform families with exact polynomial-size and constant-depth predicates | Validated 2026-09-03 |
| AC0 basis | Arbitrary-fan-in AND/OR semantics and source-faithful normal form | Basis, logical resources, class predicate, and checked normal form validated; normalization theorem open |
| Restrictions | Partial assignments, composition, and restricted semantics | Same-variable semantic layer validated 2026-09-03; circuit simplification open |
| Normal forms | Literals, bounded-width CNF/DNF, and decision trees | Dynamic canonical DNF tree, semantic correctness, and live-variable depth bound validated 2026-09-03 |
| Probability | Finite `p`-random restriction distribution | Exact normalized product PMF validated 2026-09-03 |
| Switching | Explicit finite switching lemma | Weighted-injection engine and exact canonical path transcripts validated 2026-09-03; term-position decoder and final bound open |
| Depth reduction | Iterated simplification of bounded-depth circuits | Not started |
| Parity | Restriction resilience and quantitative depth-`k` lower bound | Not started |
| Class separation | Qualitative `PARITY` not in nonuniform `AC0` | Not started |

## Claim labels

- **Literature theorem:** a statement matched to the cited source.
- **Formalization strengthening:** a proved compositional or exact finite form
  not asserted to be new mathematics.
- **Research candidate:** an unproved statement, excluded from public theorem
  dependencies.
- **Barrier:** a general proved obstruction to a proposed route.
- **Computational observation:** test evidence only; it cannot discharge a
  mathematical milestone.

## Validation record

The family milestone passed `lake build Algebraic AlgebraicTests --wfail`,
`lake test`, `lake lint`, and `git diff --check` on 2026-09-03. Its public
resource lemmas use no axioms or only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; they do not use `sorryAx`, custom axioms,
or executable proof certificates.

The AC0 basis submilestone passed the same gates on 2026-09-03. The regression
suite checks arbitrary-fan-in OR semantics, AND/OR cost, the distinction between
generic depth and source logical depth, checked input-negation normal form, and
a nonvacuous AC0 family computing disjunction. A normalization construction for
arbitrary internal negations has not yet been proved.

The partial-assignment submilestone passed the same gates on 2026-09-03. It
defines same-variable Boolean restrictions, sequential refinement, exact live
sets and counts, conversion to `InputSubstitution`, restriction of scalar and
multi-output targets, and the proof that restricted semantics depend only on
live coordinates. Its public theorem audit uses no axioms beyond Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

The literal-normal-form submilestone passed the same gates on 2026-09-03.
Terms and clauses contain at most one signed occurrence of each variable by
construction; outer DNF and CNF lists retain a deterministic order for the
later canonical decision tree. Restriction is proved semantically exact for
terms, clauses, DNF, and CNF, and is proved not to increase width. The audited
headline theorems use no axioms beyond Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. Decision trees are not part of this
submilestone.

The decision-tree foundation passed the same gates on 2026-09-03. It includes
explicit false/true branching syntax, evaluation, depth and leaf counts,
negation, semantic restriction, structural composition of restrictions, and
depth monotonicity. A constructive Shannon expansion proves the universal
`n`-variable depth upper bound without defining an optimizer or performing a
search. The audited headline theorems use no axioms beyond Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. The canonical tree used in the
switching proof is supplied by the following submilestone.

The canonical-DNF-tree submilestone passed the same gates on 2026-09-03. At
each path it restricts the entire ordered formula before selecting the first
surviving term, so assignments to earlier terms simplify all later terms. It
queries that term's remaining coordinates in canonical input order and
recurses on the strictly smaller live-variable set. The tree is proved to
compute the restricted DNF, its depth is proved at most the live-variable
count, and its decidable depth event is related to the representation-
independent decision-tree lower-depth predicate. No optimal-tree search or
finite lower-bound experiment is defined. The audited headline theorems use
no axioms beyond Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`.

The random-restriction distribution passed the same gates on 2026-09-03. For
`0 <= p <= 1`, each coordinate has exact masses `p`, `(1-p)/2`, and `(1-p)/2`
for live, fixed-false, and fixed-true states. The finite product normalization
is proved, and every restriction's point mass is proved equal to
`p^(live count) * ((1-p)/2)^(fixed count)`. Event probability, complement, and
unit upper-bound lemmas are derived from that PMF. The audited normalization
chain uses no axioms beyond Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`.

The weighted switching-encoding submilestone passed the same gates on
2026-09-03. Refinement by an assignment supported on live variables has an
exact cross-multiplied point-mass identity. A general finite injective-
encoding theorem sums that identity without division, and its specialization
gives the displayed `s`-coordinate probability inequality. This is proof
infrastructure, not yet the switching lemma: the canonical path advice,
decoder, injectivity proof, and advice-cardinality estimate remain open. The
audited headline theorems use no axioms beyond Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`.

The canonical-path submilestone passed the same gates on 2026-09-03. Source
terms are selected by the first-not-falsified rule, and the implementation's
live support is proved identical to the ordered support of the residual term.
Canonical trees satisfy a structural read-once invariant. Consequently every
canonical-depth event supplies an exact-length path whose queried coordinates
are duplicate-free and initially live, and whose path assignment fixes exactly
that many coordinates. The remaining switching work is to label these paths
by bounded positions within source terms and prove the reconstruction decoder
injective.
