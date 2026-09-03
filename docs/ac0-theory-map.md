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

The constant-sharpening layer follows the combined block encoding in Paul
Beame's
[*A Switching Lemma Primer*](https://homes.cs.washington.edu/~beame/papers/primer.ps).
A block stores its queried source positions as a subset and records path bits
relative to the assignment satisfying the selected term. Every block followed
by another block must contain a mismatch. This removes the redundant boundary
bit and excludes the all-zero difference string from every nonfinal block.

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
| Restrictions | Partial assignments, composition, and restricted semantics | Same-variable semantics and reversible live-refinement algebra validated 2026-09-03; circuit simplification open |
| Normal forms | Literals, bounded-width CNF/DNF, and decision trees | Exact De Morgan duality and structural depth-`d` tree conversion to width-`d` DNF/CNF validated 2026-09-03 |
| Probability | Finite `p`-random restriction distribution | Exact product PMF, live-coordinate marginal, survivor expectation, and good-outcome averaging validated 2026-09-03 |
| Switching | Explicit finite switching lemma | Semantic all-width `(5pt)^s` DNF and CNF decision-tree theorems validated 2026-09-03 |
| Depth reduction | Iterated simplification of bounded-depth circuits | Variable-probability, variable-tree-bound semantic iteration proved with explicit survivor schedules; closed-form parameters open |
| Parity | Restriction resilience and top-gate obstruction | Reducing every layer below a parity output now forces the final live count below the tree bound; closed-form parameters open |
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

The parity top-gate submilestone passed the full gates on 2026-09-03. If a
parity circuit has logical depth at most `i+1` and every wire through depth
`i` becomes a decision tree of depth at most `t`, Lean proves that at most
`t` variables remain live. If the output is already in the reduced layers,
the exact decision-tree lower bound applies. Otherwise checked input-negation
normal form forces the output to be an AND or OR in the next layer, where the
exact bounded CNF or DNF representation and its parity width lower bound
apply. The theorem makes no syntactic top-gate assumption and is the bridge
that permits only `d-1` restriction rounds for depth `d`. The audited public
theorem uses no axioms beyond Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`.

The restricted-parity normal-form submilestone passed the full gates on
2026-09-03. Every DNF computing parity under a nonconstant restriction has a
term containing all live variables, and every such CNF has a clause containing
all live variables. Hence width at most `t` forces `liveCount rho <= t` in
both cases. The proof is the standard sensitivity argument: flipping an
absent live variable preserves the witnessing term or falsified clause but
changes parity. This supplies the top-gate obstruction needed to stop depth
reduction after `d-1` rounds, without forcing the entire top formula into a
decision tree. It is uniform in arity and performs no formula enumeration or
finite optimization. The audited public theorems use no axioms beyond Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

The variable-parameter depth-reduction submilestone passed the full gates on
2026-09-03. Lean now iterates explicit schedules `p_i`, `t_i`, and `a_i` under
the per-round bounds `delta_i <= p_i` and
`delta_i*a_i+a_(i+1) < p_i*a_i`, where
`delta_i = S(5*p_i*t_i)^(t_(i+1)+1)`. The tree-bound schedule is required to
be monotone, allowing the first transition `1 -> t` and later transitions
`t -> t`. Finite induction returns one cumulative restriction with the final
semantic invariant and survivor guarantee. This is the structural schedule
theorem needed for the standard `d-1`-round parity argument; no asymptotic
choice or computational witness search is hidden in it. The audited public
theorems use no axioms beyond Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`.

The two-parameter live-variable extraction submilestone passed the full gates
on 2026-09-03. For source bound `s`, target bound `t >= s`, current live count
`m`, and desired survivor count `k`, Lean now extracts a concrete refinement
whenever `delta*m+k < p*m`, with `delta = S(5ps)^(t+1)`. The refinement both
advances the shallow invariant one logical layer at target bound `t` and keeps
at least `k` variables live. The proof combines the exact switching estimate
with the exact survivor first moment; it defines no sampler, optimizer, or
finite search. The audited public theorems use no axioms beyond Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

The two-parameter layer-switching submilestone passed the full gates on
2026-09-03. If layers through `i` have decision-tree depth at most `s`, a
fresh restriction advances through layer `i+1` with target depth `t >= s`
except with probability at most `S(5ps)^(t+1)`. This separation is essential
for the source-faithful first step from literal width one to target depth `t`;
subsequent steps may use source and target depth `t`. It prevents an
artificial extra factor of `t` in the first switching base and preserves the
standard parity lower-bound exponent `1/(d-1)`. The result is semantic and
uniform in all finite arities; it performs no circuit enumeration, optimizer
search, or fixed-size experiment. The audited public theorems use no axioms
beyond Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The parameterized parity-circuit contradiction passed the full gates on
2026-09-03. A shallow invariant covering the unique designated output of a
parity circuit now forces `liveCount rho <= t`. Combining this with iterated
depth reduction proves that any explicit survivor schedule ending above `t`
rules out the circuit, provided `delta <= p` and every scheduled step satisfies
`delta*a_i + a_(i+1) < p*a_i`, with
`delta = S(5pt)^(t+1)`. This is the complete structural switching argument at
the circuit level; choosing closed-form values for `p`, `t`, and `a_i` is the
remaining quantitative obligation. The audited public theorems use no axioms
beyond Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The parity-resilience submilestone passed the full gates on 2026-09-03. The
library now records the evaluation path followed by an arbitrary decision
tree and proves that agreement on its queried coordinates forces the same
output, without assuming read-once form. Reusing the canonical Boolean-ring
parity function, Lean proves that flipping any coordinate left live by a
partial assignment changes the restricted function. Hence every live
coordinate lies on every evaluation path of every computing tree, giving the
lower bound `liveCount rho`; the structural Shannon tree over the live set
gives the matching upper bound. Thus restricted parity has decision-tree
depth at most `t` exactly when `liveCount rho <= t`. No truth-table search or
finite lower-bound certificate is involved. The audited public theorems use
no axioms beyond Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`.

The iterated semantic depth-reduction submilestone passed the full gates on
2026-09-03. For a survivor schedule `a_i`, a common tree-depth allowance `t`,
and `delta = S(5pt)^(t+1)`, the checked hypotheses `delta <= p` and
`delta*a_i + a_(i+1) < p*a_i` now yield one cumulative restriction under
which every wire through logical layer `d` has decision-tree depth at most
`t` and at least `a_d` variables remain live. The proof separately establishes
that the room inequality is monotone above each scheduled minimum, then uses
finite induction and associative restriction refinement. It contains no
sampling or witness search. Closed-form parameter selection and the parity
contradiction remain open. The audited public theorems use no axioms beyond
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The existential layer-advancement submilestone passed the full gates on
2026-09-03. Writing `m` for the current live count and
`delta = S(5pt)^(t+1)` for the charged switching failure bound, Lean proves
that `delta*m + k < p*m` yields one refinement which both advances
`ShallowUpTo` by a full logical layer and retains at least `k` live variables.
The proof combines the circuit-level failure estimate with exact survivor
averaging; it does not compute or search for the witnessing restriction. The
semantic invariant is also proved monotone in its common decision-tree depth
allowance, furnishing the base conversion needed for iteration. The audited
public theorems use no axioms beyond Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`.

The live-variable averaging submilestone passed the full gates on 2026-09-03.
Each coordinate is proved live with probability exactly `p`, and finite
linearity gives
`E[liveCount (rho.refine sigma)] = p * liveCount rho` exactly. Splitting this
first moment across an arbitrary bad event of probability at most `delta`
proves that, whenever `delta*m + k < p*m`, some good refinement of a state
with `m` live variables retains at least `k`. This is an exact finite
averaging argument, not a sampler, concentration heuristic, optimizer, or
finite circuit search. The audited public theorems use no axioms beyond
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

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

The next-layer formula-composition submilestone passed the full gates on
2026-09-03. Finite indexed DNF families are flattened by disjunction and CNF
families by conjunction, preserving a common width bound and agreeing exactly
with the zero- or arbitrary-fan-in AC0 interpretation. From a
`ShallowUpTo rho i t` witness, Lean chooses exact width-`t` forms for every
argument of a connective gate at logical depth at most `i + 1`, then proves
that their aggregate computes the actual restricted internal gate function.
Thus an OR gate receives an exact width-`t` DNF and an AND gate an exact
width-`t` CNF, independent of the gate's fan-in. This is the deterministic
composition premise for the next switching step; the charged-gate union bound
remains open. The audited public theorems use no axioms beyond Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

The one-step semantic layer-switching theorem passed the full gates on
2026-09-03. Under checked input-negation form, every non-connective gate is
proved to have logical depth zero, so advancing a layer only requires new
bounds for charged AND/OR gates. For a base witness
`ShallowUpTo program rho i t`, exact DNF/CNF gate representations and the
switching lemma give each next-layer gate failure probability at most
`(5pt)^(t+1)`. A finite union over the proved connective-gate set yields the
circuit-level endpoint
`Pr[not ShallowUpTo program (rho.refine sigma) (i+1) t]
  <= S * (5pt)^(t+1)`,
where `S = program.cost andOrCost`. The event predicates are classical only
for exact finite probability formation; no decision-tree optimizer or finite
circuit experiment is implemented. Iterating this step while retaining enough
live variables is the next open obligation. The audited public theorems use no
axioms beyond Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The semantic-layer invariant submilestone passed the full gates on 2026-09-03.
`Program.ShallowUpTo rho i t` states that every wire through source logical
depth `i` has semantic decision-tree depth at most `t` after `rho`. It is
proved stable under further restrictions, and checked input negations give the
depth-zero base case via explicit one-query literal trees. Every argument of
an AND or OR gate is proved to have strictly smaller logical depth, furnishing
the induction step's structural premise. Separately, the finite set of
connective gates is proved to have cardinality exactly the program's charged
AND/OR cost; later union bounds therefore charge the source circuit size
rather than raw program gates containing free NOTs. Advancing the invariant
through one full connective layer using bounded DNF/CNF composition is the
next open obligation. The audited public theorems use no axioms beyond Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

The decoder-algebra extension to partial assignments passed the same gates on
2026-09-03. Clearing exactly the coordinates added by a live-only refinement
is proved to recover the original restriction. A second pointwise identity
proves that replacing the head satisfying assignment by its original path bit
commutes with retaining the tail refinement. These are general restriction
identities; they do not assume or search over any circuit family.

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

The canonical-trace submilestone passed the same gates on 2026-09-03. Every
path through the canonical tree now has a typed transcript partitioning its
queries into the successive source terms chosen by the dynamic canonical
procedure. Each block records the first surviving term and its live support;
the constructors distinguish continuing within a term from returning to term
selection. This is structural proof data, not an enumeration of paths or
circuits. The next step is to turn each query into bounded source-term position,
block-boundary, and relative path-bit advice and prove the corresponding
decoder.

The bounded-advice submilestone passed the same gates on 2026-09-03. A traced
query is assigned its position in the selected source term, a block-boundary
bit, and whether its path bit differs from the satisfying literal value. For a
positive width bound `t`, the formal
advice alphabet has exactly `4 * t` symbols and length-`s` advice has exactly
`(4 * t)^s` possibilities. The hidden satisfying assignment is proved to fix
exactly the path's `s` distinct coordinates and only coordinates initially
live in the input restriction. Every encoded source position is also proved
to recover the hidden coordinate from the selected source term. The explicit
replay-and-clear decoder, hence injectivity and the probability bound, remains
open.

The satisfying-compatibility submilestone passed the same gates on
2026-09-03. Within a selected source-term block, the hidden extension is proved
pointwise either live or equal to the corresponding satisfying literal value.
This avoids the incorrect invariant that the original path state continues to
satisfy the term: a path bit may falsify it while the encoding deliberately
uses the satisfying bit. As a consequence, refining by the hidden extension
preserves the first-surviving source term exactly. This selector equation is
the semantic premise for deterministic decoder replay.

The replay-decoder submilestone passed the same gates on 2026-09-03. The
decoder is a total structural program: it selects the first surviving source
term at block boundaries, reads the advised bounded support position,
reconstructs the path bit from its recorded difference, and continues or
restarts according to the block bit. A mutual trace proof shows that replay
recovers the exact original query coordinates. Clearing precisely those
coordinates from the refined output is then proved to recover the original
restriction. Thus the decoder is a kernel-checked left inverse for every valid
canonical trace encoding; choosing traces uniformly over the bad event and
instantiating the weighted injection theorem remain open.

The canonical-injection submilestone passed the same gates on 2026-09-03.
For every restriction in the canonical-depth-`s` event, proof-level classical
choice selects an exact-length structural path and its source-term trace. The
resulting total encoder is proved injective on the event by the explicit
decoder, and its extension fixes exactly `s` initially live coordinates. The
weighted engine now gives the exact division-free inequality
`((1-p)/2)^s * Pr[bad] <= (4t)^s * p^s`

for every positive width bound `t` and `0 <= p <= 1`. This is already a finite,
kernel-checked switching estimate. Converting it under `p <= 1/9` to the
standard intermediate `(9pt)^s` statement, handling zero-width edge cases,
and then sharpening to the source target `(5pt)^s` remain open.

The positive-width analytic corollary passed the same gates on 2026-09-03.
Under `p <= 1/9`, the fixed-coordinate mass satisfies
`(1-p)/2 >= 4/9`. Monotonicity raises this inequality to the `s`th power,
and the finite nonzero factor `(4/9)^s` is cancelled explicitly from the
scaled encoding bound. The resulting checked statement is
`Pr[canonical depth >= s] <= (9pt)^s`.

This is the constant delivered by the present one-position/two-bit advice
alphabet and is recorded as an intermediate bound, not as the final
Hastad-style `5pt` switching lemma. The constant-sharpening argument remains a
separate obligation.

The zero-width edge case passed the same gates on 2026-09-03. A typed trace
for a width-zero DNF is proved to have no query steps: any nonempty canonical
block would exhibit a surviving term with positive live-support length,
contradicting its zero width. Therefore every positive canonical-depth event
has probability zero; threshold zero is discharged by the general unit upper
bound. The public `(9pt)^s` theorem now covers every natural width `t`. Only
the sharper source-target constant remains open at this switching stage.

The combined-advice counting submilestone passed the same gates on 2026-09-03.
Advice is partitioned into source-term blocks. A block of length `i` chooses an
`i`-element subset of the `t` bounded positions and an `i`-bit difference
string; every block with a nonempty tail excludes the all-zero string. Lean
proves the exact first-block cardinality recurrence and the uniform bound
`|CombinedAdvice t s| <= ((5t - 1)/2)^s`

for positive `t`. The proof is symbolic and structural; it performs no
formula, path, or circuit enumeration. Connecting canonical traces to this
advice type and proving its replay decoder remain open, so this count is not
yet advertised as a `(5pt)^s` switching lemma.

The relative-value replay refinement passed the same gates on 2026-09-03. The
elementary advice alphabet still has exactly `4t` symbols per query, but its
value bit now records the XOR difference from the selected literal's satisfying
value. The decoder derives that satisfying value from the reconstructed source
term and cancels the XOR, so the existing replay, injection, scaled bound, and
all-width `(9pt)^s` theorem remain kernel-checked. This semantic alignment is
needed before the block-boundary bit can be removed by combined advice.

The combined-advice replay surface passed the same gates on 2026-09-03. Each
stored position subset is expanded in increasing source order, a closing marker
is synthesized only for nonfinal blocks, and the flattened list is proved to
have exactly length `s`. A generic replay theorem proves that clearing the last
closing marker changes no decoded coordinate, and `decodeCombined` reuses the
existing replay-and-clear semantics. The remaining obligation is to construct
this advice from every canonical trace and prove the flattening correspondence.

The replay surface also exposes checked smart constructors for a final block
and for prepending a continuing block to a nonempty tail. Their flattening
equations are definitional interfaces for the forthcoming trace packer: the
final block receives no closing marker, while every prepended continuing block
receives exactly one at its last query. This is structural assembly, not a new
switching estimate; the trace-to-advice construction remains open.

The canonical block-extraction submilestone passed the full gates on
2026-09-03. Canonical paths are now partitioned into maximal source-term
blocks, and flattening those blocks is proved to recover the elementary advice
after forgetting its boundary bit. Every block is nonempty, its source
positions are strictly increasing, its length is at most the formula width,
and all block lengths sum exactly to the path length. Most importantly, Lean
proves the semantic condition used by the combined count: every nonfinal block
has a nonzero relative difference string. If all its bits were zero, the
selected term would remain first surviving after its last live variable was
fixed, contradicting the start of a later nonempty block. Packaging these raw
blocks into the indexed `CombinedAdvice` type remains open.

The combined canonical-packing submilestone passed the full gates on
2026-09-03. Strictly ordered raw blocks are converted to finite position
subsets and indexed difference functions; the proved nonzero condition is
carried into every continuing `CombinedAdvice` block. Re-expansion is proved
to synthesize exactly the elementary boundary transcript, with only the final
closing marker cleared because replay ignores it. Consequently the existing
replay-and-clear decoder is now a checked left inverse for combined advice on
every bounded canonical path. The remaining switching-stage task is to replace
the elementary total encoder by this combined encoder and apply the already
proved `((5t - 1)/2)^s` cardinality bound in the weighted probability argument.

The combined canonical-injection submilestone passed the full gates on
2026-09-03. The bad-event encoder now stores `CombinedAdvice t s`, and the
explicit combined decoder proves that this encoder is injective. Applying the
general weighted restriction engine and the checked cardinality theorem gives
the exact positive-width inequality
`((1-p)/2)^s * Pr[canonical depth >= s] <= (((5t-1)/2)^s) * p^s`.

This is the finite trusted core of the sharp switching estimate. The remaining
analytic step is to cancel the fixed-coordinate weight and derive the standard
readable `Pr[canonical depth >= s] <= (5pt)^s`, including the zero-width and
large-parameter cases already handled for the earlier nine-constant theorem.

The sharp canonical switching lemma passed the full gates on 2026-09-03. For
`5pt <= 1`, Lean proves the one-step inequality
`((5t-1)/2) * p <= ((1-p)/2) * (5pt)`, raises it to the `s`th power, and
cancels the finite nonzero fixed-coordinate weight. For `5pt > 1`, the result
follows from probability at most one; width zero and threshold zero are handled
explicitly. Thus the public theorem now has no artificial small-`p` premise:
`Pr[canonical depth >= s] <= (5pt)^s`

for every width bound `t`, threshold `s`, and `0 <= p <= 1`. This completes the
finite switching-lemma milestone. The next dependency is a formula-level
simplification theorem connecting bounded canonical decision-tree depth to the
usual restricted DNF/CNF decision-tree statement used in depth reduction.

The semantic DNF switching theorem passed the full gates on 2026-09-03. Event
monotonicity transfers the canonical estimate to the representation-independent
predicate saying that every tree computing the restricted DNF has depth at
least `s`. Thus the public endpoint now matches the usual decision-tree form:
`Pr[DT(F restricted by rho) >= s] <= (5pt)^s`.

An equivalent checked corollary makes the integer convention explicit:
`Pr[not (DT(F restricted by rho) <= d)] <= (5pt)^(d+1)`.

Semantic depth-event decidability is classical and noncomputable; it exists
only to form the exact finite probability. No optimizer, circuit enumeration,
or finite lower-bound search is implemented. The complementary CNF statement
and its explicit De Morgan bridge are the next switching-layer obligation.

The De Morgan duality and CNF switching submilestone passed the full gates on
2026-09-03. Literal negation is involutive, preserves support and width, swaps
term conflicts with clause hits, and commutes with residual restriction.
Consequently DNF/CNF negation commutes exactly with syntactic restriction and
complements semantics. Negating every leaf preserves both upper and lower
semantic decision-tree depth, so the checked DNF theorem yields the matching
CNF bound and its explicit `d+1` off-by-one form without a second encoding
argument. The next dependency is simultaneous simplification of many bottom
gates for circuit-level depth reduction.

The finite-family switching submilestone passed the full gates on 2026-09-03.
For `M` width-`t` DNFs, and separately for CNFs, Lean proves
`Pr[exists i, DT(F_i restricted by rho) >= s] <= M * (5pt)^s`, together with
the explicit failure-of-depth-`d` form using exponent `d+1`. The proof is the
exact finite union bound over the single-formula theorem. It is not advertised
as the stronger multi-switching lemma, since it does not construct one common
decision tree for all formulas. The next obligation is to extract the bottom
normal-form gates of an alternating AC0 circuit into such a finite family.

The literal-input gate conversion passed the full gates on 2026-09-03. A
finite family of signed literals is represented by one term or clause when
repeated coordinates agree. If opposite signs occur, the conjunction is
proved constantly false and the disjunction constantly true. Both conversions
are semantically exact for arbitrary fan-in and have width at most that
fan-in. This closes the duplicate/opposite-literal edge case needed before
extracting bottom gates from the shared circuit DAG; it does not enumerate
truth tables or search for a smaller normal form.

The shared-DAG bottom-gate extraction passed the full gates on 2026-09-03.
Source logical depths are now available for every internal gate and wire. Lean
proves that a depth-zero internal gate must be NOT, and the checked
input-negation condition then proves that every depth-zero wire computes an
explicit signed original-input literal. Every connective argument of a
logical-depth-one gate is therefore a literal. A depth-one AND gate is
extracted as a width-at-most-fan-in DNF and a depth-one OR gate as the dual
CNF, each pointwise equal to the actual internal gate function. Only the one
gate is represented as a formula; the surrounding circuit remains a shared
DAG. The next obligation is to gather the relevant bottom gates into the
finite switching family and formalize their simultaneous replacement.

The padded bottom-family submilestone passed the full gates on 2026-09-03.
All `g` program indices are retained: an eligible logical-depth-one gate of
fan-in at most `t` receives an exact width-`t` representation, while every
other index receives the appropriate constant DNF or CNF. This avoids subtype
enumeration and preserves the standard size factor. Combining the padded
family with the switching union bound proves, for both connectives,
`Pr[some eligible bottom gate has restricted DT depth >= s]
  <= g * (5pt)^s`,
as well as the explicit failure-of-depth-`d` form. The event is stated for the
actual restricted internal gate functions, not merely their extracted syntax.
The next obligation is to turn simultaneous shallow decision trees into an
explicit depth-reduced program while controlling size and logical depth.

The decision-tree normal-form bridge passed the full gates on 2026-09-03.
Every tree is converted structurally to an exact DNF whose terms correspond
to accepting paths. Repeated queries are handled semantically: matching
literals are retained once and contradictory paths are discarded. Lean proves
that every resulting term has width at most the tree depth. De Morgan duality
then gives the matching CNF theorem, and both constructions lift to the
representation-independent statement that every function of decision-tree
depth at most `d` has exact width-`d` DNF and CNF representations. This is a
symbolic traversal of a supplied tree, not a truth-table expansion or a search
for an optimal tree. The next obligation is to substitute these bounded forms
for simultaneously switched bottom gates while tracking program size and
logical depth. The audited endpoint theorems use no axioms beyond Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.
