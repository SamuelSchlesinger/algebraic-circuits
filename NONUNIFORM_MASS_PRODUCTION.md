# Nonuniform mass production: proof status

The existing explicit recursive theorem remains fully proved as
`BlockInduction.exponentialMassProduction`. The new nonuniform route is not
yet a complete circuit-complexity theorem in this checkout.

The added modules prove, without new axioms or proof placeholders:

- An exact exponential collision bound, using a two-coloring of a spanning
  forest to justify conditional independence. Repeated targets are allowed.
- One fixed phase menu covering all occupied states and target tuples under
  `512 * capacity * |K| <= number of projective directions`.
- At most `capacity * (2 + 3 * addressBits)` candidate lines per menu and
  acceptance of exactly `ceil(active/2)` clean requests.
- A concrete shared propagation circuit costing exactly two charged gates
  per record, and record payload broadcast costing at most
  `records * (6 * keyWidth + 4)` per payload bit.
- A complete two-sort batched table lookup, including repeated queries,
  metadata preservation, and fixed output wires. For
  `T = 2^keyWidth + requests`, the charged cost is at most
  `256 * T * (ceil(log2 T) + keyWidth + valueWidth + 2)^5`.
- A complete candidate-selection circuit: sort requests by clean flags,
  sort whole candidate blocks by their success bit, and select a clean
  prefix from one successful candidate by fixed output wires.
- Computed-key sorting and exact collision marking, with preserved distinct
  identifiers returning every record and duplicate flag to its original
  position. Their bounds are linear in record count with polynomial width
  and sorting-depth factors.
- A duplicate-flag circuit that adds its own fixed ordering identifiers, and
  a shared batched OR circuit accepting repeated source keys, repeated
  queries, and absent keys. Their charged costs are bounded respectively by
  `256 * records * (depth + keyWidth + 1)^5` and
  `256 * (sources + queries + 1) * (depth + keyWidth + valueWidth + 2)^5`.
- An assembled enumerated-menu evaluator: shared occupancy lookup, point
  collisions within each candidate, aggregation into exact clean-request
  flags, and selection of one candidate's clean prefix. Request payloads
  survive as a permutation, and the complete circuit has an explicit bound
  linear in point count up to polynomial width and sorting-depth factors.
- A fixed-direction point generator using precomputed field offsets. Its
  `2^width` scalar slots represent precisely a punctured line after marking
  the zero scalar invalid, with at most one gate per output bit.
- A complete universal geometric phase circuit under the packing budget.
  One fixed power-of-two menu works for every encoded occupied state and
  target tuple; its successful-candidate premise is discharged by counting.
  It accepts the rounded-up half prefix, preserves original request data
  and complete line-point lists, and has an explicit total phase cost bound.
- Common-zero-block monomial line parity, independence of reduced monomial
  evaluations, and existence of a systematic information set of exact size
  `A^m - (A-1)^m` over `A^m` points. Here `A = 2^(dimension * blockWidth)`
  and the field width is `blockWidth * m`. This subsequence of field widths
  suffices for the intended asymptotic packing argument.
- A finite rate bound and packing bound with at most one codeword of
  rounding overhead, plus recovery of the original Boolean bit and
  injectivity of disjoint scheduled resource incidences.

The menu construction, information set, and source-bit placement are
nonuniform choices made offline. Their existence is proved, not assumed.

Still required for the manuscript's new end-to-end bound:

1. Compose state compaction and all halving phases, using the now-proved
   universal geometric phase circuit. The iteration still requires a
   correctness proof and a total scheduler cost bound.
2. Integrate that circuit and the high-rate code with the resource bank and
   routing pipeline, then prove the exponential-range parameter estimates
   and the coefficient `1 / (1 - gamma)` in the integer precision model.

The now-proved batched lookup can include code number, information point,
and bit selector together in its offline table. This avoids runtime division.

Neither the old theorem nor the existence of a short menu alone proves these
remaining circuit costs. The new coefficient must not be described as fully
formalized on the basis of this checkpoint.

Validation commands:

```sh
lake build Algebraic AlgebraicTests --wfail
lake test
lake lint
git diff --check
```
