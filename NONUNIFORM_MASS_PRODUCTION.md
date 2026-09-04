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

1. Assemble and verify the full batched prefix lookup. The offline lookup can
   include code number, information point, and bit selector together, using
   one record for each source prefix and avoiding runtime division.
2. Assemble candidate point generation, shared occupancy broadcast, collision
   detection, exact-half selection, compaction, and all halving phases into
   one circuit with a cost linear in the batch size up to polynomial factors
   in the bit widths.
3. Integrate that circuit and the high-rate code with the resource bank and
   routing pipeline, then prove the exponential-range parameter estimates
   and the coefficient `1 / (1 - gamma)` in the integer precision model.

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
