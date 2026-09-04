import Algebraic.MassProduction.Nonuniform.PhaseSelection
import Algebraic.MassProduction.Nonuniform.SortedPropagation
import Algebraic.MassProduction.Nonuniform.BatchLookupBound
import Algebraic.MassProduction.Nonuniform.CandidateSelection
import Algebraic.MassProduction.Nonuniform.DuplicateFlags
import Algebraic.MassProduction.Nonuniform.BatchOrCircuit

/-!
# Nonuniform scheduling: proved components

`existsUniversalPhaseMenu` proves one fixed menu works for every legal
occupied state and target tuple. `phaseMenuCandidateCount_le` bounds the
number of examined candidate lines by `capacity * (2 + 3 * addressBits)`.
`HalfClean.existsHalfSelection` gives exactly half-sized progress with
disjoint recovery lines.

`Propagation.circuit_cost` and `Broadcast.payloadCircuit_cost_le` prove
concrete linear-size propagation primitives. `BatchLookup.existsCircuit`
proves complete batched lookup, including repeated queries and fixed output
wires, with linear record-count dependence and polynomial width factors.
`CandidateSelection.circuit_selects` selects a successful candidate and a
clean prefix. `MarkDuplicates.circuit_correct` detects all key collisions and
returns their flags to the original record positions. Both have explicit
circuit-size bounds.
`DuplicateFlags.circuit_eval_iff` adds the ordering identifiers automatically.
`BatchOr.existsCircuit` proves shared OR aggregation with repeated or absent
source keys and a linear record-count bound.
The complete menu evaluator, its circuit-size bound, and the new direct mass-production theorem have
not yet been assembled. These component theorems do not assert those costs.
-/
