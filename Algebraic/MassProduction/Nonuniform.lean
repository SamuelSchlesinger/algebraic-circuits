import Algebraic.MassProduction.Nonuniform.PhaseSelection
import Algebraic.MassProduction.Nonuniform.SortedPropagation
import Algebraic.MassProduction.Nonuniform.BroadcastCircuit

/-!
# Nonuniform scheduling: proved components

`existsUniversalPhaseMenu` proves one fixed menu works for every legal
occupied state and target tuple. `phaseMenuCandidateCount_le` bounds the
number of examined candidate lines by `capacity * (2 + 3 * addressBits)`.
`HalfClean.existsHalfSelection` gives exactly half-sized progress with
disjoint recovery lines.

`Propagation.circuit_cost` and `Broadcast.payloadCircuit_cost_le` prove
concrete linear-size propagation primitives. The complete menu evaluator,
its circuit-size bound, and the new direct mass-production theorem have
not yet been assembled. These component theorems do not assert those costs.
-/
