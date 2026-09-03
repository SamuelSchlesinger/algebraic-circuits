import Algebraic.LowerBound.AC0.ParityCircuit
import Algebraic.LowerBound.AC0.ParityNormalForm

/-!
# The top-gate obstruction for parity circuits

Standard AC0 depth reduction stops one layer below the circuit output. If the
output already lies in the reduced layers, restricted parity's exact
decision-tree depth gives the contradiction. Otherwise the output is a genuine
next-layer connective: an OR has a bounded-width DNF and an AND has a
bounded-width CNF, so the restricted-parity normal-form lower bound applies.

This module packages that case split without assuming that the designated
output is syntactically a top AND or OR. Input outputs and input negations are
handled by their logical depth. Thus a depth-`i+1` parity circuit whose wires
through depth `i` are shallow leaves at most the common tree bound many
variables live.
-/

namespace Algebraic
namespace AC0
namespace Circuit

/-- Reducing all but the possible top logical layer of a parity circuit is
enough to bound its remaining live variables. -/
theorem liveCount_le_of_shallowBelowTop_computes_parity
    {circuit : Algebraic.Circuit signature n g 1}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depthBound : logicalDepth circuit ≤ level + 1)
    (shallow : Program.ShallowUpTo circuit.program rho level bound) :
    rho.liveCount ≤ bound := by
  let output := circuit.outputs 0
  have outputDepth :
      Program.logicalWireDepths circuit.program output ≤ level + 1 :=
    logicalWireDepth_output_le circuit 0 (level + 1) depthBound
  have outputComputes :
      circuit.program.wireFunction interpretation output =
        Parity.function n :=
    wireFunction_output_eq_parity_of_computes computes
  by_cases priorDepth :
      Program.logicalWireDepths circuit.program output ≤ level
  · exact shallow.parity_liveCount_le output priorDepth outputComputes
  · revert outputDepth priorDepth outputComputes
    refine Fin.addCases
      (fun input outputDepth outputComputes priorDepth => ?_)
      (fun gate outputDepth outputComputes priorDepth => ?_) output
    · exfalso
      apply priorDepth
      simp
    · have gateDepth :
          Program.logicalGateDepths circuit.program gate ≤ level + 1 := by
        simpa using outputDepth
      have connective :
          (circuit.program.lines gate).op.connective ≠ none := by
        by_contra notConnective
        have depthZero :=
          Program.logicalGateDepth_eq_zero_of_not_connective
            circuit.program normal gate notConnective
        apply priorDepth
        simp [depthZero]
      have gateComputes :
          circuit.program.gateFunction interpretation gate =
            Parity.function n := by
        simpa only [Algebraic.Program.wireFunction_gate] using
          outputComputes
      cases operation : (circuit.program.lines gate).op with
      | not => simp [operation, Op.connective] at connective
      | and fanIn =>
          obtain ⟨formula, bounded, represents⟩ :=
            shallow.exists_cnf_for_and_gate gate operation gateDepth
          exact formula.liveCount_le_width_of_computes_parity
            rho bound bounded (fun input => by
              simpa [gateComputes] using represents input)
      | or fanIn =>
          obtain ⟨formula, bounded, represents⟩ :=
            shallow.exists_dnf_for_or_gate gate operation gateDepth
          exact formula.liveCount_le_width_of_computes_parity
            rho bound bounded (fun input => by
              simpa [gateComputes] using represents input)

end Circuit
end AC0
end Algebraic
