import Algebraic.LowerBound.AC0.LayerSchedule
import Algebraic.LowerBound.AC0.ParityDepthReduction
import Algebraic.LowerBound.AC0.ParitySurvivors

/-!
# A concrete finite AC0 lower bound for parity

This module instantiates the complete structural argument with the explicit
probability and integer-survivor schedules. For a depth-`d` circuit and target
tree depth `t`, the two source-facing numerical conditions are

`S * (1/2)^(t+1) < 1/(20t)`

and

`t < n / (20 * (20t)^(d-2))`.

Here `S` is the number of AND/OR gates. Under checked input-negation normal
form these inequalities rule out exact computation of parity. The result is
uniform in every parameter and follows from symbolic inequalities; it is not
a fixed-size experiment or a finite circuit search.
-/

namespace Algebraic
namespace AC0

namespace ParityParameters

/-- Every scheduled tree allowance is at most the common target depth. -/
theorem treeBound_le_target
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    treeBound t level ≤ t := by
  cases level with
  | zero => simpa [treeBound] using oneLe
  | succ level => simp [treeBound]

end ParityParameters

namespace Circuit

open scoped ENNReal

/-- Concrete `rounds`-step parity contradiction using the canonical
probabilities, tree bounds, and floor-divided survivor targets. -/
theorem not_computes_parity_of_concrete_parameters
    (circuit : Algebraic.Circuit signature n g 1)
    (normal : Program.NegationsAtInputs circuit.program)
    (rounds : Nat)
    (circuitDepth : logicalDepth circuit ≤ rounds + 1)
    (t : Nat)
    (oneLe : 1 ≤ t)
    (small : ParityParameters.switchingFailure circuit.program t <
      (ParityParameters.minimumRatio t : ENNReal))
    (tooMany : t < ParityParameters.retained n t rounds) :
    ¬circuit.Computes interpretation (Parity.target n) := by
  have finalPositive : 0 < ParityParameters.retained n t rounds := by
    omega
  apply not_computes_parity_of_iterated_switching_below_top
    circuit normal rounds circuitDepth
    (ParityParameters.treeBound t) (by simp)
    (ParityParameters.probability t)
    (fun level _ => ParityParameters.probability_le_one t oneLe level)
    (fun level _ => ParityParameters.treeBound_mono t oneLe level)
    (ParityParameters.retained n t) (by simp)
  · intro level before
    exact Program.failureLe_of_slack
      (ParityParameters.layer_slack circuit.program t oneLe level small)
  · intro level before
    exact Program.layerRoom_of_slack
      (ParityParameters.retained_positive_of_final n t before.le
        finalPositive)
      (ParityParameters.layer_slack circuit.program t oneLe level small)
      (ParityParameters.retained_shrinks n t level)
  · exact (ParityParameters.treeBound_le_target
      t oneLe rounds).trans_lt tooMany

/-- Depth-facing concrete parity lower bound. A depth-`d` circuit uses exactly
`d-1` restriction rounds, leaving the top gate for the normal-form
obstruction. -/
theorem not_computes_parity_of_concrete_depth_reduction
    (circuit : Algebraic.Circuit signature n g 1)
    (normal : Program.NegationsAtInputs circuit.program)
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (small : ParityParameters.switchingFailure circuit.program t <
      (ParityParameters.minimumRatio t : ENNReal))
    (survivors :
      t < n / (20 * (20 * t) ^ (depth - 2))) :
    ¬circuit.Computes interpretation (Parity.target n) := by
  apply not_computes_parity_of_concrete_parameters
    circuit normal (depth - 1) (by omega) t oneLe small
  have roundsEq : depth - 1 = (depth - 2) + 1 := by omega
  rw [roundsEq, ParityParameters.retained_closed]
  exact survivors

end Circuit
end AC0
end Algebraic
