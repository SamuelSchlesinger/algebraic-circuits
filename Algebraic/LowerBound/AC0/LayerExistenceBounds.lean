import Algebraic.LowerBound.AC0.LayerExistence
import Algebraic.LowerBound.AC0.LayerSwitchingBounds

/-!
# Existential AC0 layer advancement with separate bounds

This module combines two-parameter layer switching with exact live-variable
averaging. If the current invariant has source bound `s` and the next layer
should have target bound `t >= s`, define

`delta = andOrCost(program) * (5 * p * s)^(t + 1)`.

Whenever `delta * m + k < p * m`, where `m` is the current live count, there
exists a refinement that advances one layer at target bound `t` and leaves at
least `k` variables live. This is an existence theorem from a proved first
moment, not a search procedure.
-/

namespace Algebraic
namespace AC0
namespace Program

open scoped ENNReal

/-- Charged-size switching failure bound with distinct incoming normal-form
width and outgoing decision-tree depth. -/
noncomputable def layerFailureBoundOfBounds
    (program : Algebraic.Program signature n g)
    (p : NNReal)
    (sourceBound targetBound : Nat) : ENNReal :=
  (program.cost andOrCost : ENNReal) *
    (((5 : ENNReal) * (p : ENNReal) * (sourceBound : ENNReal)) ^
      (targetBound + 1))

/-- The two-parameter failure bound specializes to the original common-bound
definition. -/
theorem layerFailureBoundOfBounds_self
    (program : Algebraic.Program signature n g)
    (p : NNReal)
    (bound : Nat) :
    layerFailureBoundOfBounds program p bound bound =
      layerFailureBound program p bound :=
  rfl

/-- Sufficient first-moment room produces a refinement that advances from the
source bound to the target bound while retaining the requested live count. -/
theorem ShallowUpTo.exists_refine_succ_with_liveCount_bounds
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (normal : NegationsAtInputs program)
    (shallow : ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (retained : Nat)
    (room :
      layerFailureBoundOfBounds program p sourceBound targetBound *
            (rho.liveCount : ENNReal) +
          (retained : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal)) :
    ∃ extension : PartialAssignment n,
      ShallowUpTo program (rho.refine extension) (level + 1) targetBound ∧
        retained ≤ (rho.refine extension).liveCount := by
  classical
  obtain ⟨extension, succeeds, survivors⟩ :=
    RandomRestriction.exists_good_refinement_with_liveCount
      n p atMostOne rho
      (fun extension =>
        ¬ShallowUpTo program (rho.refine extension)
          (level + 1) targetBound)
      (layerFailureBoundOfBounds program p sourceBound targetBound) retained
      (by
        simpa [layerFailureBoundOfBounds] using
          shallow.probability_not_succ_refine_le_five_bounds
            normal sourceLeTarget p atMostOne)
      room
  exact ⟨extension, not_not.mp succeeds, survivors⟩

end Program
end AC0
end Algebraic
