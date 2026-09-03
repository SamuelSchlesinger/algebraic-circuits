import Algebraic.LowerBound.AC0.LayerSwitchingBounds

/-!
# Two-parameter AC0 layer switching regression tests
-/

namespace AlgebraicTests.AC0LayerSwitchingBounds

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rho extension : PartialAssignment n)
    (level sourceBound targetBound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (next : ∀ gate,
      gate ∈ AC0.Program.connectiveGates program →
      AC0.Program.logicalGateDepths program gate ≤ level + 1 →
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) targetBound) :
    AC0.Program.ShallowUpTo program (rho.refine extension)
      (level + 1) targetBound :=
  shallow.succ_of_connective_bounds normal sourceLeTarget next

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rho : PartialAssignment n)
    (level sourceBound targetBound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬AC0.Program.ShallowUpTo program (rho.refine extension)
            (level + 1) targetBound) ≤
      (program.cost AC0.andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (sourceBound : ENNReal)) ^
          (targetBound + 1)) :=
  shallow.probability_not_succ_refine_le_five_bounds
    normal sourceLeTarget p atMostOne

end AlgebraicTests.AC0LayerSwitchingBounds
