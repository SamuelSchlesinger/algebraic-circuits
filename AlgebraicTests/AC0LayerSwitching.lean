import Algebraic.LowerBound.AC0.LayerSwitching

/-!
# One-step AC0 layer switching regression tests
-/

namespace AlgebraicTests.AC0LayerSwitching

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (formula : DNF n)
    (function : ScalarFunction Bool n)
    (rho extension : PartialAssignment n)
    (computes : forall input,
      formula.eval input = function.restrict rho input) :
    (formula.restrict extension).eval =
      function.restrict (rho.refine extension) :=
  formula.restrict_eval_eq_refine_of_eval_eq
    function rho extension computes

example
    (program : Program signature n g)
    (rho extension : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (next : forall gate,
      gate ∈ AC0.Program.connectiveGates program ->
      AC0.Program.logicalGateDepths program gate <= level + 1 ->
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) bound) :
    AC0.Program.ShallowUpTo program (rho.refine extension)
      (level + 1) bound :=
  shallow.succ_of_connective_raw next

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (gate : Fin g)
    (operation : (program.lines gate).op = .not) :
    AC0.Program.logicalGateDepths program gate = 0 :=
  AC0.Program.logicalGateDepth_eq_zero_of_op_eq_not
    program normal gate operation

example
    (program : Program signature n g)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p <= 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬AC0.Program.ShallowUpTo program (rho.refine extension)
            (level + 1) bound) <=
      (program.cost AC0.andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
          (bound + 1)) :=
  shallow.probability_not_succ_refine_le_five_raw p atMostOne

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rho extension : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (next : forall gate,
      gate ∈ AC0.Program.connectiveGates program ->
      AC0.Program.logicalGateDepths program gate <= level + 1 ->
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) bound) :
    AC0.Program.ShallowUpTo program (rho.refine extension)
      (level + 1) bound :=
  shallow.succ_of_connective normal next

example
    (program : Program signature n g)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (gate : Fin g)
    (connective : gate ∈ AC0.Program.connectiveGates program)
    (gateDepth :
      AC0.Program.logicalGateDepths program gate <= level + 1)
    (p : NNReal)
    (atMostOne : p <= 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬DecisionTree.DepthAtMost
            (ScalarFunction.restrict
              (program.gateFunction interpretation gate)
              (rho.refine extension)) bound) <=
      (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
        (bound + 1)) :=
  shallow.probability_gate_not_depthAtMost_refine_le_five
    gate connective gateDepth p atMostOne

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p <= 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬AC0.Program.ShallowUpTo program (rho.refine extension)
            (level + 1) bound) <=
      (program.cost AC0.andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
          (bound + 1)) :=
  shallow.probability_not_succ_refine_le_five normal p atMostOne

end AlgebraicTests.AC0LayerSwitching
