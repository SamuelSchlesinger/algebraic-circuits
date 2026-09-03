import Algebraic.LowerBound.AC0.BottomFamily

/-!
# AC0 bottom-family switching regression tests
-/

namespace AlgebraicTests.AC0BottomFamily

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (program : Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) :
    (AC0.Program.paddedAndBottomFormula program widthBound
      gate).WidthAtMost widthBound :=
  AC0.Program.paddedAndBottomFormula_widthAtMost
    program widthBound gate

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (widthBound : Nat)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : AC0.Program.logicalGateDepths program gate = 1)
    (bounded : fanIn ≤ widthBound)
    (rho : PartialAssignment n) :
    ((AC0.Program.paddedOrBottomFormula program widthBound gate).restrict
      rho).eval =
      ScalarFunction.restrict
        (program.gateFunction interpretation gate) rho :=
  AC0.Program.paddedOrBottomFormula_restrict_eval_of_bottom
    program normal widthBound gate operation depthOne bounded rho

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (widthBound pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => Exists fun gate : Fin g =>
          AC0.Program.IsBoundedBottomAnd program widthBound gate ∧
            DecisionTree.DepthAtLeast
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate) rho)
              pathLength) ≤
      (g : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength) :=
  AC0.Program.probability_exists_boundedBottomAnd_depthAtLeast_restrict_le_five
    program normal widthBound pathLength p atMostOne

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (widthBound depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => Exists fun gate : Fin g =>
          AC0.Program.IsBoundedBottomOr program widthBound gate ∧
            ¬DecisionTree.DepthAtMost
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate) rho)
              depthBound) ≤
      (g : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          (depthBound + 1)) :=
  AC0.Program.probability_exists_boundedBottomOr_not_depthAtMost_restrict_le_five
    program normal widthBound depthBound p atMostOne

end AlgebraicTests.AC0BottomFamily
