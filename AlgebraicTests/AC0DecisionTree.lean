import Algebraic.LowerBound.AC0.DecisionTree

/-!
# AC0 decision-tree regression tests
-/

namespace AlgebraicTests.AC0DecisionTree

open Algebraic
open Algebraic.AC0

def xorTwo : ScalarFunction Bool 2 :=
  fun input => Bool.xor (input 0) (input 1)

def xorTwoTree : DecisionTree 2 :=
  .query 0
    (.query 1 (.leaf false) (.leaf true))
    (.query 1 (.leaf true) (.leaf false))

theorem xorTwoTree_computes : xorTwoTree.Computes xorTwo := by
  intro input
  cases first : input 0 <;>
    cases second : input 1 <;>
      simp [xorTwoTree, xorTwo, DecisionTree.eval, first, second]

example : xorTwoTree.depth = 2 := rfl

example :
    (xorTwoTree.restrict (PartialAssignment.fix 0 true)).depth = 1 := by
  decide

example
    (rho : PartialAssignment 2)
    (input : Fin 2 -> Bool) :
    (xorTwoTree.restrict rho).eval input =
      xorTwoTree.eval (rho.apply input) :=
  DecisionTree.eval_restrict xorTwoTree rho input

example : DecisionTree.DepthAtMost xorTwo 2 :=
  ⟨xorTwoTree, xorTwoTree_computes, by decide⟩

example (rho : PartialAssignment 2) :
    DecisionTree.DepthAtMost (xorTwo.restrict rho) 2 :=
  (show DecisionTree.DepthAtMost xorTwo 2 from
    ⟨xorTwoTree, xorTwoTree_computes, by decide⟩).restrict rho

example (function : ScalarFunction Bool 4) :
    DecisionTree.DepthAtMost function 4 :=
  DecisionTree.depthAtMost_inputCount function

end AlgebraicTests.AC0DecisionTree
