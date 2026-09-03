import Algebraic.LowerBound.AC0.Switching

/-!
# Semantic AC0 switching-lemma regression tests
-/

namespace AlgebraicTests.AC0Switching

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => DecisionTree.DepthAtLeast
          (formula.restrict rho).eval pathLength) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength :=
  RandomRestriction.probability_depthAtLeast_restrict_le_five
    formula bounded pathLength p atMostOne

example
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => ¬DecisionTree.DepthAtMost
          (formula.restrict rho).eval depthBound) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        (depthBound + 1) :=
  RandomRestriction.probability_not_depthAtMost_restrict_le_five
    formula bounded depthBound p atMostOne

example
    (formula : CNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => DecisionTree.DepthAtLeast
          (formula.restrict rho).eval pathLength) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength :=
  RandomRestriction.probability_cnf_depthAtLeast_restrict_le_five
    formula bounded pathLength p atMostOne

example
    (formula : CNF n)
    (bounded : formula.WidthAtMost widthBound)
    (depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => ¬DecisionTree.DepthAtMost
          (formula.restrict rho).eval depthBound) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        (depthBound + 1) :=
  RandomRestriction.probability_cnf_not_depthAtMost_restrict_le_five
    formula bounded depthBound p atMostOne

end AlgebraicTests.AC0Switching
