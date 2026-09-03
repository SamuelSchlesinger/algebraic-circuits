import Algebraic.LowerBound.AC0.Switching.Family

/-!
# Finite-family AC0 switching regression tests
-/

namespace AlgebraicTests.AC0SwitchingFamily

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (formulas : Fin formulaCount -> DNF n)
    (bounded : forall index, (formulas index).WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => ∃ index, DecisionTree.DepthAtLeast
          ((formulas index).restrict rho).eval pathLength) ≤
      (formulaCount : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength) :=
  RandomRestriction.probability_exists_dnf_depthAtLeast_restrict_le_five
    formulas bounded pathLength p atMostOne

example
    (formulas : Fin formulaCount -> CNF n)
    (bounded : forall index, (formulas index).WidthAtMost widthBound)
    (depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => ∃ index, ¬DecisionTree.DepthAtMost
          ((formulas index).restrict rho).eval depthBound) ≤
      (formulaCount : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          (depthBound + 1)) :=
  RandomRestriction.probability_exists_cnf_not_depthAtMost_restrict_le_five
    formulas bounded depthBound p atMostOne

end AlgebraicTests.AC0SwitchingFamily
