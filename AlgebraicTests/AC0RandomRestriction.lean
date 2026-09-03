import Algebraic.LowerBound.AC0.RandomRestriction

/-!
# Random-restriction distribution regression tests
-/

namespace AlgebraicTests.AC0RandomRestriction

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    ∑ state : Option Bool,
        (RandomRestriction.coordinateWeight p state : ENNReal) = 1 :=
  RandomRestriction.sum_coordinateWeight p atMostOne

example
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.distribution 1 p atMostOne
        (PartialAssignment.empty : PartialAssignment 1) = p := by
  rw [RandomRestriction.distribution_apply_eq_live_fixed]
  simp

example
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.distribution 1 p atMostOne
        (PartialAssignment.fix 0 false) =
      RandomRestriction.fixedWeight p := by
  rw [RandomRestriction.distribution_apply]
  simp [RandomRestriction.weight, RandomRestriction.coordinateWeight,
    PartialAssignment.fix]

example
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability 2 p atMostOne (fun _ => True) = 1 := by
  simp

end AlgebraicTests.AC0RandomRestriction
