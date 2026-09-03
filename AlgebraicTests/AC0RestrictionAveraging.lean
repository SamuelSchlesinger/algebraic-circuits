import Algebraic.LowerBound.AC0.RestrictionAveraging

/-!
# Random-restriction live-variable averaging regression tests
-/

namespace AlgebraicTests.AC0RestrictionAveraging

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (p : NNReal)
    (atMostOne : p <= 1)
    (selected : Fin n) :
    RandomRestriction.probability n p atMostOne
        (fun rho => rho selected = none) = (p : ENNReal) :=
  RandomRestriction.probability_coordinate_live n p atMostOne selected

example
    (p : NNReal)
    (atMostOne : p <= 1) :
    RandomRestriction.expectedLiveCountAfter n p atMostOne
        PartialAssignment.empty =
      (p : ENNReal) * (n : ENNReal) := by
  simpa using RandomRestriction.expectedLiveCountAfter_eq
    n p atMostOne (PartialAssignment.empty : PartialAssignment n)

example
    (p : NNReal)
    (atMostOne : p <= 1)
    (rho : PartialAssignment n)
    (bad : PartialAssignment n -> Prop)
    [DecidablePred bad]
    (failureBound : ENNReal)
    (retained : Nat)
    (failure : RandomRestriction.probability n p atMostOne bad <=
      failureBound)
    (room :
      failureBound * (rho.liveCount : ENNReal) +
          (retained : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal)) :
    exists extension : PartialAssignment n,
      Not (bad extension) /\
        retained <= (rho.refine extension).liveCount :=
  RandomRestriction.exists_good_refinement_with_liveCount
    n p atMostOne rho bad failureBound retained failure room

end AlgebraicTests.AC0RestrictionAveraging
