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

example
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (left right : PartialAssignment 2 -> Prop)
    [DecidablePred left]
    [DecidablePred right]
    (included : forall rho, left rho -> right rho) :
    RandomRestriction.probability 2 p atMostOne left ≤
      RandomRestriction.probability 2 p atMostOne right :=
  RandomRestriction.probability_mono 2 p atMostOne included

example
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (left right : PartialAssignment 2 -> Prop)
    [DecidablePred left]
    [DecidablePred right] :
    RandomRestriction.probability 2 p atMostOne
        (fun rho => left rho ∨ right rho) ≤
      RandomRestriction.probability 2 p atMostOne left +
        RandomRestriction.probability 2 p atMostOne right :=
  RandomRestriction.probability_or_le 2 p atMostOne left right

example
    {indexType : Type*}
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (indices : Finset indexType)
    (events : indexType -> PartialAssignment 2 -> Prop)
    [(index : indexType) -> DecidablePred (events index)] :
    RandomRestriction.probability 2 p atMostOne
        (fun rho => ∃ index ∈ indices, events index rho) ≤
      ∑ index ∈ indices,
        RandomRestriction.probability 2 p atMostOne (events index) :=
  RandomRestriction.probability_exists_mem_le_sum
    2 p atMostOne indices events

end AlgebraicTests.AC0RandomRestriction
