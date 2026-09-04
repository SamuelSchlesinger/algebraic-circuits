import Algebraic.LowerBound.AC0.LayerIterationBounds

/-!
# Variable-parameter AC0 depth-reduction regression tests
-/

namespace AlgebraicTests.AC0LayerIterationBounds

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (program : Program signature n g)
    (rounds : Nat)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      AC0.Program.layerFailureBoundOfBounds program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      AC0.Program.layerFailureBoundOfBounds program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal)) :
    ∃ rho : PartialAssignment n,
      AC0.Program.ShallowUpTo program rho rounds (treeBound rounds) ∧
        retained rounds ≤ rho.liveCount :=
  AC0.Program.exists_shallowUpTo_with_liveCount_bounds_raw
    program rounds treeBound oneLeInitialBound p atMostOne
    boundMonotone retained initial failureLe room

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rounds : Nat)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      AC0.Program.layerFailureBoundOfBounds program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      AC0.Program.layerFailureBoundOfBounds program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal)) :
    ∃ rho : PartialAssignment n,
      AC0.Program.ShallowUpTo program rho rounds (treeBound rounds) ∧
        retained rounds ≤ rho.liveCount :=
  AC0.Program.exists_shallowUpTo_with_liveCount_bounds
    program normal rounds treeBound oneLeInitialBound p atMostOne
    boundMonotone retained initial failureLe room

end AlgebraicTests.AC0LayerIterationBounds
