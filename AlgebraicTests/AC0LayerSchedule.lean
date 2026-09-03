import Algebraic.LowerBound.AC0.LayerSchedule

/-!
# AC0 ratio-schedule regression tests
-/

namespace AlgebraicTests.AC0LayerSchedule

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    {delta q p : ENNReal}
    {current next : Nat}
    (currentPositive : 0 < current)
    (slack : delta + q < p)
    (nextLe : (next : ENNReal) ≤ q * (current : ENNReal)) :
    delta * (current : ENNReal) + (next : ENNReal) <
      p * (current : ENNReal) :=
  AC0.Program.layerRoom_of_slack currentPositive slack nextLe

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
    (retainedPositive : ∀ level, level < rounds → 0 < retained level)
    (q : Nat → ENNReal)
    (slack : ∀ level, level < rounds →
      AC0.Program.layerFailureBoundOfBounds program (p level)
            (treeBound level) (treeBound (level + 1)) + q level <
        (p level : ENNReal))
    (shrinks : ∀ level, level < rounds →
      (retained (level + 1) : ENNReal) ≤
        q level * (retained level : ENNReal)) :
    ∃ rho : PartialAssignment n,
      AC0.Program.ShallowUpTo program rho rounds (treeBound rounds) ∧
        retained rounds ≤ rho.liveCount :=
  AC0.Program.exists_shallowUpTo_with_liveCount_of_slack
    program normal rounds treeBound oneLeInitialBound p atMostOne
    boundMonotone retained initial retainedPositive q slack shrinks

end AlgebraicTests.AC0LayerSchedule
