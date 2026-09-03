import Algebraic.LowerBound.AC0.LayerIteration

/-!
# Iterated semantic AC0 depth-reduction regression tests
-/

namespace AlgebraicTests.AC0LayerIteration

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    {delta p : ENNReal}
    {minimum current next : Nat}
    (deltaFinite : delta ≠ ∞)
    (deltaLe : delta <= p)
    (minimumLe : minimum <= current)
    (room :
      delta * (minimum : ENNReal) + (next : ENNReal) <
        p * (minimum : ENNReal)) :
    delta * (current : ENNReal) + (next : ENNReal) <
      p * (current : ENNReal) :=
  AC0.Program.layerRoom_mono deltaFinite deltaLe minimumLe room

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (depth bound : Nat)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      AC0.Program.layerFailureBound program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        AC0.Program.layerFailureBound program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal)) :
    exists rho : PartialAssignment n,
      AC0.Program.ShallowUpTo program rho depth bound /\
        retained depth <= rho.liveCount :=
  AC0.Program.exists_shallowUpTo_with_liveCount
    program normal depth bound oneLeBound p atMostOne retained
    initial failureLe room

end AlgebraicTests.AC0LayerIteration
