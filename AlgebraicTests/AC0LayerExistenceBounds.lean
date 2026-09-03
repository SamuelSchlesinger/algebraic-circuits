import Algebraic.LowerBound.AC0.LayerExistenceBounds

/-!
# Two-parameter existential AC0 layer advancement regression tests
-/

namespace AlgebraicTests.AC0LayerExistenceBounds

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (program : Program signature n g)
    (p : NNReal)
    (bound : Nat) :
    AC0.Program.layerFailureBoundOfBounds program p bound bound =
      AC0.Program.layerFailureBound program p bound :=
  AC0.Program.layerFailureBoundOfBounds_self program p bound

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rho : PartialAssignment n)
    (level sourceBound targetBound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (retained : Nat)
    (room :
      AC0.Program.layerFailureBoundOfBounds
            program p sourceBound targetBound *
            (rho.liveCount : ENNReal) +
          (retained : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal)) :
    ∃ extension : PartialAssignment n,
      AC0.Program.ShallowUpTo program (rho.refine extension)
          (level + 1) targetBound ∧
        retained ≤ (rho.refine extension).liveCount :=
  shallow.exists_refine_succ_with_liveCount_bounds
    normal sourceLeTarget p atMostOne retained room

end AlgebraicTests.AC0LayerExistenceBounds
