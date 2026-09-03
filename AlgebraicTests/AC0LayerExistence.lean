import Algebraic.LowerBound.AC0.LayerExistence

/-!
# Existential AC0 layer advancement regression tests
-/

namespace AlgebraicTests.AC0LayerExistence

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (program : Program signature n g)
    (rho : PartialAssignment n)
    (level smaller larger : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level smaller)
    (le : smaller <= larger) :
    AC0.Program.ShallowUpTo program rho level larger :=
  shallow.mono le

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat)
    (room :
      AC0.Program.layerFailureBound program p bound *
            (rho.liveCount : ENNReal) +
          (retained : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal)) :
    exists extension : PartialAssignment n,
      AC0.Program.ShallowUpTo program (rho.refine extension)
          (level + 1) bound /\
        retained <= (rho.refine extension).liveCount :=
  shallow.exists_refine_succ_with_liveCount
    normal p atMostOne retained room

end AlgebraicTests.AC0LayerExistence
