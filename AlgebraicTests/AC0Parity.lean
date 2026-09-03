import Algebraic.LowerBound.AC0.Parity

/-!
# AC0 parity-resilience regression tests
-/

namespace AlgebraicTests.AC0Parity

open Algebraic
open Algebraic.AC0

example
    (rho : PartialAssignment n)
    (selected : Fin n)
    (live : selected ∈ rho.liveVariables)
    (input : Fin n -> Bool) :
    (Parity.function n).restrict rho (Parity.flip input selected) ≠
      (Parity.function n).restrict rho input :=
  Parity.restrict_ne_flip_of_live rho selected live input

example
    (rho : PartialAssignment n) :
    DecisionTree.DepthAtLeast
      ((Parity.function n).restrict rho) rho.liveCount :=
  Parity.depthAtLeast_liveCount rho

example
    (rho : PartialAssignment n)
    (bound : Nat) :
    DecisionTree.DepthAtMost ((Parity.function n).restrict rho) bound ↔
      rho.liveCount <= bound :=
  Parity.depthAtMost_iff_liveCount_le rho bound

end AlgebraicTests.AC0Parity
