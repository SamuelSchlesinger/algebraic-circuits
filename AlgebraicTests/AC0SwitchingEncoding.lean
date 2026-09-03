import Algebraic.LowerBound.AC0.Switching.Encoding

/-!
# AC0 switching-encoding regression tests
-/

namespace AlgebraicTests.AC0SwitchingEncoding

open Algebraic
open Algebraic.AC0
open Algebraic.AC0.RandomRestriction

def identityEncoding
    (rho : PartialAssignment n) : PartialAssignment n × PUnit :=
  (rho, PUnit.unit)

example
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ 0 *
        probability n p atMostOne (fun _ => True) ≤
      (Fintype.card PUnit : ENNReal) * (p : ENNReal) ^ 0 := by
  apply probability_scaled_le_of_refinement_encoding n p atMostOne
    (fun _ => True) PUnit 0 (fun _ => PartialAssignment.empty)
    identityEncoding
  · intro left _ right _ equal
    exact congrArg Prod.fst equal
  · intro rho _
    simp [identityEncoding]
  · intro rho _
    simp
  · intro rho _
    simp

end AlgebraicTests.AC0SwitchingEncoding
