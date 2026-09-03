import Algebraic.Basis.DeMorgan
import Algebraic.MassProduction.DirectProduct

/-!
# Boolean scalar synthesis data

This module packages a concrete one-output De Morgan circuit for every
Boolean function at a fixed input width. Synthesis data is always passed
explicitly; neither the fixed-width package nor a width-indexed family is a
typeclass.
-/

namespace Algebraic
namespace MassProduction

/-- Explicit data for synthesizing every Boolean function at one fixed input
width. -/
structure ScalarSynthesis (width : Nat) where
  /-- Program-gate count selected for each scalar target. -/
  gateCount : ScalarFunction Bool width -> Nat
  /-- Concrete one-output circuit selected for each scalar target. -/
  circuit : (function : ScalarFunction Bool width) ->
    Circuit DeMorgan.signature width (gateCount function) 1
  /-- Proof that every selected circuit computes its requested target. -/
  computes : forall function,
    (circuit function).Computes DeMorgan.interpretation
      (scalarTarget function)

/-- Width-indexed one-copy synthesis data. -/
abbrev ScalarSynthesisFamily :=
  (width : Nat) -> ScalarSynthesis width

end MassProduction
end Algebraic
