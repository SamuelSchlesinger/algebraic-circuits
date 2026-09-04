import Algebraic.LowerBound.AC0.ParitySeparation

/-!
# Qualitative AC0 parity separation regression tests
-/

namespace AlgebraicTests.AC0ParitySeparation

open Algebraic

example : Not (AC0.Computable AC0.Parity.targetFamily) :=
  AC0.parity_not_computable

example
    (family : Circuit.Family AC0.signature 1)
    (polynomialCost : family.HasPolynomialCost AC0.andOrCost)
    (constantDepth : AC0.Family.HasConstantLogicalDepth family)
    (negationsAtInputs : forall n,
      AC0.Program.NegationsAtInputs (family.circuit n).program) :
    Not (family.Computes AC0.interpretation AC0.Parity.targetFamily) :=
  AC0.Family.not_computes_parity
    family polynomialCost constantDepth negationsAtInputs

end AlgebraicTests.AC0ParitySeparation
