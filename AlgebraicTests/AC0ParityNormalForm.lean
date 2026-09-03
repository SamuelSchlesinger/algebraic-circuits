import Algebraic.LowerBound.AC0.ParityNormalForm

/-!
# Restricted-parity normal-form regression tests
-/

namespace AlgebraicTests.AC0ParityNormalForm

open Algebraic
open Algebraic.AC0

example
    (formula : DNF n)
    (rho : PartialAssignment n)
    (bound : Nat)
    (bounded : formula.WidthAtMost bound)
    (computes : ∀ input,
      formula.eval input = (Parity.function n).restrict rho input) :
    rho.liveCount ≤ bound :=
  formula.liveCount_le_width_of_computes_parity
    rho bound bounded computes

example
    (formula : CNF n)
    (rho : PartialAssignment n)
    (bound : Nat)
    (bounded : formula.WidthAtMost bound)
    (computes : ∀ input,
      formula.eval input = (Parity.function n).restrict rho input) :
    rho.liveCount ≤ bound :=
  formula.liveCount_le_width_of_computes_parity
    rho bound bounded computes

end AlgebraicTests.AC0ParityNormalForm
