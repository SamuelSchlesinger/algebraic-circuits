import Algebraic.CircuitFamily.Growth

/-!
# Circuit-family growth regression tests
-/

namespace AlgebraicTests.CircuitFamilyGrowth

open Filter
open Algebraic

example (constant degree : Nat) :
    ∀ᶠ n in atTop, constant * n ^ degree <= 2 ^ n :=
  Circuit.Resource.eventually_const_mul_pow_le_two_pow constant degree

end AlgebraicTests.CircuitFamilyGrowth
