import Algebraic.Core

/-!
# Core facade regressions

This module intentionally imports only `Algebraic.Core` and exercises the
zero-gate identity circuit through its public API.
-/

namespace AlgebraicTests.Core

open Algebraic

example (signature : Signature) (inputCount : Nat) :
    (Circuit.id signature inputCount).size = 0 := rfl

example (interpretation : Interpretation signature U)
    (input : Fin inputCount → U) :
    (Circuit.id signature inputCount).eval interpretation input = input := by
  simp

end AlgebraicTests.Core
