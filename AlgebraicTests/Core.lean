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

namespace AlgebraicTests.CslibInterop

open Algebraic

-- Public types are CSLib's types, with no conversion or copying.
example : Algebraic.Signature = Cslib.Circuits.Signature := rfl

example (signature : Cslib.Circuits.Signature) (n g m : Nat) :
    Algebraic.Circuit signature n g m = Cslib.Circuits.Circuit signature n g m := rfl

-- Native CSLib circuits use the local semantics, costs, and composition API.
example (circuit : Cslib.Circuits.Circuit signature n g m) :
    circuit.cost OperationCost.unit = g := circuit.cost_unit

example (circuit : Cslib.Circuits.Circuit signature n g m)
    (interpretation : Cslib.Circuits.Interpretation signature U) :
    circuit.Computes interpretation (circuit.eval interpretation) := fun _ => rfl

example (circuit : Cslib.Circuits.Circuit signature n g m)
    (interpretation : Cslib.Circuits.Interpretation signature U)
    (input : Fin n → U) :
    (circuit.comp (Cslib.Circuits.Circuit.id signature n)).eval interpretation input =
      circuit.eval interpretation input := by
  simp

end AlgebraicTests.CslibInterop
