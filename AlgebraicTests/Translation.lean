import Algebraic.Applications
import Algebraic.Translation
import AlgebraicTests.Circuit

/-!
# Translation and compilation API regressions

These tests apply the public translation laws to a concrete shared circuit and
exercise the reusable binary-power compiler at its zero, one, and recursive
cases.
-/

namespace AlgebraicTests.Translation

open Algebraic

example (input : Fin 3 → Bool) :
    ((Algebraic.Translation.id DeMorgan.signature).compile
        Circuit.sharedCircuit).eval DeMorgan.interpretation input =
      Circuit.sharedCircuit.eval DeMorgan.interpretation input :=
  Algebraic.Translation.compile_id_eval Circuit.sharedCircuit
    DeMorgan.interpretation input

example :
    ((Algebraic.Translation.id DeMorgan.signature).compile
        Circuit.sharedCircuit).cost DeMorgan.binaryCost =
      Circuit.sharedCircuit.cost DeMorgan.binaryCost :=
  Algebraic.Translation.compile_id_cost Circuit.sharedCircuit
    DeMorgan.binaryCost

example {K R : Type} [One K] [Semiring R]
    (constant : K → R)
    (mapsOne : constant 1 = 1)
    (input : Fin 1 → R)
    (exponent : Nat) :
    (Arithmetic.Power.binaryCircuit (K := K) exponent).2.eval
        (Arithmetic.interpretation constant) input 0 = input 0 ^ exponent :=
  Arithmetic.Power.binaryCircuit_eval constant mapsOne input exponent

example {K R : Type} [One K] [Semiring R]
    (constant : K → R)
    (mapsOne : constant 1 = 1)
    (input : Fin 1 → R) :
    (Applications.binaryPowerCircuit (K := K) 13).eval
        (Arithmetic.interpretation constant) input 0 = input 0 ^ 13 :=
  Applications.binaryPowerCircuit_eval constant mapsOne input 13

example :
    (Arithmetic.Power.binaryCircuit (K := Nat) 0).2.cost
        (Arithmetic.multiplicationCost (K := Nat)) = 0 := by
  simp

example :
    (Arithmetic.Power.binaryCircuit (K := Nat) 1).2.cost
        (Arithmetic.multiplicationCost (K := Nat)) = 0 := by
  simp

example :
    (Arithmetic.Power.binaryCircuit (K := Nat) 13).2.cost
        (Arithmetic.multiplicationCost (K := Nat)) ≤
      2 * Nat.log2 13 := by
  rw [Arithmetic.Power.binaryCircuit_multiplicationCost]
  exact Arithmetic.Power.binaryMultiplicationCount_le_two_mul_log2 13
    (by decide)

example :
    (Applications.binaryPowerCircuit (K := Nat) 13).cost
        (Arithmetic.multiplicationCost (K := Nat)) =
      Arithmetic.Power.binaryMultiplicationCount 13 := by
  exact Applications.binaryPowerCircuit_multiplicationCost 13

end AlgebraicTests.Translation
