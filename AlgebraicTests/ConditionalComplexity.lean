import Algebraic.ConditionalComplexity.Counterexample
import Algebraic.ConditionalComplexity.Counting

/-!
# Conditional complexity regressions

Exercise free supplied values over an empty basis, zero-width boundaries,
and a circuit that combines an original coordinate with a supplied value.
-/

namespace AlgebraicTests.ConditionalComplexity

open Algebraic

private abbrev emptySignature : Signature where
  Op := Empty
  Arity := Empty.elim

private def emptyInterpretation : Interpretation emptySignature Bool := fun op => nomatch op

-- Supplied values do not need an implementation over the chosen basis.
example (f : Target Bool n m) :
    Circuit.conditionalGateComplexity emptyInterpretation f f = 0 := by
  simp

-- Both zero inputs and zero outputs are supported.
example :
    Circuit.conditionalGateComplexity emptyInterpretation
      (fun _ : Fin 0 → Bool => Fin.elim0) (fun _ => Fin.elim0) = 0 := by
  exact Circuit.conditionalGateComplexity_self _ (fun _ : Fin 0 → Bool => Fin.elim0)

private def combineOriginalAndGiven :
    Circuit Cslib.Circuits.Boolean.signature (2 + 1) 1 1 where
  program := .gate .empty
    ⟨.and, fun i => Wire.input (if i.val = 0 then 0 else 2)⟩
  outputs := fun _ => Wire.gate 0

-- Advice values and original inputs coexist, and only the combining gate is charged.
example (given : Target Bool 2 1) :
    Circuit.conditionalGateComplexity Cslib.Circuits.Boolean.interpretation
      (fun input (_ : Fin 1) => input 0 && given input 0) given ≤ 1 := by
  apply Circuit.conditionalGateComplexity_le (circuit := combineOriginalAndGiven)
  intro input
  funext output
  rfl

-- The public counterexample exposes exact values, not just an upper-bound comparison.
example :
    Circuit.gateComplexity Cslib.Circuits.Boolean.interpretation
      Algebraic.ConditionalComplexity.nandTarget = 2 ∧
    Circuit.conditionalGateComplexity Cslib.Circuits.Boolean.interpretation
      Algebraic.ConditionalComplexity.andTarget Algebraic.ConditionalComplexity.nandTarget = 1 :=
  ⟨Algebraic.ConditionalComplexity.gateComplexity_nand,
    Algebraic.ConditionalComplexity.conditionalGateComplexity_and_given_nand⟩

end AlgebraicTests.ConditionalComplexity
