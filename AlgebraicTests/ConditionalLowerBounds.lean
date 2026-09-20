import Algebraic.ConditionalComplexity.Linear
import Algebraic.ConditionalComplexity.Restriction
import Algebraic.Complexity.RelativeApproximation
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.PairingRelative

/-!
# Conditional lower-bound regressions

Exercise a basis with nonlinear gates, actual savings from a helper,
characteristic two, high-degree free preprocessing, exact source
initialization for approximation, and restrictions with weighted costs.
-/

namespace AlgebraicTests.ConditionalLowerBounds

open Algebraic
open Algebraic.ConditionalComplexity.Linear
open scoped Matrix

private def xorCircuit : Circuit (Arithmetic.signature (ZMod 2)) 2 1 1 where
  program := (Program.empty : Program (Arithmetic.signature (ZMod 2)) 2 0).gate
    ⟨.add, Wire.input⟩
  outputs := fun _ => Wire.gate 0

private theorem xorCircuit_eval (input : Fin 2 → ZMod 2) :
    xorCircuit.eval Arithmetic.nativeInterpretation input 0 = input 0 + input 1 := rfl

private theorem arithmetic_binary (op : Arithmetic.Op (ZMod 2)) :
    (Arithmetic.signature (ZMod 2)).Arity op ≤ 2 := by
  cases op <;> simp [Arithmetic.arity]

private def parity : Fin 3 → ZMod 2 := fun _ => 1

private def pairHelper : Fin 1 → Fin 3 → ZMod 2 := fun _ => ![1, 1, 0]

-- Multiplication is available as a nonlinear Boolean AND gate. It cannot
-- improve on the one XOR needed after receiving x_0 + x_1.
example : Circuit.conditionalGateComplexity Arithmetic.nativeInterpretation
    (fun input (_ : Fin 1) => parity ⬝ᵥ input) (forms pairHelper) = 1 := by
  rw [conditionalGateComplexity_eq_min_weight Arithmetic.nativeInterpretation
    arithmetic_binary xorCircuit xorCircuit_eval parity (by decide)]
  apply le_antisymm
  · exact iInf_le_of_le (fun _ => 1) (by decide)
  · have small : ∀ coefficients : Fin 1 → ZMod 2,
        1 ≤ weight coefficients + weight (parity + ∑ j, coefficients j • pairHelper j) - 1 := by
      decide
    exact le_iInf fun coefficients => by exact_mod_cast small coefficients

-- With no helpers the same target needs exactly two gates, including in
-- this basis with arbitrary field constants and multiplication.
example : Circuit.conditionalGateComplexity Arithmetic.nativeInterpretation
    (fun input (_ : Fin 1) => parity ⬝ᵥ input)
    (forms (fun i : Fin 0 => Fin.elim0 i)) = 2 := by
  rw [conditionalGateComplexity_eq_min_weight Arithmetic.nativeInterpretation
    arithmetic_binary xorCircuit xorCircuit_eval parity (by decide)]
  simp [weight, parity]

-- Supplying the entire nonzero target permits the zero-gate boundary case.
example : Circuit.conditionalGateComplexity Arithmetic.nativeInterpretation
    (fun input (_ : Fin 1) => parity ⬝ᵥ input) (forms (fun _ : Fin 1 => parity)) = 0 := by
  rw [conditionalGateComplexity_eq_min_weight Arithmetic.nativeInterpretation
    arithmetic_binary xorCircuit xorCircuit_eval parity (by decide)]
  apply le_antisymm _ zero_le
  exact iInf_le_of_le (fun _ => 1) (by decide)

-- High-degree and nonhomogeneous helpers are permitted, even in
-- characteristic two, where pointwise and formal polynomial equality differ.
example : Fusion.Arithmetic.Interaction.Hessian.Pairing.preprocessedMultiplicationComplexity
    (fun _ : Fin 1 =>
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (ZMod 2)) ^ 2 +
        MvPolynomial.X 1 ^ 7 + 1) = 2 :=
  Fusion.Arithmetic.Interaction.Hessian.Pairing.preprocessedMultiplicationComplexity_eq _

-- The empty pairing costs zero even with arbitrary helpers.
example {K : Type} [Field K] (given : Fin k → MvPolynomial (Fin 0) K) :
    Fusion.Arithmetic.Interaction.Hessian.Pairing.preprocessedMultiplicationComplexity given = 0 :=
  Fusion.Arithmetic.Interaction.Hessian.Pairing.preprocessedMultiplicationComplexity_eq given

private abbrev andSignature : Signature := ⟨Unit, fun _ => 2⟩

private def andInterpretation : Interpretation andSignature Bool :=
  fun _ input => input 0 && input 1

-- Approximate every gate by its first argument. On the four Boolean
-- samples, a local AND gate introduces at most one fresh error and the
-- target AND differs from each possible approximate output at one sample.
example : (1 : ℕ∞) ≤ Circuit.relativeCostComplexity andInterpretation
    OperationCost.unit (fun input (_ : Fin 1) => input 0 && input 1)
    (fun input : Fin 2 → Bool => input) := by
  apply Approximation.Scheme.relativeCostComplexity_lowerBound_of_localErrors
    andInterpretation (fun _ (input : Fin 2 → Fin 2) => input 0)
    (fun i (input : Fin 2 → Bool) => input i) (fun input => input) (fun i => i)
    OperationCost.unit (by intros; rfl)
  · decide
  · decide

-- Restrictions charge the whole source tuple jointly.
example (interpretation : Interpretation σ U) (cost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) (map : Target U d n)
    (hard : (11 : ℕ∞) ≤ Circuit.costComplexity interpretation cost (target ∘ map))
    (cheap : Circuit.costComplexity interpretation cost
      (fun input => Fin.append (map input) (given (map input))) ≤ 4) :
    (7 : ℕ∞) ≤ Circuit.conditionalCostComplexity interpretation cost target given :=
  Circuit.conditionalCostComplexity_lowerBound_of_precomp
    interpretation cost target given map 11 4 hard cheap

end AlgebraicTests.ConditionalLowerBounds
