import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear
import Algebraic.LowerBound.Fusion.Arithmetic.Combined
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Selected-coefficient Fusion for polynomial circuits

Project a polynomial onto any finite family of selected monomial
coefficients.  If the selected monomials are distinct and none is a constant
or one of the free input variables, their coefficient vectors form a standard
basis.  Computing all of them therefore needs one multiplication per output,
even with arbitrary field constants, subtraction, and cancellation.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial

noncomputable section

variable {K : Type u} {C : Type v} {σ : Type w} {I : Type x}

/-- Simultaneously extract the coefficients of a selected exponent family. -/
def coefficientFeature
    [CommSemiring K]
    (exponent : I → σ →₀ ℕ) :
    MvPolynomial σ K →ₗ[K] (I → K) :=
  LinearMap.pi fun output => MvPolynomial.lcoeff K (exponent output)

@[simp] theorem coefficientFeature_apply
    [CommSemiring K]
    (exponent : I → σ →₀ ℕ)
    (polynomial : MvPolynomial σ K)
    (output : I) :
    coefficientFeature exponent polynomial output =
      MvPolynomial.coeff (exponent output) polynomial :=
  rfl

/-- Selected nonconstant coefficients vanish on scalar polynomials. -/
theorem coefficientFeature_C_eq_zero
    [CommSemiring K]
    [DecidableEq σ]
    (exponent : I → σ →₀ ℕ)
    (nonconstant : ∀ output, exponent output ≠ 0)
    (scalar : K) :
    coefficientFeature exponent (MvPolynomial.C scalar) = (0 : I → K) := by
  funext output
  simp [coefficientFeature, MvPolynomial.coeff_C,
    (nonconstant output).symm]

/-- Selected coefficients vanish on a variable when no selected exponent is
that variable's degree-one exponent. -/
theorem coefficientFeature_X_eq_zero
    [CommSemiring K]
    [DecidableEq σ]
    (exponent : I → σ →₀ ℕ)
    (coordinate : σ)
    (notSelected : ∀ output,
      exponent output ≠ Finsupp.single coordinate 1) :
    coefficientFeature exponent (MvPolynomial.X coordinate) =
      (0 : I → K) := by
  funext output
  simp [coefficientFeature, MvPolynomial.coeff_X,
    (notSelected output).symm]

/-- A selected monomial maps to the corresponding standard basis vector. -/
theorem coefficientFeature_monomial_eq_single
    [CommSemiring K]
    [DecidableEq σ]
    [DecidableEq I]
    (exponent : I → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (output : I) :
    coefficientFeature exponent
        (MvPolynomial.monomial (exponent output) (1 : K)) =
      Pi.single output (1 : K) := by
  funext candidate
  by_cases equal : output = candidate
  · subst candidate
    simp [coefficientFeature]
  · have exponentNe : exponent output ≠ exponent candidate :=
      fun exponentEqual => equal (injective exponentEqual)
    simp [coefficientFeature, MvPolynomial.coeff_monomial, equal, exponentNe]

/-- Requested monomials for a selected exponent family. -/
def targets
    [CommSemiring K]
    (exponent : Fin m → σ →₀ ℕ) :
    Fin m → MvPolynomial σ K :=
  fun output => MvPolynomial.monomial (exponent output) 1

/-- The selected-coefficient features of distinct requested monomials are
linearly independent. -/
theorem targetFeatures_linearIndependent
    [Field K]
    [DecidableEq σ]
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent) :
    LinearIndependent K
      (coefficientFeature (K := K) exponent ∘ targets (K := K) exponent) := by
  have standard := Pi.linearIndependent_single_one (Fin m) K
  simpa [Function.comp_def, targets,
    coefficientFeature_monomial_eq_single (K := K) exponent injective]
      using standard

/-- Polynomial problem whose free inputs are the designated variables.  Its
dummy target is unused by the multi-output theorem. -/
abbrev inputProblem
    [CommSemiring K]
    (inputVariables : Fin n → σ) : Problem (MvPolynomial σ K) where
  inputCount := n
  inputs := fun input => MvPolynomial.X (inputVariables input)
  target := 0

/-- Computing `m` distinct selected monomials, none constant or already a free
input, requires at least `m` multiplication gates. -/
theorem circuit_multiplication_lowerBound
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ output, exponent output ≠ 0)
    (notInput : ∀ output input,
      exponent output ≠ Finsupp.single (inputVariables input) 1)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (targets exponent) circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Linear.circuit_multiplication_lowerBound_of_linearIndependent
    (fun scalar => MvPolynomial.C (constant scalar))
    (inputProblem inputVariables) (coefficientFeature exponent)
  · intro input
    exact coefficientFeature_X_eq_zero exponent (inputVariables input)
      (fun output => notInput output input)
  · intro scalar
    exact coefficientFeature_C_eq_zero exponent nonconstant (constant scalar)
  · exact targetFeatures_linearIndependent exponent injective
  · exact constructs

/-- Total nonconstant arithmetic-gate cost is at least the number of selected
monomial outputs. -/
theorem circuit_gate_lowerBound
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ output, exponent output ≠ 0)
    (notInput : ∀ output input,
      exponent output ≠ Finsupp.single (inputVariables input) 1)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (targets exponent) circuit) :
    m ≤ circuit.cost (Algebraic.Arithmetic.gateCost (K := C)) :=
  (circuit_multiplication_lowerBound constant inputVariables exponent injective
    nonconstant notInput circuit constructs).trans
      (Combined.circuit_multiplicationCost_le_gateCost circuit)

/-- Raw circuit size is at least the number of selected monomial outputs. -/
theorem circuit_size_lowerBound
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ output, exponent output ≠ 0)
    (notInput : ∀ output input,
      exponent output ≠ Finsupp.single (inputVariables input) 1)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (targets exponent) circuit) :
    m ≤ circuit.size :=
  (circuit_gate_lowerBound constant inputVariables exponent injective nonconstant
    notInput circuit constructs).trans
      (Combined.circuit_gateCost_le_size circuit)

end
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
