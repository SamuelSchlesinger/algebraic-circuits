import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Degree-visible catalecticant fusion

The middle catalecticant at half-degree `n` only reads coefficients of total
degree `2 * n`.  Consequently every lower-degree polynomial is invisible to
the feature.  This supplies a structural way to discharge the invisible
branch of `PowerOrInvisibleAtMultiplications`.

The resulting ordinary-circuit subclass permits arbitrary lower-degree
multiplication outputs and charges only critical-degree outputs, which must be
scalar multiples of `2n`-th powers of linear forms.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Degree

noncomputable section

open scoped BigOperators

variable {K : Type} {C : Type}

/-- Every coefficient read by the middle catalecticant vanishes below the
critical total degree. -/
theorem coeff_entryExponent_eq_zero_of_totalDegree_lt
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (small : polynomial.totalDegree < 2 * n)
    (row column : SumOfTerms.MatrixRank.Layer (2 * n) n) :
    MvPolynomial.coeff (SumOfTerms.Waring.entryExponent n row column)
      polynomial = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  have degree :
      (∑ index ∈
          (SumOfTerms.Waring.entryExponent n row column).support,
        SumOfTerms.Waring.entryExponent n row column index) = 2 * n := by
    change (SumOfTerms.Waring.entryExponent n row column).sum
      (fun _ multiplicity => multiplicity) = 2 * n
    exact SumOfTerms.Waring.exponent_add_complement_sum n row column
  rw [degree]
  exact small

/-- A polynomial below total degree `2n` has zero middle catalecticant. -/
theorem catalecticant_eq_zero_of_totalDegree_lt
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (small : polynomial.totalDegree < 2 * n) :
    SumOfTerms.Waring.catalecticant K n polynomial = 0 := by
  ext row column
  simp [SumOfTerms.Waring.catalecticant_apply,
    coeff_entryExponent_eq_zero_of_totalDegree_lt n polynomial small]

/-- A polynomial below total degree `2n` is invisible to the catalecticant
linear-map feature. -/
theorem feature_eq_zero_of_totalDegree_lt
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (small : polynomial.totalDegree < 2 * n) :
    SumOfTerms.Waring.feature K n polynomial = 0 := by
  simp [SumOfTerms.Waring.feature,
    catalecticant_eq_zero_of_totalDegree_lt n polynomial small]

/-- Structural ordinary-circuit restriction: each multiplication output is
either below the critical degree or one scalar multiple of a `2n`-th power of
a linear form. -/
def LowDegreeOrPowerAtMultiplications
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin (2 * n)) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature C)
      (MvPolynomial (Fin (2 * n)) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin (2 * n) →
            MvPolynomial (Fin (2 * n)) K) →
    (arguments (0 : Fin 2) * arguments (1 : Fin 2)).totalDegree < 2 * n ∨
      ∃ term : SumOfTerms.Waring.Term K n,
        arguments (0 : Fin 2) * arguments (1 : Fin 2) =
          SumOfTerms.Waring.termValue term

/-- The structural degree-or-power restriction implies the semantic
power-or-invisible restriction. -/
theorem powerOrInvisible_of_lowDegreeOrPower
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    PowerOrInvisibleAtMultiplications constant n circuit := by
  intro arguments present
  rcases restricted arguments present with small | power
  · exact Or.inl (feature_eq_zero_of_totalDegree_lt n _ small)
  · exact Or.inr power

/-- Degree-or-power multiplication outputs have catalecticant rank at most
one. -/
theorem multiplicationOutputRankAtMost_one_of_lowDegreeOrPower
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    MultiplicationOutputRankAtMost constant n positive circuit 1 :=
  multiplicationOutputRankAtMost_one_of_powerOrInvisible constant n positive
    circuit
      (powerOrInvisible_of_lowDegreeOrPower constant n circuit restricted)

/-- Every degree-or-power ordinary arithmetic circuit for the squarefree
target needs central-binomial multiplication cost. -/
theorem multiplication_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  powerOrInvisible_multiplication_lowerBound constant n positive circuit
    constructs
      (powerOrInvisible_of_lowDegreeOrPower constant n circuit restricted)

/-- Explicit exponential size lower bound for the structural degree-or-power
ordinary arithmetic circuit subclass. -/
theorem four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    4 ^ n < n * circuit.size :=
  powerOrInvisible_four_pow_lt_mul_size constant n n_big circuit constructs
    (powerOrInvisible_of_lowDegreeOrPower constant n circuit restricted)

end
end Degree
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
