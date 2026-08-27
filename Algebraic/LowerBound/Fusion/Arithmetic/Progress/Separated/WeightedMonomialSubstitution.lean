import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.MonomialSubstitution

/-!
# Positive weighted monomial substitutions

A weighted monomial substitution sends each source variable to one monomial
with a specified natural coefficient.  If every weight is positive, the
weights affect coefficients but not support: the support is still the image
of the source support under the linear exponent map.

This is the coefficient-aware extension of `MonomialSubstitution` needed for
positive named constants.  A positive scalar is represented by a monomial of
exponent zero and that scalar as its weight.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace WeightedMonomialSubstitution

noncomputable section

variable {SourceVar : Type u}
variable {TargetVar : Type v}

/-- Send a source variable to a monomial with the prescribed exponent and
coefficient. -/
def substitution
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (source : SourceVar) : MvPolynomial TargetVar ℕ :=
  MvPolynomial.monomial (basis source) (weight source)

/-- Product of the coefficient weights contributed by a source monomial. -/
def coefficient
    (weight : SourceVar → ℕ)
    (exponent : SourceVar →₀ ℕ) : ℕ :=
  exponent.prod fun source power => weight source ^ power

/-- A weighted monomial substitution still expands one monomial to one
monomial; its exponent and coefficient are computed independently. -/
theorem monomialExpansion_eq
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (exponent : SourceVar →₀ ℕ) :
    Expansion.monomialExpansion (substitution weight basis) exponent =
      MvPolynomial.monomial
        (MonomialSubstitution.exponentMap basis exponent)
        (coefficient weight exponent) := by
  rw [Expansion.monomialExpansion, MvPolynomial.bind₁_monomial]
  simp only [MvPolynomial.C_1, one_mul, substitution,
    MvPolynomial.monomial_pow]
  rw [MonomialSubstitution.exponentMap,
    Finsupp.linearCombination_apply, coefficient]
  simp only [Finsupp.prod, Finsupp.sum]
  exact (MvPolynomial.monomial_sum_prod exponent.support
    (fun source => exponent source • basis source)
    (fun source => weight source ^ exponent source)).symm

/-- Positivity of all variable weights implies positivity of every monomial
coefficient produced by the substitution. -/
theorem coefficient_pos
    (weight : SourceVar → ℕ)
    (positive : ∀ source, 0 < weight source)
    (exponent : SourceVar →₀ ℕ) :
    0 < coefficient weight exponent := by
  rw [coefficient, Finsupp.prod]
  exact Finset.prod_pos fun source _ =>
    pow_pos (positive source) _

/-- Under positive weights, every source monomial has singleton support at
the ordinary linear exponent image. -/
@[simp] theorem support_monomialExpansion
    [DecidableEq TargetVar]
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (positive : ∀ source, 0 < weight source)
    (exponent : SourceVar →₀ ℕ) :
    (Expansion.monomialExpansion
      (substitution weight basis) exponent).support =
        {MonomialSubstitution.exponentMap basis exponent} := by
  rw [monomialExpansion_eq, MvPolynomial.support_monomial]
  simp [Nat.ne_of_gt (coefficient_pos weight positive exponent)]

/-- Apply a weighted monomial substitution to a polynomial. -/
def transform
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    MvPolynomial TargetVar ℕ :=
  MvPolynomial.bind₁ (substitution weight basis) polynomial

/-- Exact support of a positive weighted monomial substitution. -/
theorem support_transform
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (positive : ∀ source, 0 < weight source)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (transform weight basis polynomial).support =
      polynomial.support.image
        (MonomialSubstitution.exponentMap basis) := by
  classical
  rw [transform, Expansion.support_bind₁]
  simp_rw [support_monomialExpansion weight basis positive]
  exact Finset.biUnion_singleton

end
end WeightedMonomialSubstitution
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
