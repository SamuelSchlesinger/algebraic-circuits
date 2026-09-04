import Algebraic.CircuitFamily
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Eventual growth bounds for circuit resources

Polynomial resource bounds and exponential lower bounds meet repeatedly in
circuit complexity. This module records the elementary asymptotic bridge in
the generic `Circuit.Resource` namespace: every fixed natural monomial,
including its coefficient, is eventually dominated by `2^n`.
-/

namespace Algebraic
namespace Circuit
namespace Resource

open Filter
open scoped Topology

/-- Every fixed natural polynomial monomial, including a fixed coefficient,
is eventually bounded by the matching binary exponential. -/
theorem eventually_const_mul_pow_le_two_pow
    (constant degree : Nat) :
    ∀ᶠ n in atTop, constant * n ^ degree <= 2 ^ n := by
  have little :=
    isLittleO_pow_const_const_pow_of_one_lt (R := Real) degree
      (show (1 : Real) < 2 by norm_num)
  have epsilonPositive : 0 < (1 / (constant + 1 : Real)) := by positivity
  have bounded := little.bound epsilonPositive
  filter_upwards [bounded] with n hn
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (Nat.cast_nonneg n),
    Real.norm_eq_abs, abs_pow, abs_of_nonneg (by norm_num : (0 : Real) <= 2),
    one_div] at hn
  have castBound :
      (constant : Real) * (n : Real) ^ degree <= (2 : Real) ^ n := by
    have coefficientBound :
        (constant : Real) <= (constant + 1 : Real) := by norm_num
    calc
      (constant : Real) * (n : Real) ^ degree <=
          (constant + 1 : Real) * (n : Real) ^ degree := by
        gcongr
      _ <= (constant + 1 : Real) *
          ((constant + 1 : Real)⁻¹ * (2 : Real) ^ n) := by
        gcongr
      _ = (2 : Real) ^ n := by
        field_simp
  exact_mod_cast castBound

end Resource
end Circuit
end Algebraic
