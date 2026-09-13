import Algebraic.CircuitFamily
import Cslib.Foundations.Data.Nat.Asymptotics

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
theorem _root_.Cslib.Circuits.Circuit.Resource.eventually_const_mul_pow_le_two_pow
    (constant degree : Nat) :
    ∀ᶠ n in atTop, constant * n ^ degree <= 2 ^ n :=
  Nat.eventually_mul_pow_le_pow constant degree (by decide)

export Cslib.Circuits.Circuit.Resource (eventually_const_mul_pow_le_two_pow)

end Resource
end Circuit
end Algebraic
