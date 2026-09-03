import Algebraic.Basis.DeMorgan
import Algebraic.MassProduction.DirectProduct

/-!
# Exact statements of Boolean mass production

This module fixes the circuit model and quantifiers used by
`projects/complexity/sharing/main.tex`.  Rates are represented by natural
fractions and the copy budget is
`2 ^ floor (numerator * inputs / denominator)`.  Keeping the finite statement
discrete avoids hiding real-number rounding in the circuit theorem.

`MassProducesAt` is the eventual form used by the induction in the paper.
`MassProducesAtAllLengths` is the final, every-positive-input-length form of
the headline theorem.  Neither definition asserts that the theorem has
already been proved.
-/

namespace Algebraic
namespace MassProduction

/-- Minimum standard De Morgan cost of independently evaluating one Boolean
function on `copies` row-major input blocks. -/
noncomputable def booleanMassComplexity
    (function : ScalarFunction Bool inputs)
    (copies : Nat) : ℕ∞ :=
  Circuit.costComplexity DeMorgan.interpretation DeMorgan.standardCost
    (directProduct function copies)

/-- The discrete copy budget at rational exponent `numerator / denominator`.
Natural division is deliberate: it implements the floor in the exponent. -/
def rationalCopyBudget
    (numerator denominator inputs : Nat) : Nat :=
  2 ^ (numerator * inputs / denominator)

/-- Eventual worst-case mass production at one rational exponent.

The constant and cutoff may depend on the fixed exponent, but not on the
input length, function, or requested number of copies.  Positivity is carried
as an ordinary hypothesis rather than a typeclass instance. -/
def MassProducesAt (numerator denominator : Nat) : Prop :=
  ∃ constant cutoff : Nat,
    ∀ inputs : Nat, 0 < inputs → cutoff ≤ inputs →
      ∀ (function : ScalarFunction Bool inputs) (copies : Nat),
        0 < copies →
        copies ≤ rationalCopyBudget numerator denominator inputs →
          booleanMassComplexity function copies ≤
            (constant * (2 ^ inputs / inputs) : Nat)

/-- Every-positive-length version of mass production at one rational
exponent.  This is the direct discrete analogue of the manuscript's main
theorem after the exponent is fixed. -/
def MassProducesAtAllLengths (numerator denominator : Nat) : Prop :=
  ∃ constant : Nat,
    ∀ inputs : Nat, 0 < inputs →
      ∀ (function : ScalarFunction Bool inputs) (copies : Nat),
        0 < copies →
        copies ≤ rationalCopyBudget numerator denominator inputs →
          booleanMassComplexity function copies ≤
            (constant * (2 ^ inputs / inputs) : Nat)

/-- The manuscript's exponential-range conclusion, in its exact rational and
discrete form: every nonnegative rational exponent strictly below one has a
uniform all-length mass-production bound. -/
def ExponentialMassProduction : Prop :=
  ∀ numerator denominator : Nat,
    0 < denominator → numerator < denominator →
      MassProducesAtAllLengths numerator denominator

/-- The all-length statement immediately implies its eventual counterpart. -/
theorem MassProducesAtAllLengths.eventually
    {numerator denominator : Nat}
    (production : MassProducesAtAllLengths numerator denominator) :
    MassProducesAt numerator denominator := by
  obtain ⟨constant, bound⟩ := production
  exact ⟨constant, 0, fun inputs positive _ function copies copiesPositive
    copiesBound =>
      bound inputs positive function copies copiesPositive copiesBound⟩

/-- Enlarging the allowed numerator weakens the eventual production
statement. -/
theorem MassProducesAt.mono_numerator
    {small large denominator : Nat}
    (production : MassProducesAt large denominator)
    (numeratorBound : small ≤ large) :
    MassProducesAt small denominator := by
  obtain ⟨constant, cutoff, bound⟩ := production
  refine ⟨constant, cutoff, ?_⟩
  intro inputs inputsPositive pastCutoff function copies copiesPositive
    copiesBound
  apply bound inputs inputsPositive pastCutoff function copies copiesPositive
  exact copiesBound.trans <| by
    unfold rationalCopyBudget
    apply Nat.pow_le_pow_right (by omega)
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right inputs numeratorBound

/-- Enlarging the allowed numerator also weakens the all-length statement. -/
theorem MassProducesAtAllLengths.mono_numerator
    {small large denominator : Nat}
    (production : MassProducesAtAllLengths large denominator)
    (numeratorBound : small ≤ large) :
    MassProducesAtAllLengths small denominator := by
  obtain ⟨constant, bound⟩ := production
  refine ⟨constant, ?_⟩
  intro inputs inputsPositive function copies copiesPositive copiesBound
  apply bound inputs inputsPositive function copies copiesPositive
  exact copiesBound.trans <| by
    unfold rationalCopyBudget
    apply Nat.pow_le_pow_right (by omega)
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right inputs numeratorBound

end MassProduction
end Algebraic
