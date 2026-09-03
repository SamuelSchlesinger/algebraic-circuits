import Algebraic.MassProduction.BlockInductionStep

/-!
# The equal-block induction

This module assembles the equal-block induction from its explicit parameter
and scheduler bounds. At level `k`, the input is split into one prefix block
of width `m` and a suffix of width `k * m`; successive steps cover every fixed
rational exponent below one.

All positivity and size conditions are ordinary hypotheses.  No instances
are declared here.
-/

namespace Algebraic
namespace MassProduction
namespace BlockInduction

open CodeParameters
open GroupedScheduler
open LineEnumeration
open Sorting

/-! ## Iterating the equal-block step -/

/-- Level `k` of the manuscript induction: all rational rates strictly below
`k / (k + 1)` have eventual mass production. -/
def ProducesAtLevel (level : Nat) : Prop :=
  ∀ numerator denominator : Nat,
    0 < denominator ->
    (level + 1) * numerator < level * denominator ->
    MassProducesAt numerator denominator

theorem producesAtLevel_one : ProducesAtLevel 1 := by
  intro numerator denominator denominatorPositive rateBelow
  apply _root_.Algebraic.MassProduction.EqualBlock.massProducesAt_of_rateBelowHalf
    numerator denominator denominatorPositive
  simpa using rateBelow

theorem producesAtLevel_succ
    (previousLevel : Nat)
    (previousLevelPositive : 0 < previousLevel)
    (previous : ProducesAtLevel previousLevel) :
    ProducesAtLevel (previousLevel + 1) := by
  intro numerator denominator denominatorPositive rateBelow
  let level := previousLevel + 1
  have levelAtLeastTwo : 2 <= level := by
    dsimp [level]
    omega
  have recursiveDenominatorPositive :
      0 < groupRateDenominator denominator * level := by
    unfold groupRateDenominator
    positivity
  have recursiveRate :
      (previousLevel + 1) * groupRateNumerator level denominator <
        previousLevel * (groupRateDenominator denominator * level) := by
    have rate := groupRate_below_previousLevel level denominator
      levelAtLeastTwo denominatorPositive
    simpa only [level, Nat.add_sub_cancel] using rate
  have recursive := previous (groupRateNumerator level denominator)
    (groupRateDenominator denominator * level)
    recursiveDenominatorPositive recursiveRate
  apply massProducesAt_step level numerator denominator levelAtLeastTwo
    denominatorPositive
  · simpa only [level, Nat.add_assoc] using rateBelow
  · exact recursive

theorem producesAtLevel_all
    (level : Nat)
    (levelPositive : 0 < level) :
    ProducesAtLevel level := by
  induction level with
  | zero => omega
  | succ previousLevel inductionHypothesis =>
      by_cases previousZero : previousLevel = 0
      · subst previousLevel
        simpa using producesAtLevel_one
      · have previousPositive : 0 < previousLevel :=
          Nat.pos_of_ne_zero previousZero
        simpa only [Nat.succ_eq_add_one] using
          producesAtLevel_succ previousLevel previousPositive
            (inductionHypothesis previousPositive)

/-- Eventual mass production at every fixed rational exponent strictly below
one.  A concrete level `numerator + 1` already suffices. -/
theorem massProducesAt_of_rateBelowOne
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowOne : numerator < denominator) :
    MassProducesAt numerator denominator := by
  let level := numerator + 1
  have levelPositive : 0 < level := by omega
  have numeratorSuccessorLe : numerator + 1 <= denominator := by omega
  have scaled := Nat.mul_le_mul_left (numerator + 1) numeratorSuccessorLe
  have levelRate : (level + 1) * numerator < level * denominator := by
    dsimp [level]
    calc
      (numerator + 1 + 1) * numerator <
          (numerator + 1) * (numerator + 1) := by
        nlinarith
      _ <= (numerator + 1) * denominator := scaled
  exact producesAtLevel_all level levelPositive numerator denominator
    denominatorPositive levelRate

/-! ## From eventual bounds to the every-length headline theorem -/

/-- Padding by the fixed cutoff converts an eventual theorem into an
every-positive-length theorem. -/
theorem massProducesAtAllLengths_of_eventual
    (numerator denominator : Nat)
    (production : MassProducesAt numerator denominator) :
    MassProducesAtAllLengths numerator denominator := by
  obtain ⟨eventualConstant, cutoff, eventualBound⟩ := production
  refine ⟨(2 * 2 ^ cutoff) * eventualConstant, ?_⟩
  intro inputWidth inputPositive function copies copiesPositive copiesBound
  let paddedWidth := inputWidth + cutoff
  have fits : inputWidth <= paddedWidth := by
    dsimp [paddedWidth]
    omega
  have paddedPositive : 0 < paddedWidth := inputPositive.trans_le fits
  have paddedPastCutoff : cutoff <= paddedWidth := by
    dsimp [paddedWidth]
    omega
  have paddedCopiesBound : copies <=
      rationalCopyBudget numerator denominator paddedWidth := by
    exact copiesBound.trans
      (rationalCopyBudget_mono_inputs
        (numerator := numerator) (denominator := denominator) fits)
  let paddedFunction := InputSplit.paddedFunction fits function
  have paddedMass := eventualBound paddedWidth paddedPositive
    paddedPastCutoff paddedFunction copies copiesPositive paddedCopiesBound
  have transport := InputSplit.booleanMassComplexity_le_paddedFunction
    inputPositive fits function copies
  have scaleBound : 2 ^ paddedWidth / paddedWidth <=
      (2 * 2 ^ cutoff) * (2 ^ inputWidth / inputWidth) := by
    apply shannonScale_le_of_le_add inputWidth paddedWidth cutoff inputPositive
      fits
    dsimp [paddedWidth]
    exact le_rfl
  calc
    booleanMassComplexity function copies <=
        booleanMassComplexity paddedFunction copies := transport
    _ <= (eventualConstant *
          (2 ^ paddedWidth / paddedWidth) : Nat) := paddedMass
    _ <= (((2 * 2 ^ cutoff) * eventualConstant) *
          (2 ^ inputWidth / inputWidth) : Nat) := by
      exact_mod_cast (calc
        eventualConstant * (2 ^ paddedWidth / paddedWidth) <=
            eventualConstant * ((2 * 2 ^ cutoff) *
              (2 ^ inputWidth / inputWidth)) := by gcongr
        _ = ((2 * 2 ^ cutoff) * eventualConstant) *
            (2 ^ inputWidth / inputWidth) := by ring)

/-- The formal counterpart of the manuscript's main theorem. -/
theorem exponentialMassProduction : ExponentialMassProduction := by
  intro numerator denominator denominatorPositive rateBelowOne
  exact massProducesAtAllLengths_of_eventual numerator denominator
    (massProducesAt_of_rateBelowOne numerator denominator
      denominatorPositive rateBelowOne)

end BlockInduction
end MassProduction
end Algebraic
