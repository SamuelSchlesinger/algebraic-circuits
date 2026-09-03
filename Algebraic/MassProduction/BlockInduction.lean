import Algebraic.MassProduction.BlockInductionFiniteStep

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

/-! ## Padding arbitrary widths to equal blocks -/

/-- A floor-stable comparison of Shannon scales when the larger width adds
at most `padding` variables. -/
theorem shannonScale_le_of_le_add
    (inputWidth targetWidth padding : Nat)
    (inputPositive : 0 < inputWidth)
    (fits : inputWidth <= targetWidth)
    (upper : targetWidth <= inputWidth + padding) :
    2 ^ targetWidth / targetWidth <=
      (2 * 2 ^ padding) * (2 ^ inputWidth / inputWidth) := by
  have powerBound : 2 ^ targetWidth <= 2 ^ padding * 2 ^ inputWidth := by
    calc
      2 ^ targetWidth <= 2 ^ (inputWidth + padding) :=
        Nat.pow_le_pow_right (by omega) upper
      _ = 2 ^ padding * 2 ^ inputWidth := by
        rw [Nat.pow_add]
        ring
  have inputFitsPower : inputWidth <= 2 ^ inputWidth := by
    exact (by omega : inputWidth <= 2 * inputWidth).trans
      (Nat.mul_le_pow (by decide : 2 ≠ 1) inputWidth)
  calc
    2 ^ targetWidth / targetWidth <= 2 ^ targetWidth / inputWidth :=
      Nat.div_le_div_left fits inputPositive
    _ <= (2 ^ padding * 2 ^ inputWidth) / inputWidth :=
      Nat.div_le_div_right powerBound
    _ <= 2 * 2 ^ padding * (2 ^ inputWidth / inputWidth) :=
      Growth.mul_div_le_two_mul_mul_div (2 ^ padding) (2 ^ inputWidth)
        inputWidth inputPositive inputFitsPower

/-- Smallest equal-block width whose complete input covers `inputWidth`. -/
def blockCeil (level inputWidth : Nat) : Nat :=
  inputWidth ⌈/⌉ (level + 1)

/-- Least multiple of `level + 1` represented by the equal-block layout. -/
def nextEqualBlockWidth (level inputWidth : Nat) : Nat :=
  stepInputWidth level (blockCeil level inputWidth)

theorem inputWidth_le_nextEqualBlockWidth
    (level inputWidth : Nat) :
    inputWidth <= nextEqualBlockWidth level inputWidth := by
  have capacity : inputWidth <=
      (level + 1) * (inputWidth ⌈/⌉ (level + 1)) :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < level + 1)).mp le_rfl
  unfold nextEqualBlockWidth stepInputWidth blockCeil
  calc
    inputWidth <= (level + 1) * (inputWidth ⌈/⌉ (level + 1)) := capacity
    _ = inputWidth ⌈/⌉ (level + 1) +
        level * (inputWidth ⌈/⌉ (level + 1)) := by ring

theorem nextEqualBlockWidth_le_add
    (level inputWidth : Nat) :
    nextEqualBlockWidth level inputWidth <= inputWidth + (level + 1) := by
  let divisor := level + 1
  have divisorPositive : 0 < divisor := by omega
  have ceiling := CodeParameters.ceilDiv_le_div_add_one inputWidth divisor
    divisorPositive
  have floor := Nat.mul_div_le inputWidth divisor
  unfold nextEqualBlockWidth stepInputWidth blockCeil
  dsimp [divisor] at ceiling floor
  calc
    inputWidth ⌈/⌉ (level + 1) +
        level * (inputWidth ⌈/⌉ (level + 1)) =
      (level + 1) * (inputWidth ⌈/⌉ (level + 1)) := by ring
    _ <= (level + 1) * (inputWidth / (level + 1) + 1) := by gcongr
    _ = (level + 1) * (inputWidth / (level + 1)) +
        (level + 1) := by ring
    _ <= inputWidth + (level + 1) := Nat.add_le_add_right floor _

theorem shannonScale_nextEqualBlockWidth_le
    (level inputWidth : Nat)
    (inputPositive : 0 < inputWidth) :
    2 ^ nextEqualBlockWidth level inputWidth /
        nextEqualBlockWidth level inputWidth <=
      (2 * 2 ^ (level + 1)) * (2 ^ inputWidth / inputWidth) :=
  shannonScale_le_of_le_add inputWidth
    (nextEqualBlockWidth level inputWidth) (level + 1) inputPositive
    (inputWidth_le_nextEqualBlockWidth level inputWidth)
    (nextEqualBlockWidth_le_add level inputWidth)

/-- The manuscript's equal-block induction step on arbitrary sufficiently
large input widths. -/
theorem massProducesAt_step
    (level numerator denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (previous : MassProducesAt
      (groupRateNumerator level denominator)
      (groupRateDenominator denominator * level)) :
    MassProducesAt numerator denominator := by
  obtain ⟨equalConstant, eventualEqualBound⟩ :=
    eventually_step_mass_bound level numerator denominator levelAtLeastTwo
      denominatorPositive rateBelowLevel previous
  obtain ⟨blockCutoff, equalBound⟩ :=
    Filter.eventually_atTop.1 eventualEqualBound
  refine ⟨(2 * 2 ^ (level + 1)) * equalConstant,
    (level + 1) * blockCutoff, ?_⟩
  intro inputWidth inputPositive pastCutoff function copies copiesPositive
    copiesBound
  let blockWidth := blockCeil level inputWidth
  let paddedWidth := nextEqualBlockWidth level inputWidth
  have fits : inputWidth <= paddedWidth :=
    inputWidth_le_nextEqualBlockWidth level inputWidth
  have blockPastCutoff : blockCutoff <= blockWidth := by
    have capacity : inputWidth <= (level + 1) * blockWidth := by
      dsimp [blockWidth, blockCeil]
      exact (ceilDiv_le_iff_le_mul (by omega : 0 < level + 1)).mp le_rfl
    have scaled : (level + 1) * blockCutoff <=
        (level + 1) * blockWidth := pastCutoff.trans capacity
    exact Nat.le_of_mul_le_mul_left scaled (by omega)
  have paddedCopiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator) := by
    have widened := copiesBound.trans
      (rationalCopyBudget_mono_inputs
        (numerator := numerator) (denominator := denominator) fits)
    simpa [rationalCopyBudget, paddedWidth, nextEqualBlockWidth] using widened
  let paddedFunction := InputSplit.paddedFunction fits function
  have paddedMass := equalBound blockWidth blockPastCutoff paddedFunction
    copies copiesPositive paddedCopiesBound
  have transport := InputSplit.booleanMassComplexity_le_paddedFunction
    inputPositive fits function copies
  have scaleBound := shannonScale_nextEqualBlockWidth_le level inputWidth
    inputPositive
  calc
    booleanMassComplexity function copies <=
        booleanMassComplexity paddedFunction copies := transport
    _ <= (equalConstant *
          (2 ^ stepInputWidth level blockWidth /
            stepInputWidth level blockWidth) : Nat) := paddedMass
    _ = (equalConstant * (2 ^ paddedWidth / paddedWidth) : Nat) := by rfl
    _ <= (((2 * 2 ^ (level + 1)) * equalConstant) *
          (2 ^ inputWidth / inputWidth) : Nat) := by
      exact_mod_cast (calc
        equalConstant * (2 ^ paddedWidth / paddedWidth) <=
            equalConstant * ((2 * 2 ^ (level + 1)) *
              (2 ^ inputWidth / inputWidth)) := by gcongr
        _ = ((2 * 2 ^ (level + 1)) * equalConstant) *
            (2 ^ inputWidth / inputWidth) := by ring)

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
