import Algebraic.MassProduction.BlockInductionOverhead

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

/-! ## Recursive resource bank -/

/-- Previous-level Shannon-scale bound supplied to every resource function. -/
def stepResourceBound
    (recursiveConstant level blockWidth : Nat) : Nat :=
  recursiveConstant *
    (2 ^ stepSuffixWidth level blockWidth /
      stepSuffixWidth level blockWidth)

/-- Full-input coefficient contributed by the recursive resource bank. -/
def stepResourceConstant
    (denominator recursiveConstant : Nat) : Nat :=
  4 * resourceConstant (stepDimension denominator) * recursiveConstant

/-- Multiplying the previous level's Shannon-scale resource complexity by
the number of encoded resource bits remains at the full-input Shannon scale.
-/
theorem step_resourceTerm_le
    (level denominator blockWidth recursiveConstant : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth) :
    ResourceEvaluation.resourceBitCount
          (stepDimension denominator)
          (fieldWidth blockWidth (stepDimension denominator)
            (stepDimension_positive denominatorPositive)) *
        stepResourceBound recursiveConstant level blockWidth <=
      stepResourceConstant denominator recursiveConstant *
        (2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let suffixWidth := stepSuffixWidth level blockWidth
  let inputWidth := stepInputWidth level blockWidth
  let scale := 2 ^ inputWidth / inputWidth
  have countBound := resourceBitCount_le blockWidth dimension dimensionPositive
  have suffixPositive : 0 < suffixWidth := by
    dsimp [suffixWidth, stepSuffixWidth]
    positivity
  have inputPositive : 0 < inputWidth := by
    dsimp [inputWidth, stepInputWidth]
    positivity
  have suffixLeInput : suffixWidth <= inputWidth := by
    dsimp [suffixWidth, inputWidth, stepSuffixWidth, stepInputWidth]
    omega
  have inputLeDoubleSuffix : inputWidth <= 2 * suffixWidth := by
    have blockLeSuffix : blockWidth <= suffixWidth := by
      dsimp [suffixWidth, stepSuffixWidth]
      calc
        blockWidth = 1 * blockWidth := by ring
        _ <= level * blockWidth :=
          Nat.mul_le_mul_right blockWidth (by omega)
    calc
      inputWidth = blockWidth + suffixWidth := by rfl
      _ <= suffixWidth + suffixWidth :=
        Nat.add_le_add_right blockLeSuffix suffixWidth
      _ = 2 * suffixWidth := by ring
  have twiceInputFits : 2 * inputWidth <= 2 ^ inputWidth :=
    Nat.mul_le_pow (by decide : 2 ≠ 1) inputWidth
  have twiceSuffixFits : 2 * suffixWidth <= 2 ^ inputWidth :=
    (Nat.mul_le_mul_left 2 suffixLeInput).trans twiceInputFits
  have doubledQuotient := Growth.div_le_four_mul_double_div
    (2 ^ inputWidth) suffixWidth suffixPositive twiceSuffixFits
  have denominatorComparison :
      2 ^ inputWidth / (2 * suffixWidth) <=
        2 ^ inputWidth / inputWidth :=
    Nat.div_le_div_left inputLeDoubleSuffix inputPositive
  have quotientBound : 2 ^ inputWidth / suffixWidth <= 4 * scale :=
    doubledQuotient.trans <|
      Nat.mul_le_mul_left 4 denominatorComparison
  have productQuotient :
      2 ^ blockWidth * (2 ^ suffixWidth / suffixWidth) <=
        2 ^ inputWidth / suffixWidth := by
    calc
      2 ^ blockWidth * (2 ^ suffixWidth / suffixWidth) <=
          (2 ^ blockWidth * 2 ^ suffixWidth) / suffixWidth :=
        Nat.mul_div_le_mul_div_assoc
          (2 ^ blockWidth) (2 ^ suffixWidth) suffixWidth
      _ = 2 ^ inputWidth / suffixWidth := by
        apply congrArg (fun value => value / suffixWidth)
        rw [← Nat.pow_add]
        rfl
  change ResourceEvaluation.resourceBitCount dimension width *
      (recursiveConstant * (2 ^ suffixWidth / suffixWidth)) <=
    stepResourceConstant denominator recursiveConstant * scale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
        (recursiveConstant * (2 ^ suffixWidth / suffixWidth)) <=
      (resourceConstant dimension * 2 ^ blockWidth) *
        (recursiveConstant * (2 ^ suffixWidth / suffixWidth)) := by gcongr
    _ = resourceConstant dimension * recursiveConstant *
        (2 ^ blockWidth * (2 ^ suffixWidth / suffixWidth)) := by ring
    _ <= resourceConstant dimension * recursiveConstant *
        (2 ^ inputWidth / suffixWidth) := by gcongr
    _ <= resourceConstant dimension * recursiveConstant *
        (4 * scale) := by gcongr
    _ = stepResourceConstant denominator recursiveConstant * scale := by
      unfold stepResourceConstant
      dsimp [dimension]
      ring

/-! ## The finite and eventual induction steps -/

/-- Fully instantiated finite composition for one equal-block induction
step, assuming a uniform recursive bound for each induced suffix function. -/
theorem step_finiteComposition
    (level numerator denominator blockWidth copies recursiveConstant : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (suffixLarge : 16 <= stepSuffixWidth level blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator))
    (function : ScalarFunction Bool (stepInputWidth level blockWidth))
    (resourceComplexity :
      let dimension := stepDimension denominator
      let dimensionPositive := stepDimension_positive denominatorPositive
      let width := fieldWidth blockWidth dimension dimensionPositive
      let split := InputSplit.splitFunction
        (prefixWidth := blockWidth)
        (suffixWidth := stepSuffixWidth level blockWidth) function
      ∀ member : Fin (ResourceEvaluation.resourceBitCount dimension width),
        booleanMassComplexity
            (CompositionBound.canonicalResourceFunction
              (fieldWidth_positive blockWidth dimension dimensionPositive)
              (fieldWidth_packingFits blockWidth dimension dimensionPositive)
              split member)
            (groupCount level denominator blockWidth) <=
          (stepResourceBound recursiveConstant level blockWidth : Nat)) :
    booleanMassComplexity function copies <=
      (FiniteParameters.canonicalCostBound copies
        (groupCount level denominator blockWidth) blockWidth
        (stepDimension denominator)
        (fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive))
        (stepSuffixWidth level blockWidth)
        (stepResourceBound recursiveConstant level blockWidth) : Nat) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let split := InputSplit.splitFunction
    (prefixWidth := blockWidth) (suffixWidth := suffixWidth) function
  have loadBound : requestGroupSize copies groups * 2 ^ width <
      2 ^ (width * (dimension - 1)) := by
    exact step_loadBound level numerator denominator blockWidth copies
      levelAtLeastTwo denominatorPositive rateBelowLevel blockLarge
      (by simpa [stepInputWidth, Nat.add_mul, Nat.add_comm] using copiesBound)
  have composition := CodeParameters.booleanMassComplexity_le
    copies groups blockWidth dimension suffixWidth
    (stepDimension_atLeastTwo denominatorPositive)
    (groupCount_positive level denominator blockWidth) suffixLarge loadBound
    split (stepResourceBound recursiveConstant level blockWidth)
    resourceComplexity
  have recovered : RuntimePipeline.requestFunction split = function := by
    dsimp [split]
    exact InputSplit.requestFunction_splitFunction function
  rw [recovered] at composition
  exact composition

/-- Sum of the recursive resource coefficient and one overhead unit. -/
def stepMassConstant
    (denominator recursiveConstant : Nat) : Nat :=
  stepResourceConstant denominator recursiveConstant + 1

/-- Once the overhead has entered one Shannon-scale unit, adding the
recursive resource bank gives the complete canonical bound. -/
theorem step_canonicalCostBound_le
    (level denominator blockWidth copies recursiveConstant : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth)
    (overheadBound :
      let dimension := stepDimension denominator
      let dimensionPositive := stepDimension_positive denominatorPositive
      let width := fieldWidth blockWidth dimension dimensionPositive
      let groups := groupCount level denominator blockWidth
      let schedulerDepth :=
        FiniteParameters.schedulerDepth copies groups width
      let groupBitWidth := FiniteParameters.groupBitWidth groups
      let orderWidth := FiniteParameters.orderWidth copies width
      let routingDepth :=
        FiniteParameters.routingDepth copies groups dimension width
      CompositionBound.overheadCostBound copies groups blockWidth dimension
          width (stepSuffixWidth level blockWidth) schedulerDepth
          groupBitWidth orderWidth routingDepth routingDepth <=
        2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) :
    FiniteParameters.canonicalCostBound copies
        (groupCount level denominator blockWidth) blockWidth
        (stepDimension denominator)
        (fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive))
        (stepSuffixWidth level blockWidth)
        (stepResourceBound recursiveConstant level blockWidth) <=
      stepMassConstant denominator recursiveConstant *
        (2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let scale := 2 ^ stepInputWidth level blockWidth /
    stepInputWidth level blockWidth
  have resourceBound := step_resourceTerm_le level denominator blockWidth
    recursiveConstant levelAtLeastTwo denominatorPositive blockPositive
  change ResourceEvaluation.resourceBitCount dimension width *
      stepResourceBound recursiveConstant level blockWidth +
      CompositionBound.overheadCostBound copies groups blockWidth dimension
        width suffixWidth
        (FiniteParameters.schedulerDepth copies groups width)
        (FiniteParameters.groupBitWidth groups)
        (FiniteParameters.orderWidth copies width)
        (FiniteParameters.routingDepth copies groups dimension width)
        (FiniteParameters.routingDepth copies groups dimension width) <=
    stepMassConstant denominator recursiveConstant * scale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
          stepResourceBound recursiveConstant level blockWidth +
        CompositionBound.overheadCostBound copies groups blockWidth dimension
          width suffixWidth
          (FiniteParameters.schedulerDepth copies groups width)
          (FiniteParameters.groupBitWidth groups)
          (FiniteParameters.orderWidth copies width)
          (FiniteParameters.routingDepth copies groups dimension width)
          (FiniteParameters.routingDepth copies groups dimension width) <=
      stepResourceConstant denominator recursiveConstant * scale + scale :=
        Nat.add_le_add resourceBound overheadBound
    _ = stepMassConstant denominator recursiveConstant * scale := by
      unfold stepMassConstant
      ring

/-- Equal-multiple induction step: a previous-level eventual theorem gives
the next level for all sufficiently large equal block widths. -/
theorem eventually_step_mass_bound
    (level numerator denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (previous : MassProducesAt
      (groupRateNumerator level denominator)
      (groupRateDenominator denominator * level)) :
    ∃ nextConstant : Nat,
      ∀ᶠ blockWidth in Filter.atTop,
        ∀ (function : ScalarFunction Bool (stepInputWidth level blockWidth))
          (copies : Nat),
          0 < copies ->
          copies <=
            2 ^ (numerator * stepInputWidth level blockWidth / denominator) ->
          booleanMassComplexity function copies <=
            (nextConstant *
              (2 ^ stepInputWidth level blockWidth /
                stepInputWidth level blockWidth) : Nat) := by
  obtain ⟨recursiveConstant, recursiveCutoff, recursiveBound⟩ := previous
  refine ⟨stepMassConstant denominator recursiveConstant, ?_⟩
  have overhead := eventually_step_overhead_le level numerator denominator
    levelAtLeastTwo denominatorPositive rateBelowLevel
  filter_upwards [overhead,
    Filter.eventually_ge_atTop (max recursiveCutoff 16),
    Filter.eventually_ge_atTop (4 * denominator)] with blockWidth
      overheadBound blockLarge rateLarge
  intro function copies copiesPositive copiesBound
  have blockPositive : 0 < blockWidth := by omega
  have suffixPositive : 0 < stepSuffixWidth level blockWidth := by
    unfold stepSuffixWidth
    positivity
  have suffixPastCutoff : recursiveCutoff <=
      stepSuffixWidth level blockWidth := by
    have cutoffLeBlock : recursiveCutoff <= blockWidth := by omega
    exact cutoffLeBlock.trans <| by
      unfold stepSuffixWidth
      calc
        blockWidth = 1 * blockWidth := by ring
        _ <= level * blockWidth :=
          Nat.mul_le_mul_right blockWidth (by omega)
  have suffixLarge : 16 <= stepSuffixWidth level blockWidth := by
    have sixteenLeBlock : 16 <= blockWidth := by omega
    exact sixteenLeBlock.trans <| by
      unfold stepSuffixWidth
      calc
        blockWidth = 1 * blockWidth := by ring
        _ <= level * blockWidth :=
          Nat.mul_le_mul_right blockWidth (by omega)
  have finite := step_finiteComposition level numerator denominator
    blockWidth copies recursiveConstant levelAtLeastTwo denominatorPositive
    rateBelowLevel rateLarge suffixLarge copiesBound function (by
      dsimp only
      intro member
      apply recursiveBound (stepSuffixWidth level blockWidth) suffixPositive
        suffixPastCutoff _ (groupCount level denominator blockWidth)
        (groupCount_positive level denominator blockWidth)
      exact groupCount_le_recursiveBudget level denominator blockWidth
        (by omega))
  have canonical := step_canonicalCostBound_le level denominator blockWidth
    copies recursiveConstant levelAtLeastTwo denominatorPositive blockPositive
    (overheadBound copies copiesPositive copiesBound)
  exact finite.trans (by exact_mod_cast canonical)

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
