import Algebraic.MassProduction.EqualBlockVolumeBound
import Algebraic.MassProduction.Growth
import Algebraic.MassProduction.InputSplit
import Algebraic.MassProduction.OverheadBound

/-!
# Exact parameters for the equal-block induction

This module assembles the two-block base case of the fixed-exponent induction.
Rates remain natural fractions, block lengths remain integral, and all floor
and ceiling operations are explicit.
-/

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters
open GroupedScheduler
open LineEnumeration
open Sorting

/-- Fixed coefficient multiplying the polynomial-times-subunit-exponential
upper bound for every non-resource gate. -/
def twoBlockOverheadConstant (denominator : Nat) : Nat :=
  twoBlockVolumeConstant denominator *
    (twoBlockCoefficientConstant denominator * 2 ^ 10)

/-- Pointwise composition of the exact ledger, record-volume estimate, and
polynomial coefficient estimate. -/
theorem twoBlock_overhead_le_of_growth
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (blockPositive : 0 < blockWidth)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator))
    (growthBound :
      twoBlockOverheadConstant denominator *
          (blockWidth + blockWidth) ^ 10 *
          2 ^ ((twoBlockMarginDenominator denominator - 1) *
            (blockWidth + blockWidth) /
              twoBlockMarginDenominator denominator) <=
        2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
    let groupBitWidth := FiniteParameters.groupBitWidth 1
    let orderWidth := FiniteParameters.orderWidth copies width
    let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
    CompositionBound.overheadCostBound copies 1 blockWidth dimension width
        blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
        routingDepth <=
      2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth) := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
  let groupBitWidth := FiniteParameters.groupBitWidth 1
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
  let parameterBound := twoBlockParameterBound denominator blockWidth
  let inputWidth := blockWidth + blockWidth
  let commonExponent := (twoBlockMarginDenominator denominator - 1) *
    inputWidth / twoBlockMarginDenominator denominator
  obtain ⟨dimensionBound, widthBound, schedulerBound, prefixBound,
      keyBound, suffixBound, orderBound, routingBound⟩ :=
    twoBlock_parameters_bounded numerator denominator blockWidth copies
      denominatorPositive rateBelowHalf copiesBound
  have factored := OverheadBound.overheadCostBound_le_factored
    copies 1 blockWidth dimension width blockWidth schedulerDepth
    groupBitWidth orderWidth routingDepth
    (fieldWidth_positive blockWidth dimension dimensionPositive)
  have byVolume := OverheadBound.factoredOverhead_le_volume_mul_envelope
    copies 1 blockWidth dimension width blockWidth schedulerDepth
    groupBitWidth orderWidth routingDepth parameterBound dimensionBound
    widthBound schedulerBound prefixBound keyBound suffixBound orderBound
    routingBound
  have volumeBound := twoBlock_overheadVolume_exponential_le
    numerator denominator blockWidth copies denominatorPositive rateBelowHalf
    copiesPositive copiesBound
  have coefficientBound := twoBlock_coefficient_le_monomial
    denominator blockWidth blockPositive
  calc
    CompositionBound.overheadCostBound copies 1 blockWidth dimension width
        blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
        routingDepth <=
      OverheadBound.factoredOverhead copies 1 blockWidth dimension width
        blockWidth schedulerDepth groupBitWidth orderWidth routingDepth :=
      factored
    _ <= OverheadBound.overheadVolume copies 1 width schedulerDepth
          routingDepth *
        (OverheadBound.coefficientEnvelope parameterBound +
          5 * parameterBound) := byVolume
    _ <= (twoBlockVolumeConstant denominator * 2 ^ commonExponent) *
        ((twoBlockCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10) := Nat.mul_le_mul volumeBound coefficientBound
    _ = twoBlockOverheadConstant denominator * inputWidth ^ 10 *
        2 ^ commonExponent := by
      unfold twoBlockOverheadConstant
      ring
    _ <= 2 ^ inputWidth / inputWidth := growthBound

/-- The polynomial ledger is eventually absorbed by its strict binary
exponent margin, uniformly over every permitted batch at the fixed rate. -/
theorem eventually_twoBlock_overhead_le
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator) :
    ∀ᶠ blockWidth in Filter.atTop,
      ∀ copies : Nat,
        0 < copies ->
        copies <=
          2 ^ (numerator * (blockWidth + blockWidth) / denominator) ->
        let dimension := twoBlockDimension denominator
        let dimensionPositive :=
          twoBlockDimension_positive denominatorPositive
        let width := fieldWidth blockWidth dimension dimensionPositive
        let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
        let groupBitWidth := FiniteParameters.groupBitWidth 1
        let orderWidth := FiniteParameters.orderWidth copies width
        let routingDepth :=
          FiniteParameters.routingDepth copies 1 dimension width
        CompositionBound.overheadCostBound copies 1 blockWidth dimension width
            blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
            routingDepth <=
          2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth) := by
  let marginDenominator := twoBlockMarginDenominator denominator
  have marginPositive : 0 < marginDenominator := by
    dsimp [marginDenominator]
    unfold twoBlockMarginDenominator
    omega
  have marginProper : marginDenominator - 1 < marginDenominator := by omega
  have growth := Growth.eventually_mul_two_pow_rational_le_shannonScale
    (twoBlockOverheadConstant denominator) 10 (marginDenominator - 1)
    marginDenominator marginPositive marginProper
  obtain ⟨cutoff, pastCutoff⟩ := Filter.eventually_atTop.1 growth
  apply Filter.eventually_atTop.2
  refine ⟨max cutoff 1, fun blockWidth blockLarge copies copiesPositive
    copiesBound => ?_⟩
  have inputPastCutoff : cutoff <= blockWidth + blockWidth := by omega
  have growthBound := pastCutoff (blockWidth + blockWidth) inputPastCutoff
  exact twoBlock_overhead_le_of_growth numerator denominator blockWidth copies
    denominatorPositive rateBelowHalf (by omega) copiesPositive copiesBound
    (by simpa only [marginDenominator] using growthBound)

/-- Constant left after adding the recursive resource bank and the eventually
negligible overhead. -/
def twoBlockMassConstant (denominator : Nat) : Nat :=
  216 * resourceConstant (twoBlockDimension denominator) + 1

/-- Once the explicit overhead has entered the Shannon scale, the complete
canonical finite cost has the same scale. -/
theorem twoBlock_canonicalCostBound_le
    (denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth)
    (overheadBound :
      let dimension := twoBlockDimension denominator
      let dimensionPositive := twoBlockDimension_positive denominatorPositive
      let width := fieldWidth blockWidth dimension dimensionPositive
      let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
      let groupBitWidth := FiniteParameters.groupBitWidth 1
      let orderWidth := FiniteParameters.orderWidth copies width
      let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
      CompositionBound.overheadCostBound copies 1 blockWidth dimension width
          blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
          routingDepth <=
        2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)) :
    FiniteParameters.canonicalCostBound copies 1 blockWidth
        (twoBlockDimension denominator)
        (fieldWidth blockWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive))
        blockWidth (twoBlockResourceBound blockWidth) <=
      twoBlockMassConstant denominator *
        (2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let scale := 2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)
  have resourceBound := twoBlock_resourceTerm_le denominator blockWidth
    denominatorPositive blockPositive
  change ResourceEvaluation.resourceBitCount dimension width *
      twoBlockResourceBound blockWidth +
      CompositionBound.overheadCostBound copies 1 blockWidth dimension width
        blockWidth (FiniteParameters.schedulerDepth copies 1 width)
        (FiniteParameters.groupBitWidth 1)
        (FiniteParameters.orderWidth copies width)
        (FiniteParameters.routingDepth copies 1 dimension width)
        (FiniteParameters.routingDepth copies 1 dimension width) <=
    twoBlockMassConstant denominator * scale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
          twoBlockResourceBound blockWidth +
        CompositionBound.overheadCostBound copies 1 blockWidth dimension width
          blockWidth (FiniteParameters.schedulerDepth copies 1 width)
          (FiniteParameters.groupBitWidth 1)
          (FiniteParameters.orderWidth copies width)
          (FiniteParameters.routingDepth copies 1 dimension width)
          (FiniteParameters.routingDepth copies 1 dimension width) <=
      (216 * resourceConstant dimension) * scale + scale :=
        Nat.add_le_add resourceBound overheadBound
    _ = twoBlockMassConstant denominator * scale := by
      unfold twoBlockMassConstant
      ring

/-- Fully instantiated finite two-block composition.  At this point the only
remaining work for the base case is to bound the displayed explicit natural
cost expression at the Shannon scale. -/
theorem twoBlock_finiteComposition
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (blockLarge : 16 <= blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator))
    (function : ScalarFunction Bool (blockWidth + blockWidth)) :
    booleanMassComplexity function copies <=
      (FiniteParameters.canonicalCostBound copies 1 blockWidth
        (twoBlockDimension denominator)
        (fieldWidth blockWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive))
        blockWidth (twoBlockResourceBound blockWidth) : Nat) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let split := InputSplit.splitFunction function
  have loadBound : requestGroupSize copies 1 * 2 ^ width <
      2 ^ (width * (dimension - 1)) := by
    exact twoBlock_loadBound numerator denominator blockWidth copies
      denominatorPositive rateBelowHalf copiesBound
  have composition := CodeParameters.booleanMassComplexity_le
    copies 1 blockWidth dimension blockWidth
    (twoBlockDimension_atLeastTwo denominatorPositive)
    (by omega : 0 < 1) blockLarge loadBound split
    (twoBlockResourceBound blockWidth) (fun member => ?_)
  · simpa only [split, dimension, dimensionPositive, width,
      InputSplit.booleanMassComplexity_requestFunction_splitFunction] using
      composition
  · have shannon :=
      ShannonSynthesis.booleanMassComplexity_le_replicatedShannon
        blockWidth blockLarge
        (CompositionBound.canonicalResourceFunction
          (fieldWidth_positive blockWidth dimension dimensionPositive)
          (fieldWidth_packingFits blockWidth dimension dimensionPositive)
          split member)
        1
    simpa [twoBlockResourceBound] using shannon

/-- The actual two-block mass-production bound, before padding arbitrary
input lengths to the next even length. -/
theorem eventually_twoBlock_mass_bound
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator) :
    ∀ᶠ blockWidth in Filter.atTop,
      ∀ (function : ScalarFunction Bool (blockWidth + blockWidth))
        (copies : Nat),
        0 < copies ->
        copies <=
          2 ^ (numerator * (blockWidth + blockWidth) / denominator) ->
        booleanMassComplexity function copies <=
          (twoBlockMassConstant denominator *
            (2 ^ (blockWidth + blockWidth) /
              (blockWidth + blockWidth)) : Nat) := by
  filter_upwards [eventually_twoBlock_overhead_le numerator denominator
      denominatorPositive rateBelowHalf,
    Filter.eventually_ge_atTop 16] with blockWidth overhead blockLarge
  intro function copies copiesPositive copiesBound
  have finite := twoBlock_finiteComposition numerator denominator blockWidth
    copies denominatorPositive rateBelowHalf blockLarge copiesBound function
  have canonical := twoBlock_canonicalCostBound_le denominator blockWidth copies
    denominatorPositive (by omega) (overhead copies copiesPositive copiesBound)
  exact finite.trans (by exact_mod_cast canonical)

/-! ## Padding arbitrary lengths to the next even length -/

/-- Ceiling of half the input width, used as the common padded block width. -/
def halfCeil (inputWidth : Nat) : Nat :=
  inputWidth ⌈/⌉ 2

/-- The least even width represented as two copies of `halfCeil`. -/
def nextEvenWidth (inputWidth : Nat) : Nat :=
  halfCeil inputWidth + halfCeil inputWidth

theorem inputWidth_le_nextEvenWidth (inputWidth : Nat) :
    inputWidth <= nextEvenWidth inputWidth := by
  have capacity : inputWidth <= 2 * (inputWidth ⌈/⌉ 2) :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < 2)).mp le_rfl
  unfold nextEvenWidth halfCeil
  omega

theorem nextEvenWidth_le_add_two (inputWidth : Nat) :
    nextEvenWidth inputWidth <= inputWidth + 2 := by
  have ceiling := CodeParameters.ceilDiv_le_div_add_one inputWidth 2
    (by omega)
  have floor := Nat.mul_div_le inputWidth 2
  unfold nextEvenWidth halfCeil
  omega

theorem shannonScale_nextEvenWidth_le
    (inputWidth : Nat)
    (inputPositive : 0 < inputWidth) :
    2 ^ nextEvenWidth inputWidth / nextEvenWidth inputWidth <=
      8 * (2 ^ inputWidth / inputWidth) := by
  have fits := inputWidth_le_nextEvenWidth inputWidth
  have upper := nextEvenWidth_le_add_two inputWidth
  have powerBound : 2 ^ nextEvenWidth inputWidth <= 4 * 2 ^ inputWidth := by
    calc
      2 ^ nextEvenWidth inputWidth <= 2 ^ (inputWidth + 2) :=
        Nat.pow_le_pow_right (by omega) upper
      _ = 4 * 2 ^ inputWidth := by
        rw [Nat.pow_add]
        norm_num
        ring
  have inputFitsPower : inputWidth <= 2 ^ inputWidth := by
    exact (by omega : inputWidth <= 2 * inputWidth).trans
      (Nat.mul_le_pow (by decide : 2 ≠ 1) inputWidth)
  calc
    2 ^ nextEvenWidth inputWidth / nextEvenWidth inputWidth <=
        2 ^ nextEvenWidth inputWidth / inputWidth :=
      Nat.div_le_div_left fits inputPositive
    _ <= (4 * 2 ^ inputWidth) / inputWidth :=
      Nat.div_le_div_right powerBound
    _ <= 2 * 4 * (2 ^ inputWidth / inputWidth) :=
      Growth.mul_div_le_two_mul_mul_div 4 (2 ^ inputWidth) inputWidth
        inputPositive inputFitsPower
    _ = 8 * (2 ^ inputWidth / inputWidth) := by ring

/-- The complete two-block base case `P₁`: every fixed rational rate below
one half has eventual mass production for arbitrary positive input lengths. -/
theorem massProducesAt_of_rateBelowHalf
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator) :
    MassProducesAt numerator denominator := by
  obtain ⟨blockCutoff, blockBound⟩ := Filter.eventually_atTop.1
    (eventually_twoBlock_mass_bound numerator denominator denominatorPositive
      rateBelowHalf)
  refine ⟨8 * twoBlockMassConstant denominator,
    max 1 (2 * blockCutoff), ?_⟩
  intro inputWidth inputPositive pastCutoff function copies copiesPositive
    copiesBound
  let blockWidth := halfCeil inputWidth
  let paddedWidth := nextEvenWidth inputWidth
  have fits : inputWidth <= paddedWidth := inputWidth_le_nextEvenWidth inputWidth
  have paddedWidthEq : paddedWidth = blockWidth + blockWidth := by rfl
  have blockLarge : blockCutoff <= blockWidth := by
    have inputLarge : 2 * blockCutoff <= inputWidth :=
      (le_max_right 1 (2 * blockCutoff)).trans pastCutoff
    have capacity : inputWidth <= 2 * blockWidth := by
      dsimp [blockWidth, halfCeil]
      exact (ceilDiv_le_iff_le_mul (by omega : 0 < 2)).mp le_rfl
    omega
  have paddedCopiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator) := by
    have widened := copiesBound.trans
      (rationalCopyBudget_mono_inputs
        (numerator := numerator) (denominator := denominator) fits)
    simpa [rationalCopyBudget, paddedWidthEq] using widened
  let paddedFunction := InputSplit.paddedFunction fits function
  have paddedMass := blockBound blockWidth blockLarge paddedFunction copies
    copiesPositive paddedCopiesBound
  have transport := InputSplit.booleanMassComplexity_le_paddedFunction
    inputPositive fits function copies
  have scaleBound := shannonScale_nextEvenWidth_le inputWidth inputPositive
  calc
    booleanMassComplexity function copies <=
        booleanMassComplexity paddedFunction copies := transport
    _ <= (twoBlockMassConstant denominator *
          (2 ^ (blockWidth + blockWidth) /
            (blockWidth + blockWidth)) : Nat) := paddedMass
    _ = (twoBlockMassConstant denominator *
          (2 ^ paddedWidth / paddedWidth) : Nat) := by
      rw [paddedWidthEq]
    _ <= ((8 * twoBlockMassConstant denominator) *
          (2 ^ inputWidth / inputWidth) : Nat) := by
      exact_mod_cast (calc
        twoBlockMassConstant denominator *
            (2 ^ paddedWidth / paddedWidth) <=
          twoBlockMassConstant denominator *
            (8 * (2 ^ inputWidth / inputWidth)) := by gcongr
        _ = (8 * twoBlockMassConstant denominator) *
            (2 ^ inputWidth / inputWidth) := by ring)

end EqualBlock
end MassProduction
end Algebraic
