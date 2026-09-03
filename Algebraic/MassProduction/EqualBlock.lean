import Algebraic.MassProduction.CodeParameters
import Algebraic.MassProduction.Growth
import Algebraic.MassProduction.InputSplit
import Algebraic.MassProduction.OverheadBound

/-!
# Exact parameters for the equal-block induction

This module begins the quantitative specialization of the finite composition
theorem.  Rates remain natural fractions, block lengths remain integral, and
all floor and ceiling operations are explicit.
-/

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters
open GroupedScheduler
open LineEnumeration
open Sorting

/-- A concrete recovery-code dimension for the two-block base case.  The
factor three leaves a strict direction-capacity margin at every rational rate
strictly below one half. -/
def twoBlockDimension (denominator : Nat) : Nat :=
  3 * denominator

theorem twoBlockDimension_positive
    (denominatorPositive : 0 < denominator) :
    0 < twoBlockDimension denominator := by
  unfold twoBlockDimension
  omega

theorem twoBlockDimension_atLeastTwo
    (denominatorPositive : 0 < denominator) :
    2 <= twoBlockDimension denominator := by
  unfold twoBlockDimension
  omega

/-- Exact exponent inequality behind the two-block scheduler.  It uses only
the information-rate lower bound forced by successful prefix packing. -/
theorem twoBlock_loadExponent
    (numerator denominator prefixWidth width : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (widthPositive : 0 < width)
    (packingRate : prefixWidth <=
      (twoBlockDimension denominator + 1) * width) :
    numerator * (prefixWidth + prefixWidth) / denominator + width <
      width * (twoBlockDimension denominator - 1) := by
  let dimension := twoBlockDimension denominator
  let exponent := numerator * (prefixWidth + prefixWidth) / denominator
  have rateBound : 2 * numerator <= denominator - 1 := by omega
  have divided : exponent * denominator <=
      2 * numerator * prefixWidth := by
    calc
      exponent * denominator <=
          numerator * (prefixWidth + prefixWidth) := by
        exact Nat.div_mul_le_self _ _
      _ = 2 * numerator * prefixWidth := by ring
  have coefficientGap :
      (denominator - 1) * (dimension + 1) <
        denominator * (dimension - 2) := by
    have denominatorEq : denominator = (denominator - 1) + 1 := by omega
    have dimensionMinus : dimension - 2 =
        3 * (denominator - 1) + 1 := by
      dsimp [dimension]
      unfold twoBlockDimension
      omega
    have dimensionPlus : dimension + 1 =
        3 * (denominator - 1) + 4 := by
      dsimp [dimension]
      unfold twoBlockDimension
      omega
    rw [denominatorEq, dimensionMinus, dimensionPlus]
    simp only [Nat.add_sub_cancel]
    nlinarith
  have scaledExponent :
      exponent * (denominator * (dimension + 1)) <
        (width * (dimension - 2)) *
          (denominator * (dimension + 1)) := by
    calc
      exponent * (denominator * (dimension + 1)) =
          exponent * denominator * (dimension + 1) := by ring
      _ <= (2 * numerator * prefixWidth) * (dimension + 1) := by
        gcongr
      _ <= ((denominator - 1) * prefixWidth) * (dimension + 1) := by
        gcongr
      _ <= ((denominator - 1) * ((dimension + 1) * width)) *
          (dimension + 1) := by
        gcongr
      _ = ((denominator - 1) * (dimension + 1)) *
          ((dimension + 1) * width) := by ring
      _ < (denominator * (dimension - 2)) *
          ((dimension + 1) * width) := by
        exact Nat.mul_lt_mul_of_pos_right coefficientGap (by positivity)
      _ = (width * (dimension - 2)) *
          (denominator * (dimension + 1)) := by ring
  have exponentSmall : exponent < width * (dimension - 2) :=
    Nat.lt_of_mul_lt_mul_right scaledExponent
  change exponent + width < width * (dimension - 1)
  calc
    exponent + width < width * (dimension - 2) + width :=
      Nat.add_lt_add_right exponentSmall width
    _ = width * (dimension - 1) := by
      have dimensionAtLeast : 2 <= dimension := by
        dsimp [dimension]
        exact twoBlockDimension_atLeastTwo denominatorPositive
      have dimensionStep : dimension - 1 = (dimension - 2) + 1 := by omega
      rw [dimensionStep, Nat.mul_add, Nat.mul_one]

/-- For one request group, every allowed two-block batch has enough
projective directions for the least admissible field selected by
`CodeParameters`. -/
theorem twoBlock_loadBound
    (numerator denominator prefixWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (copiesBound : copies <=
      2 ^ (numerator * (prefixWidth + prefixWidth) / denominator)) :
    requestGroupSize copies 1 *
        2 ^ fieldWidth prefixWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive) <
      2 ^ (fieldWidth prefixWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive) *
        (twoBlockDimension denominator - 1)) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth prefixWidth dimension dimensionPositive
  have widthPositive := fieldWidth_positive prefixWidth dimension
    dimensionPositive
  have packingRate :=
    prefixWidth_le_succ_dimension_mul_fieldWidth prefixWidth dimension
      dimensionPositive
  have exponentSmall := twoBlock_loadExponent numerator denominator
    prefixWidth width denominatorPositive rateBelowHalf widthPositive
    packingRate
  have powerBound :
      2 ^ (numerator * (prefixWidth + prefixWidth) / denominator + width) <
        2 ^ (width * (dimension - 1)) :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 exponentSmall
  calc
    requestGroupSize copies 1 * 2 ^ width = copies * 2 ^ width := by
      simp [requestGroupSize]
    _ <= 2 ^ (numerator * (prefixWidth + prefixWidth) / denominator) *
        2 ^ width := Nat.mul_le_mul_right _ copiesBound
    _ = 2 ^ (numerator * (prefixWidth + prefixWidth) / denominator +
        width) := (Nat.pow_add _ _ _).symm
    _ < 2 ^ (width * (dimension - 1)) := powerBound

/-- The concrete Shannon bound supplied to every one-copy resource circuit in
the two-block base case. -/
def twoBlockResourceBound (blockWidth : Nat) : Nat :=
  27 * 2 ^ blockWidth / blockWidth

/-- The recursive resource bank already lies at the sharp Shannon scale for
the complete two-block input. -/
theorem twoBlock_resourceTerm_le
    (denominator blockWidth : Nat)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth) :
    ResourceEvaluation.resourceBitCount
          (twoBlockDimension denominator)
          (fieldWidth blockWidth (twoBlockDimension denominator)
            (twoBlockDimension_positive denominatorPositive)) *
        twoBlockResourceBound blockWidth <=
      (216 * resourceConstant (twoBlockDimension denominator)) *
        (2 ^ (blockWidth + blockWidth) /
          (blockWidth + blockWidth)) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let resourceScale := 2 ^ (blockWidth + blockWidth) /
    (blockWidth + blockWidth)
  have countBound := resourceBitCount_le blockWidth dimension dimensionPositive
  have twiceFits : 2 * blockWidth <= 2 ^ (blockWidth + blockWidth) := by
    calc
      2 * blockWidth <= 2 ^ blockWidth :=
        Nat.mul_le_pow (by decide : 2 ≠ 1) blockWidth
      _ <= 2 ^ (blockWidth + blockWidth) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have quotientBound := Growth.div_le_four_mul_double_div
    (2 ^ (blockWidth + blockWidth)) blockWidth blockPositive twiceFits
  have quotientBound' :
      2 ^ (blockWidth + blockWidth) / blockWidth <= 4 * resourceScale := by
    simpa only [resourceScale, two_mul] using quotientBound
  have blockFits : blockWidth <= 2 ^ (blockWidth + blockWidth) :=
    (by omega : blockWidth <= 2 * blockWidth).trans twiceFits
  change ResourceEvaluation.resourceBitCount dimension width *
      (27 * 2 ^ blockWidth / blockWidth) <=
    (216 * resourceConstant dimension) * resourceScale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
        (27 * 2 ^ blockWidth / blockWidth) <=
      (resourceConstant dimension * 2 ^ blockWidth) *
        (27 * 2 ^ blockWidth / blockWidth) := by
      gcongr
    _ <= ((resourceConstant dimension * 2 ^ blockWidth) *
        (27 * 2 ^ blockWidth)) / blockWidth :=
      Nat.mul_div_le_mul_div_assoc
        (resourceConstant dimension * 2 ^ blockWidth)
        (27 * 2 ^ blockWidth) blockWidth
    _ = (27 * resourceConstant dimension *
        2 ^ (blockWidth + blockWidth)) / blockWidth := by
      rw [Nat.pow_add]
      apply congrArg (fun value => value / blockWidth)
      ring
    _ <= 2 * (27 * resourceConstant dimension) *
        (2 ^ (blockWidth + blockWidth) / blockWidth) := by
      exact Growth.mul_div_le_two_mul_mul_div
        (27 * resourceConstant dimension)
        (2 ^ (blockWidth + blockWidth)) blockWidth blockPositive blockFits
    _ <= 2 * (27 * resourceConstant dimension) *
        (4 * resourceScale) := by gcongr
    _ = (216 * resourceConstant dimension) * resourceScale := by ring

/-- Linear upper bound for the selected extension-field bit width in the
two-block construction. -/
def twoBlockWidthBound (denominator blockWidth : Nat) : Nat :=
  blockWidth + 4 * twoBlockDimension denominator + 3

/-- Shared linear bound for every bit width and sorting depth occurring in
the canonical two-block ledger. -/
def twoBlockParameterBound (denominator blockWidth : Nat) : Nat :=
  let dimension := twoBlockDimension denominator
  let widthBound := twoBlockWidthBound denominator blockWidth
  (blockWidth + blockWidth) + widthBound + dimension * widthBound + 2

theorem twoBlock_fieldWidth_le_widthBound
    (denominator blockWidth : Nat)
    (denominatorPositive : 0 < denominator) :
    fieldWidth blockWidth (twoBlockDimension denominator)
        (twoBlockDimension_positive denominatorPositive) <=
      twoBlockWidthBound denominator blockWidth := by
  have selected := fieldWidth_le_quotient_add blockWidth
    (twoBlockDimension denominator)
    (twoBlockDimension_positive denominatorPositive)
  unfold twoBlockWidthBound
  exact selected.trans (by
    have := Nat.div_le_self blockWidth (twoBlockDimension denominator)
    omega)

/-- All coefficient parameters in the canonical two-block ledger lie below
`twoBlockParameterBound`. -/
theorem twoBlock_parameters_bounded
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator)) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
    let groupBitWidth := FiniteParameters.groupBitWidth 1
    let orderWidth := FiniteParameters.orderWidth copies width
    let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
    let bound := twoBlockParameterBound denominator blockWidth
    dimension <= bound ∧
      width <= bound ∧
      schedulerDepth <= bound ∧
      blockWidth <= bound ∧
      IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
        bound ∧
      blockWidth <= bound ∧
      orderWidth + 1 <= bound ∧
      routingDepth <= bound := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let widthBound := twoBlockWidthBound denominator blockWidth
  let inputWidth := blockWidth + blockWidth
  let exponent := numerator * inputWidth / denominator
  let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
  let groupBitWidth := FiniteParameters.groupBitWidth 1
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
  let bound := twoBlockParameterBound denominator blockWidth
  have dimensionPositive' : 0 < dimension := dimensionPositive
  have widthSelected : width <= widthBound := by
    exact twoBlock_fieldWidth_le_widthBound denominator blockWidth
      denominatorPositive
  have numeratorBelow : numerator <= denominator := by omega
  have exponentLeInput : exponent <= inputWidth := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right inputWidth numeratorBelow
  have copiesCoarse : copies <= 2 ^ inputWidth :=
    copiesBound.trans (Nat.pow_le_pow_right (by omega) exponentLeInput)
  have scalarBound : nonzeroScalarCount width <= 2 ^ width := by
    rw [nonzeroScalarCount_eq_two_pow_sub_one
      (fieldWidth_positive blockWidth dimension dimensionPositive)]
    exact Nat.sub_le _ _
  have widthPowerBound : 2 ^ width <= 2 ^ widthBound :=
    Nat.pow_le_pow_right (by omega) widthSelected
  have incidenceBound :
      FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound) := by
    unfold FiniteParameters.incidenceCount
    calc
      copies * nonzeroScalarCount width <= 2 ^ inputWidth * 2 ^ width :=
        Nat.mul_le_mul copiesCoarse scalarBound
      _ <= 2 ^ inputWidth * 2 ^ widthBound := by gcongr
      _ = 2 ^ (inputWidth + widthBound) :=
        (Nat.pow_add _ _ _).symm
  have schedulerRecordBound :
      requestGroupSize copies 1 * nonzeroScalarCount width <=
        2 ^ (inputWidth + widthBound) := by
    simpa [requestGroupSize, FiniteParameters.incidenceCount] using
      incidenceBound
  have schedulerDepthBound : schedulerDepth <= inputWidth + widthBound := by
    unfold schedulerDepth FiniteParameters.schedulerDepth
    exact FiniteParameters.binaryDepth_le _ _ schedulerRecordBound
  have orderDepthBound : orderWidth <= inputWidth + widthBound := by
    unfold orderWidth FiniteParameters.orderWidth
    exact FiniteParameters.binaryDepth_le _ _ incidenceBound
  have slotBound : FiniteParameters.resourceSlotCount 1 dimension width <=
      2 ^ (dimension * widthBound) := by
    unfold FiniteParameters.resourceSlotCount
      FiniteParameters.groupBitWidth FiniteParameters.binaryDepth
    simp only [Nat.clog_one_right, zero_add]
    exact Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left dimension widthSelected)
  let routingExponent := inputWidth + widthBound + dimension * widthBound + 1
  have routingRecordBound :
      FiniteParameters.routingRecords copies 1 dimension width <=
        2 ^ routingExponent := by
    have incidenceRaised : FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      incidenceBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have slotsRaised : FiniteParameters.resourceSlotCount 1 dimension width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      slotBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    unfold FiniteParameters.routingRecords
    calc
      FiniteParameters.incidenceCount copies width +
          FiniteParameters.resourceSlotCount 1 dimension width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) +
          2 ^ (inputWidth + widthBound + dimension * widthBound) :=
        Nat.add_le_add incidenceRaised slotsRaised
      _ = 2 ^ routingExponent := by
        rw [show routingExponent =
          (inputWidth + widthBound + dimension * widthBound) + 1 by rfl,
          Nat.pow_succ]
        ring
  have routingDepthBound : routingDepth <= routingExponent := by
    unfold routingDepth FiniteParameters.routingDepth
    exact FiniteParameters.binaryDepth_le _ _ routingRecordBound
  have boundEq : bound =
      inputWidth + widthBound + dimension * widthBound + 2 := by rfl
  have dimensionLeWidthBound : dimension <= widthBound := by
    dsimp [widthBound]
    unfold twoBlockWidthBound
    omega
  have inputLeBound : inputWidth <= bound := by
    rw [boundEq]
    omega
  have widthBoundLeBound : widthBound <= bound := by
    rw [boundEq]
    omega
  have productLeBound : dimension * widthBound <= bound := by
    rw [boundEq]
    omega
  have routingExponentLeBound : routingExponent <= bound := by
    rw [boundEq]
    dsimp [routingExponent]
    omega
  have schedulerBound : schedulerDepth <= bound :=
    schedulerDepthBound.trans (by rw [boundEq]; omega)
  have blockBound : blockWidth <= bound := by
    exact (by omega : blockWidth <= inputWidth).trans inputLeBound
  have keyBound : IncidenceRouting.incidenceKeyWidth
      groupBitWidth dimension width <= bound := by
    have productBound : dimension * width <= dimension * widthBound :=
      Nat.mul_le_mul_left dimension widthSelected
    have productPlusBound : dimension * width + 1 <= bound :=
      (Nat.add_le_add_right productBound 1).trans (by rw [boundEq]; omega)
    dsimp [groupBitWidth, FiniteParameters.groupBitWidth,
      FiniteParameters.binaryDepth, IncidenceRouting.incidenceKeyWidth]
    simpa using productPlusBound
  have orderBound : orderWidth + 1 <= bound :=
    (Nat.add_le_add_right orderDepthBound 1).trans (by rw [boundEq]; omega)
  have localBounds :
      dimension <= bound ∧
        width <= bound ∧
        schedulerDepth <= bound ∧
        blockWidth <= bound ∧
        IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
          bound ∧
        blockWidth <= bound ∧
        orderWidth + 1 <= bound ∧
        routingDepth <= bound :=
    ⟨dimensionLeWidthBound.trans widthBoundLeBound,
      widthSelected.trans widthBoundLeBound, schedulerBound, blockBound,
      keyBound, blockBound, orderBound,
      routingDepthBound.trans routingExponentLeBound⟩
  simpa only [dimension, dimensionPositive, width, schedulerDepth,
    groupBitWidth, orderWidth, routingDepth, bound] using localBounds

/-- The exact canonical record volume in the two-block case has the three
expected contributions: quadratic scheduling, incidences, and resource
slots. -/
theorem twoBlock_overheadVolume_le
    (denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (copiesPositive : 0 < copies) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    OverheadBound.overheadVolume copies 1 width
        (FiniteParameters.schedulerDepth copies 1 width)
        (FiniteParameters.routingDepth copies 1 dimension width) <=
      2 * copies * copies * 2 ^ width +
        7 * copies * 2 ^ width +
        4 * 2 ^ (dimension * width) := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let scalarCount := nonzeroScalarCount width
  let schedulerRecords := copies * scalarCount
  let routingRecords := FiniteParameters.routingRecords copies 1 dimension width
  have widthPositive := fieldWidth_positive blockWidth dimension
    dimensionPositive
  have scalarPositive : 0 < scalarCount := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    have : 1 < 2 ^ width := by
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 widthPositive
    exact Nat.sub_pos_of_lt this
  have schedulerRecordsPositive : 0 < schedulerRecords :=
    Nat.mul_pos copiesPositive scalarPositive
  have schedulerNetwork :
      networkRecords (FiniteParameters.schedulerDepth copies 1 width) <=
        2 * (copies * scalarCount) := by
    exact Nat.le_of_lt (by
      simpa [FiniteParameters.schedulerDepth, requestGroupSize,
        schedulerRecords] using
        FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          schedulerRecords schedulerRecordsPositive)
  have scalarBound : scalarCount <= 2 ^ width := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    exact Nat.sub_le _ _
  have slotEquality :
      FiniteParameters.resourceSlotCount 1 dimension width =
        2 ^ (dimension * width) := by
    unfold FiniteParameters.resourceSlotCount
      FiniteParameters.groupBitWidth FiniteParameters.binaryDepth
    simp
  have routingRecordsPositive : 0 < routingRecords := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords
    rw [slotEquality]
    positivity
  have routingNetwork :
      networkRecords
          (FiniteParameters.routingDepth copies 1 dimension width) <=
        2 * routingRecords := by
    exact Nat.le_of_lt (by
      simpa [FiniteParameters.routingDepth, routingRecords] using
        FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          routingRecords routingRecordsPositive)
  have routingRecordsBound : routingRecords <=
      copies * 2 ^ width + 2 ^ (dimension * width) := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords FiniteParameters.incidenceCount
    rw [slotEquality]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left copies scalarBound) _
  unfold OverheadBound.overheadVolume
  simp only [requestGroupSize, ceilDiv_one, one_mul]
  calc
    copies *
          (networkRecords (FiniteParameters.schedulerDepth copies 1 width) +
            2 ^ width) +
        2 * (copies * 2 ^ width) +
        2 * networkRecords
          (FiniteParameters.routingDepth copies 1 dimension width) <=
      copies * (2 * (copies * scalarCount) + 2 ^ width) +
        2 * (copies * 2 ^ width) + 2 * (2 * routingRecords) := by
      gcongr
    _ <= copies * (2 * (copies * 2 ^ width) + 2 ^ width) +
        2 * (copies * 2 ^ width) +
        2 * (2 * (copies * 2 ^ width +
          2 ^ (dimension * width))) := by
      gcongr
    _ = 2 * copies * copies * 2 ^ width +
        7 * copies * 2 ^ width +
        4 * 2 ^ (dimension * width) := by ring

/-- Denominator used for the common strict subunit exponent in the two-block
overhead bound. -/
def twoBlockMarginDenominator (denominator : Nat) : Nat :=
  6 * denominator

/-- Fixed multiplicative loss in the field-cardinality upper bound. -/
def twoBlockFieldConstant (denominator : Nat) : Nat :=
  2 ^ (4 * twoBlockDimension denominator + 3)

/-- Fixed multiplicative loss after raising the field cardinality to the code
dimension. -/
def twoBlockSlotConstant (denominator : Nat) : Nat :=
  2 ^ (twoBlockDimension denominator *
    (4 * twoBlockDimension denominator + 3))

/-- Fixed coefficient for the complete canonical record-volume bound. -/
def twoBlockVolumeConstant (denominator : Nat) : Nat :=
  9 * twoBlockFieldConstant denominator +
    4 * twoBlockSlotConstant denominator

/-- Slope relating every concrete ledger width to the full two-block input
length. -/
def twoBlockParameterSlope (denominator : Nat) : Nat :=
  let dimension := twoBlockDimension denominator
  3 + (dimension + 1) * (4 * dimension + 4)

/-- Constant coefficient of the degree-ten common ledger envelope. -/
def twoBlockCoefficientConstant (denominator : Nat) : Nat :=
  let slope := twoBlockParameterSlope denominator
  1000000 * (slope + 1) ^ 10 + 5 * slope

theorem twoBlock_parameterBound_le
    (denominator blockWidth : Nat) :
    twoBlockParameterBound denominator blockWidth <=
      twoBlockParameterSlope denominator *
        (blockWidth + blockWidth + 1) := by
  let dimension := twoBlockDimension denominator
  let inputWidth := blockWidth + blockWidth
  let widthBound := twoBlockWidthBound denominator blockWidth
  let slope := twoBlockParameterSlope denominator
  have blockLeInput : blockWidth <= inputWidth := by
    dsimp [inputWidth]
    omega
  have widthLinear : widthBound <=
      (4 * dimension + 4) * (inputWidth + 1) := by
    dsimp [widthBound]
    unfold twoBlockWidthBound
    change blockWidth + 4 * dimension + 3 <= _
    ring_nf
    omega
  change inputWidth + widthBound + dimension * widthBound + 2 <=
    slope * (inputWidth + 1)
  calc
    inputWidth + widthBound + dimension * widthBound + 2 =
        inputWidth + (dimension + 1) * widthBound + 2 := by ring
    _ <= inputWidth +
        (dimension + 1) * ((4 * dimension + 4) * (inputWidth + 1)) +
          2 := by gcongr
    _ <= slope * (inputWidth + 1) := by
      rw [show slope =
        3 + (dimension + 1) * (4 * dimension + 4) by rfl]
      ring_nf
      omega

/-- The common coefficient in the two-block ledger is a fixed constant times
a degree-ten polynomial in the complete input length. -/
theorem twoBlock_coefficient_le
    (denominator blockWidth : Nat) :
    let parameterBound := twoBlockParameterBound denominator blockWidth
    let inputWidth := blockWidth + blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      twoBlockCoefficientConstant denominator * (inputWidth + 1) ^ 10 := by
  dsimp only
  let parameterBound := twoBlockParameterBound denominator blockWidth
  let inputWidth := blockWidth + blockWidth
  let slope := twoBlockParameterSlope denominator
  have parameterLinear : parameterBound <= slope * (inputWidth + 1) :=
    twoBlock_parameterBound_le denominator blockWidth
  have successorLinear : parameterBound + 1 <=
      (slope + 1) * (inputWidth + 1) := by
    calc
      parameterBound + 1 <= slope * (inputWidth + 1) + 1 := by omega
      _ <= slope * (inputWidth + 1) + (inputWidth + 1) := by omega
      _ = (slope + 1) * (inputWidth + 1) := by ring
  have envelope := OverheadBound.coefficientEnvelope_le parameterBound
  have envelopePolynomial : OverheadBound.coefficientEnvelope parameterBound <=
      (1000000 * (slope + 1) ^ 10) * (inputWidth + 1) ^ 10 := by
    calc
      OverheadBound.coefficientEnvelope parameterBound <=
          1000000 * (parameterBound + 1) ^ 10 := envelope
      _ <= 1000000 * ((slope + 1) * (inputWidth + 1)) ^ 10 := by
        gcongr
      _ = (1000000 * (slope + 1) ^ 10) *
          (inputWidth + 1) ^ 10 := by
        rw [mul_pow]
        ring
  have inputPower : inputWidth + 1 <= (inputWidth + 1) ^ 10 := by
    calc
      inputWidth + 1 = (inputWidth + 1) * 1 := by omega
      _ <= (inputWidth + 1) * (inputWidth + 1) ^ 9 := by
        gcongr
        exact Nat.one_le_pow 9 (inputWidth + 1) (by omega)
      _ = (inputWidth + 1) ^ 10 := by
        rw [show 10 = 1 + 9 by omega, pow_add, pow_one]
  have linearPolynomial : 5 * parameterBound <=
      (5 * slope) * (inputWidth + 1) ^ 10 := by
    calc
      5 * parameterBound <= 5 * (slope * (inputWidth + 1)) := by gcongr
      _ <= 5 * (slope * (inputWidth + 1) ^ 10) := by gcongr
      _ = (5 * slope) * (inputWidth + 1) ^ 10 := by ring
  calc
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
        (1000000 * (slope + 1) ^ 10) * (inputWidth + 1) ^ 10 +
          (5 * slope) * (inputWidth + 1) ^ 10 :=
      Nat.add_le_add envelopePolynomial linearPolynomial
    _ = twoBlockCoefficientConstant denominator *
        (inputWidth + 1) ^ 10 := by
      unfold twoBlockCoefficientConstant
      dsimp [slope]
      ring

theorem twoBlock_coefficient_le_monomial
    (denominator blockWidth : Nat)
    (blockPositive : 0 < blockWidth) :
    let parameterBound := twoBlockParameterBound denominator blockWidth
    let inputWidth := blockWidth + blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      (twoBlockCoefficientConstant denominator * 2 ^ 10) *
        inputWidth ^ 10 := by
  dsimp only
  let inputWidth := blockWidth + blockWidth
  have inputPositive : 0 < inputWidth := by dsimp [inputWidth]; omega
  have successorBound : inputWidth + 1 <= 2 * inputWidth := by omega
  exact (twoBlock_coefficient_le denominator blockWidth).trans <| by
    calc
      twoBlockCoefficientConstant denominator * (inputWidth + 1) ^ 10 <=
          twoBlockCoefficientConstant denominator * (2 * inputWidth) ^ 10 := by
        gcongr
      _ = (twoBlockCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10 := by
        rw [mul_pow]
        ring

/-- The common overhead exponent is strictly below one and dominates the
quadratic scheduler, incidence, and resource-slot exponents. -/
theorem twoBlock_overheadVolume_exponential_le
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator)) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
    let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
    let inputWidth := blockWidth + blockWidth
    let marginDenominator := twoBlockMarginDenominator denominator
    OverheadBound.overheadVolume copies 1 width schedulerDepth routingDepth <=
      twoBlockVolumeConstant denominator *
        2 ^ ((marginDenominator - 1) * inputWidth / marginDenominator) := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
  let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
  let inputWidth := blockWidth + blockWidth
  let marginDenominator := twoBlockMarginDenominator denominator
  let requestExponent := numerator * inputWidth / denominator
  let fieldExponent := inputWidth / marginDenominator
  let commonExponent := (marginDenominator - 1) * inputWidth /
    marginDenominator
  let fieldConstant := twoBlockFieldConstant denominator
  let slotConstant := twoBlockSlotConstant denominator
  have marginPositive : 0 < marginDenominator := by
    dsimp [marginDenominator]
    unfold twoBlockMarginDenominator
    omega
  have dimensionPositive' : 0 < dimension := dimensionPositive
  have marginEq : marginDenominator = 6 * denominator := by
    dsimp [marginDenominator]
    rfl
  have dimensionEq : dimension = 3 * denominator := by
    dsimp [dimension]
    rfl
  have requestRescale : requestExponent =
      6 * numerator * inputWidth / marginDenominator := by
    dsimp [requestExponent]
    rw [marginEq]
    have rescaled := Nat.mul_div_mul_left (m := 6)
      (numerator * inputWidth) denominator (by omega)
    rw [show 6 * numerator * inputWidth =
      6 * (numerator * inputWidth) by ring]
    exact rescaled.symm
  have fieldRescale : blockWidth / dimension = fieldExponent := by
    dsimp [fieldExponent, inputWidth]
    rw [marginEq, dimensionEq]
    have rescaled := Nat.mul_div_mul_left (m := 2) blockWidth
      (3 * denominator) (by omega)
    have denominatorSum : 6 * denominator =
        3 * denominator + 3 * denominator := by omega
    rw [denominatorSum]
    simpa only [two_mul] using rescaled.symm
  have fieldBound : 2 ^ width <=
      fieldConstant * 2 ^ fieldExponent := by
    have selected := fieldCard_le blockWidth dimension dimensionPositive
    dsimp [fieldConstant]
    rw [fieldRescale] at selected
    exact selected
  have slotBound : 2 ^ (dimension * width) <=
      slotConstant * 2 ^ blockWidth := by
    have selected := fieldCard_pow_dimension_le blockWidth dimension
      dimensionPositive
    exact selected
  have schedulerExponentBound :
      requestExponent + requestExponent + fieldExponent <= commonExponent := by
    have twiceFloored : 2 * requestExponent <=
        (12 * numerator * inputWidth) / marginDenominator := by
      rw [requestRescale]
      calc
        2 * (6 * numerator * inputWidth / marginDenominator) <=
            2 * (6 * numerator * inputWidth) / marginDenominator :=
          Nat.mul_div_le_mul_div_assoc 2
            (6 * numerator * inputWidth) marginDenominator
        _ = (12 * numerator * inputWidth) / marginDenominator := by
          apply congrArg (fun value => value / marginDenominator)
          ring
    have combined :
        (12 * numerator * inputWidth) / marginDenominator +
            inputWidth / marginDenominator <=
          ((12 * numerator + 1) * inputWidth) / marginDenominator := by
      calc
        (12 * numerator * inputWidth) / marginDenominator +
            inputWidth / marginDenominator <=
          (12 * numerator * inputWidth + inputWidth) /
            marginDenominator :=
          Growth.div_add_div_le _ _ _ marginPositive
        _ = ((12 * numerator + 1) * inputWidth) /
            marginDenominator := by
          apply congrArg (fun value => value / marginDenominator)
          ring
    have coefficientBound : 12 * numerator + 1 <= marginDenominator - 1 := by
      rw [marginEq]
      omega
    calc
      requestExponent + requestExponent + fieldExponent =
          2 * requestExponent + fieldExponent := by omega
      _ <= (12 * numerator * inputWidth) / marginDenominator +
          fieldExponent := Nat.add_le_add_right twiceFloored _
      _ <= ((12 * numerator + 1) * inputWidth) /
          marginDenominator := by
        dsimp [fieldExponent]
        exact combined
      _ <= commonExponent := by
        dsimp [commonExponent]
        exact Nat.div_le_div_right
          (Nat.mul_le_mul_right inputWidth coefficientBound)
  have incidenceExponentBound :
      requestExponent + fieldExponent <= commonExponent := by
    calc
      requestExponent + fieldExponent =
          0 + (requestExponent + fieldExponent) := by omega
      _ <= requestExponent + (requestExponent + fieldExponent) :=
        Nat.add_le_add_right (Nat.zero_le requestExponent) _
      _ = requestExponent + requestExponent + fieldExponent := by omega
      _ <= commonExponent := schedulerExponentBound
  have slotExponentBound : blockWidth <= commonExponent := by
    apply (Nat.le_div_iff_mul_le marginPositive).2
    dsimp [commonExponent, inputWidth]
    rw [marginEq]
    have marginAtLeastTwo : 2 <= 6 * denominator := by omega
    calc
      blockWidth * (6 * denominator) <=
          blockWidth * (2 * (6 * denominator - 1)) := by
        exact Nat.mul_le_mul_left blockWidth (by omega)
      _ = (6 * denominator - 1) *
          (blockWidth + blockWidth) := by ring
  have schedulerPowerBound :
      copies * copies * 2 ^ width <=
        fieldConstant * 2 ^ commonExponent := by
    calc
      copies * copies * 2 ^ width <=
          2 ^ requestExponent * 2 ^ requestExponent *
            (fieldConstant * 2 ^ fieldExponent) := by gcongr
      _ = fieldConstant *
          2 ^ (requestExponent + requestExponent + fieldExponent) := by
        rw [Nat.pow_add, Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExponent :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) schedulerExponentBound)
  have incidencePowerBound : copies * 2 ^ width <=
      fieldConstant * 2 ^ commonExponent := by
    calc
      copies * 2 ^ width <=
          2 ^ requestExponent * (fieldConstant * 2 ^ fieldExponent) := by
        gcongr
      _ = fieldConstant * 2 ^ (requestExponent + fieldExponent) := by
        rw [Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExponent :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) incidenceExponentBound)
  have slotPowerBound : 2 ^ (dimension * width) <=
      slotConstant * 2 ^ commonExponent := by
    exact slotBound.trans <| Nat.mul_le_mul_left slotConstant
      (Nat.pow_le_pow_right (by omega) slotExponentBound)
  have schedulerScaled : 2 * copies * copies * 2 ^ width <=
      2 * (fieldConstant * 2 ^ commonExponent) := by
    calc
      2 * copies * copies * 2 ^ width =
          2 * (copies * copies * 2 ^ width) := by ring
      _ <= 2 * (fieldConstant * 2 ^ commonExponent) :=
        Nat.mul_le_mul_left 2 schedulerPowerBound
  have incidenceScaled : 7 * copies * 2 ^ width <=
      7 * (fieldConstant * 2 ^ commonExponent) := by
    calc
      7 * copies * 2 ^ width = 7 * (copies * 2 ^ width) := by ring
      _ <= 7 * (fieldConstant * 2 ^ commonExponent) :=
        Nat.mul_le_mul_left 7 incidencePowerBound
  have slotsScaled : 4 * 2 ^ (dimension * width) <=
      4 * (slotConstant * 2 ^ commonExponent) :=
    Nat.mul_le_mul_left 4 slotPowerBound
  calc
    OverheadBound.overheadVolume copies 1 width schedulerDepth routingDepth <=
        2 * copies * copies * 2 ^ width +
          7 * copies * 2 ^ width +
          4 * 2 ^ (dimension * width) :=
      twoBlock_overheadVolume_le denominator blockWidth copies
        denominatorPositive copiesPositive
    _ <= 2 * (fieldConstant * 2 ^ commonExponent) +
        7 * (fieldConstant * 2 ^ commonExponent) +
        4 * (slotConstant * 2 ^ commonExponent) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          schedulerScaled incidenceScaled)
        slotsScaled
    _ = twoBlockVolumeConstant denominator * 2 ^ commonExponent := by
      unfold twoBlockVolumeConstant
      dsimp [fieldConstant, slotConstant]
      ring

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
