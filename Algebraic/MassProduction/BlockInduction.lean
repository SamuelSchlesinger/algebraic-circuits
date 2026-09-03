import Algebraic.MassProduction.EqualBlock

/-!
# The equal-block induction

This file formalizes the induction in the mass-production manuscript.  At
level `k`, the input is split into one prefix block of width `m` and a suffix
of width `k * m`.  The number of request groups is an exact power of two at a
fixed rational rate strictly below `(k - 1) / k` on the suffix.  This removes
all real-valued ceilings from the finite construction.

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

/-- The recovery-code dimension used at every non-base induction step. -/
def stepDimension (denominator : Nat) : Nat :=
  12 * denominator

theorem stepDimension_positive
    (denominatorPositive : 0 < denominator) :
    0 < stepDimension denominator := by
  unfold stepDimension
  omega

theorem stepDimension_atLeastTwo
    (denominatorPositive : 0 < denominator) :
    2 <= stepDimension denominator := by
  unfold stepDimension
  omega

/-- Numerator of the group exponent in block units.  It is one integer below
the `(k - 1)`-block threshold at denominator `2 * denominator`. -/
def groupRateNumerator (level denominator : Nat) : Nat :=
  2 * denominator * (level - 1) - 1

/-- Denominator used to express the group exponent in block units. -/
def groupRateDenominator (denominator : Nat) : Nat :=
  2 * denominator

/-- Floored base-two exponent of the number of request groups. -/
def groupExponent (level denominator blockWidth : Nat) : Nat :=
  groupRateNumerator level denominator * blockWidth /
    groupRateDenominator denominator

/-- Exact power-of-two number of request groups at one induction step. -/
def groupCount (level denominator blockWidth : Nat) : Nat :=
  2 ^ groupExponent level denominator blockWidth

theorem groupRateNumerator_add_one
    (level denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator) :
    groupRateNumerator level denominator + 1 =
      2 * denominator * (level - 1) := by
  unfold groupRateNumerator
  have levelMinusPositive : 0 < level - 1 := by omega
  have productPositive : 0 < 2 * denominator * (level - 1) := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) denominatorPositive)
      levelMinusPositive
  exact Nat.sub_add_cancel productPositive

theorem groupRate_below_previousLevel
    (level denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator) :
    level * groupRateNumerator level denominator <
      (level - 1) * (groupRateDenominator denominator * level) := by
  have numeratorStep := groupRateNumerator_add_one level denominator
    levelAtLeastTwo denominatorPositive
  unfold groupRateDenominator
  have levelPositive : 0 < level := by omega
  have identity :
      level * (2 * denominator * (level - 1)) =
        (level - 1) * (2 * denominator * level) := by ring
  calc
    level * groupRateNumerator level denominator <
        level * (groupRateNumerator level denominator + 1) := by
      exact Nat.mul_lt_mul_of_pos_left
        (Nat.lt_succ_self (groupRateNumerator level denominator))
        levelPositive
    _ = level * (2 * denominator * (level - 1)) := by
      rw [numeratorStep]
    _ = (level - 1) * (2 * denominator * level) := identity

theorem groupCount_positive
    (level denominator blockWidth : Nat) :
    0 < groupCount level denominator blockWidth := by
  unfold groupCount
  positivity

/-- The group count is exactly within the recursive rational copy budget on
the `level * blockWidth` suffix. -/
theorem groupCount_le_recursiveBudget
    (level denominator blockWidth : Nat)
    (levelPositive : 0 < level) :
    groupCount level denominator blockWidth <=
      rationalCopyBudget (groupRateNumerator level denominator)
        (groupRateDenominator denominator * level)
        (level * blockWidth) := by
  unfold groupCount groupExponent rationalCopyBudget
  have rescaled := Nat.mul_div_mul_right
    (groupRateNumerator level denominator * blockWidth)
    (groupRateDenominator denominator) levelPositive
  have numeratorIdentity :
      groupRateNumerator level denominator * (level * blockWidth) =
        (groupRateNumerator level denominator * blockWidth) * level := by
    ring
  have denominatorIdentity :
      groupRateDenominator denominator * level =
        groupRateDenominator denominator * level := rfl
  rw [numeratorIdentity, denominatorIdentity, rescaled]

/-- A single rational exponent dominates the request load left in one group.
The extra half-margin absorbs the one-unit loss from adding two floors. -/
def groupLoadExponent (denominator blockWidth : Nat) : Nat :=
  (4 * denominator - 1) * blockWidth / (4 * denominator)

theorem requestExponent_le_group_add_load
    (level numerator denominator blockWidth : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth) :
    numerator * ((level + 1) * blockWidth) / denominator <=
      groupExponent level denominator blockWidth +
        groupLoadExponent denominator blockWidth := by
  let groupNumerator := groupRateNumerator level denominator
  let twiceDenominator := 2 * denominator
  have targetCoefficient :
      2 * ((level + 1) * numerator) <=
        groupNumerator + (2 * denominator - 1) := by
    have groupStep := groupRateNumerator_add_one level denominator
      levelAtLeastTwo denominatorPositive
    dsimp [groupNumerator]
    have targetStep :
        (level + 1) * numerator + 1 <= level * denominator := by
      omega
    have doubled := Nat.mul_le_mul_left 2 targetStep
    have levelDecomposition : level = (level - 1) + 1 := by omega
    have productIdentity :
        2 * (level * denominator) =
          2 * denominator * (level - 1) + 2 * denominator := by
      calc
        2 * (level * denominator) =
            2 * (((level - 1) + 1) * denominator) := by
          exact congrArg (fun value => 2 * (value * denominator))
            levelDecomposition
        _ = 2 * denominator * (level - 1) + 2 * denominator := by ring
    have levelMinusPositive : 0 < level - 1 := by omega
    have leftProductPositive : 0 < 2 * denominator * (level - 1) := by
      exact Nat.mul_pos (Nat.mul_pos (by omega) denominatorPositive)
        levelMinusPositive
    have rightProductPositive : 0 < 2 * denominator := by omega
    calc
      2 * ((level + 1) * numerator) <=
          2 * (level * denominator) - 2 := by omega
      _ = groupRateNumerator level denominator +
          (2 * denominator - 1) := by
        unfold groupRateNumerator
        omega
  have rescaled :
      numerator * ((level + 1) * blockWidth) / denominator =
        (2 * ((level + 1) * numerator) * blockWidth) /
          twiceDenominator := by
    dsimp [twiceDenominator]
    have scaled := Nat.mul_div_mul_left
      (numerator * ((level + 1) * blockWidth)) denominator
      (by omega : 0 < 2)
    rw [show 2 * (numerator * ((level + 1) * blockWidth)) =
      2 * ((level + 1) * numerator) * blockWidth by ring] at scaled
    exact scaled.symm
  have splitBound :
      (2 * ((level + 1) * numerator) * blockWidth) /
          twiceDenominator <=
        (groupNumerator * blockWidth) / twiceDenominator +
          ((2 * denominator - 1) * blockWidth) / twiceDenominator + 1 := by
    have coefficientScaled :
        2 * ((level + 1) * numerator) * blockWidth <=
          (groupNumerator + (2 * denominator - 1)) * blockWidth :=
      Nat.mul_le_mul_right blockWidth targetCoefficient
    calc
      (2 * ((level + 1) * numerator) * blockWidth) /
          twiceDenominator <=
        ((groupNumerator + (2 * denominator - 1)) * blockWidth) /
          twiceDenominator := Nat.div_le_div_right coefficientScaled
      _ = (groupNumerator * blockWidth +
          (2 * denominator - 1) * blockWidth) / twiceDenominator := by
        congr 1
        ring
      _ <= (groupNumerator * blockWidth) / twiceDenominator +
          ((2 * denominator - 1) * blockWidth) / twiceDenominator + 1 :=
        Nat.add_div_le_div_add_div_add_one _ _ _
  have remainderBound :
      ((2 * denominator - 1) * blockWidth) / twiceDenominator + 1 <=
        groupLoadExponent denominator blockWidth := by
    have twicePositive : 0 < twiceDenominator := by
      dsimp [twiceDenominator]
      omega
    have quotientScaled :
        (((2 * denominator - 1) * blockWidth) / twiceDenominator) *
            twiceDenominator <=
          (2 * denominator - 1) * blockWidth :=
      Nat.div_mul_le_self _ _
    unfold groupLoadExponent
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4 * denominator)).2
    calc
      ((((2 * denominator - 1) * blockWidth) / twiceDenominator + 1) *
          (4 * denominator)) =
          2 * ((((2 * denominator - 1) * blockWidth) /
            twiceDenominator) * twiceDenominator) +
            4 * denominator := by
        dsimp [twiceDenominator]
        ring
      _ <= 2 * ((2 * denominator - 1) * blockWidth) +
          4 * denominator := by gcongr
      _ <= (4 * denominator - 1) * blockWidth := by
        have coefficientIdentity :
            2 * (2 * denominator - 1) + 1 = 4 * denominator - 1 := by
          omega
        calc
          2 * ((2 * denominator - 1) * blockWidth) +
              4 * denominator <=
            2 * ((2 * denominator - 1) * blockWidth) +
              blockWidth := Nat.add_le_add_left blockLarge _
          _ = (2 * (2 * denominator - 1) + 1) * blockWidth := by
            ring
          _ = (4 * denominator - 1) * blockWidth := by
            rw [coefficientIdentity]
  rw [rescaled]
  exact splitBound.trans <| by
    unfold groupExponent groupRateDenominator
    dsimp [groupNumerator, twiceDenominator]
    exact Nat.add_le_add_left remainderBound _

/-- Every permitted batch leaves at most `2^groupLoadExponent` requests in a
single request group. -/
theorem requestGroupSize_le
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * ((level + 1) * blockWidth) / denominator)) :
    requestGroupSize copies (groupCount level denominator blockWidth) <=
      2 ^ groupLoadExponent denominator blockWidth := by
  have exponentBound := requestExponent_le_group_add_load level numerator
    denominator blockWidth levelAtLeastTwo denominatorPositive
    rateBelowLevel blockLarge
  apply (ceilDiv_le_iff_le_mul
    (groupCount_positive level denominator blockWidth)).2
  calc
    copies <=
        2 ^ (numerator * ((level + 1) * blockWidth) / denominator) :=
      copiesBound
    _ <= 2 ^ (groupExponent level denominator blockWidth +
        groupLoadExponent denominator blockWidth) :=
      Nat.pow_le_pow_right (by omega) exponentBound
    _ = groupCount level denominator blockWidth *
        2 ^ groupLoadExponent denominator blockWidth := by
      unfold groupCount
      rw [Nat.pow_add]

/-- The exact scheduler-capacity inequality for one induction step. -/
theorem step_loadBound
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * ((level + 1) * blockWidth) / denominator)) :
    requestGroupSize copies (groupCount level denominator blockWidth) *
        2 ^ fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive) <
      2 ^ (fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive) *
        (stepDimension denominator - 1)) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let loadExponent := groupLoadExponent denominator blockWidth
  have groupBound := requestGroupSize_le level numerator denominator
    blockWidth copies levelAtLeastTwo denominatorPositive rateBelowLevel
    blockLarge copiesBound
  have packingRate := prefixWidth_le_succ_dimension_mul_fieldWidth
    blockWidth dimension dimensionPositive
  have loadScaled :
      loadExponent * (4 * denominator) <=
        (4 * denominator - 1) * blockWidth := by
    dsimp [loadExponent]
    exact Nat.div_mul_le_self _ _
  have coefficientGap :
      (4 * denominator - 1) * (dimension + 1) <
        4 * denominator * (dimension - 2) := by
    dsimp [dimension]
    unfold stepDimension
    have firstStep : 4 * denominator - 1 + 1 = 4 * denominator := by
      omega
    have secondStep : 12 * denominator - 2 + 2 =
        12 * denominator := by omega
    nlinarith
  have scaledLoad :
      loadExponent * (4 * denominator * (dimension + 1)) <
        (width * (dimension - 2)) *
          (4 * denominator * (dimension + 1)) := by
    calc
      loadExponent * (4 * denominator * (dimension + 1)) =
          (loadExponent * (4 * denominator)) * (dimension + 1) := by ring
      _ <= ((4 * denominator - 1) * blockWidth) *
          (dimension + 1) := by gcongr
      _ = ((4 * denominator - 1) * (dimension + 1)) *
          blockWidth := by ring
      _ < (4 * denominator * (dimension - 2)) * blockWidth := by
        exact Nat.mul_lt_mul_of_pos_right coefficientGap (by omega)
      _ <= (4 * denominator * (dimension - 2)) *
          ((dimension + 1) * width) := by gcongr
      _ = (width * (dimension - 2)) *
          (4 * denominator * (dimension + 1)) := by ring
  have loadSmall : loadExponent < width * (dimension - 2) :=
    Nat.lt_of_mul_lt_mul_right scaledLoad
  have exponentSmall : loadExponent + width < width * (dimension - 1) := by
    calc
      loadExponent + width < width * (dimension - 2) + width :=
        Nat.add_lt_add_right loadSmall width
      _ = width * (dimension - 1) := by
        have dimensionAtLeast : 2 <= dimension := by
          dsimp [dimension]
          exact stepDimension_atLeastTwo denominatorPositive
        have step : dimension - 1 = (dimension - 2) + 1 := by omega
        rw [step, Nat.mul_add, Nat.mul_one]
  calc
    requestGroupSize copies (groupCount level denominator blockWidth) *
        2 ^ width <= 2 ^ loadExponent * 2 ^ width := by gcongr
    _ = 2 ^ (loadExponent + width) := (Nat.pow_add _ _ _).symm
    _ < 2 ^ (width * (dimension - 1)) :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 exponentSmall

/-! ## A shared bound for all finite bookkeeping parameters -/

/-- Width of the recursive suffix containing `level` equal blocks. -/
def stepSuffixWidth (level blockWidth : Nat) : Nat :=
  level * blockWidth

/-- Total width of the prefix block followed by the recursive suffix. -/
def stepInputWidth (level blockWidth : Nat) : Nat :=
  blockWidth + level * blockWidth

/-- Linear upper bound for the least admissible extension-field width. -/
def stepWidthBound
    (level denominator blockWidth : Nat) : Nat :=
  stepInputWidth level blockWidth + 4 * stepDimension denominator + 3

/-- Common bound for every width and sorting depth in the finite ledger. -/
def stepParameterBound
    (level denominator blockWidth : Nat) : Nat :=
  let inputWidth := stepInputWidth level blockWidth
  let widthBound := stepWidthBound level denominator blockWidth
  inputWidth + widthBound +
    stepDimension denominator * widthBound + 2

theorem targetNumerator_lt_denominator
    (level numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator) :
    numerator < denominator := by
  by_contra notBelow
  have denominatorLe : denominator <= numerator := by omega
  have scaled := Nat.mul_le_mul_left (level + 1) denominatorLe
  have strict : level * denominator < (level + 1) * denominator := by
    calc
      level * denominator < level * denominator + denominator := by omega
      _ = (level + 1) * denominator := by ring
  exact (rateBelowLevel.trans_le
    (show level * denominator <= (level + 1) * numerator from
      strict.le.trans scaled)).false

theorem groupExponent_le_inputWidth
    (level denominator blockWidth : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator) :
    groupExponent level denominator blockWidth <=
      stepInputWidth level blockWidth := by
  have numeratorStep := groupRateNumerator_add_one level denominator
    levelAtLeastTwo denominatorPositive
  apply Nat.div_le_of_le_mul
  unfold groupRateDenominator stepInputWidth
  have coefficientBound :
      groupRateNumerator level denominator <=
        2 * denominator * (level + 1) := by
    calc
      groupRateNumerator level denominator <=
          groupRateNumerator level denominator + 1 := Nat.le_succ _
      _ = 2 * denominator * (level - 1) := numeratorStep
      _ <= 2 * denominator * (level + 1) :=
        Nat.mul_le_mul_left (2 * denominator) (by omega)
  calc
    groupRateNumerator level denominator * blockWidth <=
        (2 * denominator * (level + 1)) * blockWidth := by gcongr
    _ = (2 * denominator) * stepInputWidth level blockWidth := by
      unfold stepInputWidth
      ring

theorem requestGroupSize_le_copies
    (copies groups : Nat)
    (groupsPositive : 0 < groups) :
    requestGroupSize copies groups <= copies := by
  apply (ceilDiv_le_iff_le_mul groupsPositive).2
  calc
    copies = 1 * copies := by ring
    _ <= groups * copies :=
      Nat.mul_le_mul_right copies (by omega)

/-- Every bit width and network depth in one induction-step ledger is bounded
by one explicit expression linear in the total input width. -/
theorem step_parameters_bounded
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator)) :
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
    let bound := stepParameterBound level denominator blockWidth
    dimension <= bound ∧
      width <= bound ∧
      schedulerDepth <= bound ∧
      blockWidth <= bound ∧
      IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
        bound ∧
      stepSuffixWidth level blockWidth <= bound ∧
      orderWidth + 1 <= bound ∧
      routingDepth <= bound := by
  dsimp only
  let inputWidth := stepInputWidth level blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let widthBound := stepWidthBound level denominator blockWidth
  let schedulerDepth := FiniteParameters.schedulerDepth copies groups width
  let groupBitWidth := FiniteParameters.groupBitWidth groups
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth :=
    FiniteParameters.routingDepth copies groups dimension width
  let bound := stepParameterBound level denominator blockWidth
  have inputWidthEq : inputWidth = (level + 1) * blockWidth := by
    dsimp [inputWidth, stepInputWidth]
    ring
  have suffixWidthEq : suffixWidth = level * blockWidth := rfl
  have widthSelected : width <= widthBound := by
    have selected := fieldWidth_le_quotient_add blockWidth dimension
      dimensionPositive
    dsimp [widthBound, stepWidthBound, inputWidth, stepInputWidth]
    exact selected.trans <| by
      have quotient := Nat.div_le_self blockWidth dimension
      have blockLe : blockWidth <= (level + 1) * blockWidth := by
        calc
          blockWidth = 1 * blockWidth := by ring
          _ <= (level + 1) * blockWidth :=
            Nat.mul_le_mul_right blockWidth (by omega)
      omega
  have numeratorBelow : numerator <= denominator :=
    (targetNumerator_lt_denominator level numerator denominator
      denominatorPositive rateBelowLevel).le
  have requestExponentLeInput :
      numerator * inputWidth / denominator <= inputWidth := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right inputWidth numeratorBelow
  have copiesCoarse : copies <= 2 ^ inputWidth :=
    copiesBound.trans (Nat.pow_le_pow_right (by omega)
      requestExponentLeInput)
  have groupExponentBound :
      groupExponent level denominator blockWidth <= inputWidth := by
    exact groupExponent_le_inputWidth level denominator blockWidth
      levelAtLeastTwo denominatorPositive
  have groupsCoarse : groups <= 2 ^ inputWidth := by
    dsimp [groups, groupCount]
    exact Nat.pow_le_pow_right (by omega) groupExponentBound
  have widthPositive := fieldWidth_positive blockWidth dimension
    dimensionPositive
  have scalarBound : nonzeroScalarCount width <= 2 ^ width := by
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    exact Nat.sub_le _ _
  have widthPowerBound : 2 ^ width <= 2 ^ widthBound :=
    Nat.pow_le_pow_right (by omega) widthSelected
  have incidenceBound :
      FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound) := by
    unfold FiniteParameters.incidenceCount
    calc
      copies * nonzeroScalarCount width <=
          2 ^ inputWidth * 2 ^ width := Nat.mul_le_mul copiesCoarse scalarBound
      _ <= 2 ^ inputWidth * 2 ^ widthBound := by gcongr
      _ = 2 ^ (inputWidth + widthBound) :=
        (Nat.pow_add _ _ _).symm
  have groupSizeBound : requestGroupSize copies groups <= copies :=
    requestGroupSize_le_copies copies groups <| by
      dsimp [groups]
      exact groupCount_positive level denominator blockWidth
  have schedulerRecordBound :
      requestGroupSize copies groups * nonzeroScalarCount width <=
        2 ^ (inputWidth + widthBound) := by
    calc
      requestGroupSize copies groups * nonzeroScalarCount width <=
          copies * nonzeroScalarCount width := by gcongr
      _ = FiniteParameters.incidenceCount copies width := rfl
      _ <= 2 ^ (inputWidth + widthBound) := incidenceBound
  have schedulerDepthBound : schedulerDepth <= inputWidth + widthBound := by
    unfold schedulerDepth FiniteParameters.schedulerDepth
    exact FiniteParameters.binaryDepth_le _ _ schedulerRecordBound
  have orderDepthBound : orderWidth <= inputWidth + widthBound := by
    unfold orderWidth FiniteParameters.orderWidth
    exact FiniteParameters.binaryDepth_le _ _ incidenceBound
  have groupWidthBound : groupBitWidth <= inputWidth := by
    unfold groupBitWidth FiniteParameters.groupBitWidth
    exact FiniteParameters.binaryDepth_le _ _ groupsCoarse
  have slotBound :
      FiniteParameters.resourceSlotCount groups dimension width <=
        2 ^ (inputWidth + dimension * widthBound) := by
    unfold FiniteParameters.resourceSlotCount
    exact Nat.pow_le_pow_right (by omega) <| by
      exact Nat.add_le_add groupWidthBound
        (Nat.mul_le_mul_left dimension widthSelected)
  let routingExponent := inputWidth + widthBound +
    dimension * widthBound + 1
  have routingRecordBound :
      FiniteParameters.routingRecords copies groups dimension width <=
        2 ^ routingExponent := by
    have incidenceRaised : FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      incidenceBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have slotsRaised :
        FiniteParameters.resourceSlotCount groups dimension width <=
          2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      slotBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    unfold FiniteParameters.routingRecords
    calc
      FiniteParameters.incidenceCount copies width +
          FiniteParameters.resourceSlotCount groups dimension width <=
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
    dsimp [widthBound, stepWidthBound]
    omega
  have inputLeBound : inputWidth <= bound := by rw [boundEq]; omega
  have widthBoundLeBound : widthBound <= bound := by rw [boundEq]; omega
  have suffixLeInput : suffixWidth <= inputWidth := by
    dsimp [suffixWidth, inputWidth, stepSuffixWidth, stepInputWidth]
    omega
  have schedulerBound : schedulerDepth <= bound :=
    schedulerDepthBound.trans (by rw [boundEq]; omega)
  have blockLeInput : blockWidth <= inputWidth := by
    dsimp [inputWidth, stepInputWidth]
    omega
  have keyBound : IncidenceRouting.incidenceKeyWidth
      groupBitWidth dimension width <= bound := by
    unfold IncidenceRouting.incidenceKeyWidth
    have productBound : dimension * width <= dimension * widthBound :=
      Nat.mul_le_mul_left dimension widthSelected
    rw [boundEq]
    omega
  have orderBound : orderWidth + 1 <= bound :=
    (Nat.add_le_add_right orderDepthBound 1).trans
      (by rw [boundEq]; omega)
  have routingExponentLeBound : routingExponent <= bound := by
    rw [boundEq]
    dsimp [routingExponent]
    omega
  have localBounds :
      dimension <= bound ∧ width <= bound ∧ schedulerDepth <= bound ∧
        blockWidth <= bound ∧
        IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
          bound ∧ suffixWidth <= bound ∧ orderWidth + 1 <= bound ∧
        routingDepth <= bound :=
    ⟨dimensionLeWidthBound.trans widthBoundLeBound,
      widthSelected.trans widthBoundLeBound, schedulerBound,
      blockLeInput.trans inputLeBound, keyBound,
      suffixLeInput.trans inputLeBound, orderBound,
      routingDepthBound.trans routingExponentLeBound⟩
  simpa only [inputWidth, suffixWidth, dimension, dimensionPositive, width,
    groups, schedulerDepth, groupBitWidth, orderWidth, routingDepth, bound]
    using localBounds

/-! ## Exact live-record volume -/

/-- The canonical live-record volume has precisely the four contributions
needed by the exponent calculation: grouped scheduling, group-line work,
incidences, and group-indexed resource slots. -/
theorem step_overheadVolume_le
    (level denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (copiesPositive : 0 < copies) :
    let dimension := stepDimension denominator
    let dimensionPositive := stepDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let groups := groupCount level denominator blockWidth
    let groupSize := requestGroupSize copies groups
    OverheadBound.overheadVolume copies groups width
        (FiniteParameters.schedulerDepth copies groups width)
        (FiniteParameters.routingDepth copies groups dimension width) <=
      2 * groups * groupSize * groupSize * 2 ^ width +
        groups * groupSize * 2 ^ width +
        6 * copies * 2 ^ width +
        4 * groups * 2 ^ (dimension * width) := by
  dsimp only
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let groupSize := requestGroupSize copies groups
  let scalarCount := nonzeroScalarCount width
  let schedulerRecords := groupSize * scalarCount
  let routingRecords :=
    FiniteParameters.routingRecords copies groups dimension width
  have widthPositive := fieldWidth_positive blockWidth dimension
    dimensionPositive
  have groupsPositive : 0 < groups := by
    dsimp [groups]
    exact groupCount_positive level denominator blockWidth
  have groupSizePositive : 0 < groupSize := by
    by_contra notPositive
    have groupSizeZero : groupSize = 0 := by omega
    have impossible := (ceilDiv_le_iff_le_mul groupsPositive).mp
      (show requestGroupSize copies groups <= 0 by
        simpa only [groupSize] using Nat.le_of_eq groupSizeZero)
    omega
  have scalarPositive : 0 < scalarCount := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    have : 1 < 2 ^ width :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 widthPositive
    exact Nat.sub_pos_of_lt this
  have schedulerRecordsPositive : 0 < schedulerRecords :=
    Nat.mul_pos groupSizePositive scalarPositive
  have schedulerNetwork :
      networkRecords
          (FiniteParameters.schedulerDepth copies groups width) <=
        2 * (groupSize * scalarCount) := by
    exact Nat.le_of_lt <| by
      simpa [FiniteParameters.schedulerDepth, groupSize, schedulerRecords]
        using FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          schedulerRecords schedulerRecordsPositive
  have scalarBound : scalarCount <= 2 ^ width := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    exact Nat.sub_le _ _
  have groupWidthBound :
      FiniteParameters.groupBitWidth groups <=
        groupExponent level denominator blockWidth := by
    unfold FiniteParameters.groupBitWidth
    apply FiniteParameters.binaryDepth_le
    dsimp [groups]
    unfold groupCount
    exact le_rfl
  have slotBound :
      FiniteParameters.resourceSlotCount groups dimension width <=
        groups * 2 ^ (dimension * width) := by
    unfold FiniteParameters.resourceSlotCount
    calc
      2 ^ (FiniteParameters.groupBitWidth groups + dimension * width) <=
          2 ^ (groupExponent level denominator blockWidth +
            dimension * width) :=
        Nat.pow_le_pow_right (by omega)
          (Nat.add_le_add_right groupWidthBound _)
      _ = groups * 2 ^ (dimension * width) := by
        rw [Nat.pow_add]
        dsimp [groups]
        unfold groupCount
        rfl
  have routingRecordsPositive : 0 < routingRecords := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords
    have slotPositive : 0 <
        FiniteParameters.resourceSlotCount groups dimension width := by
      unfold FiniteParameters.resourceSlotCount
      positivity
    omega
  have routingNetwork :
      networkRecords
          (FiniteParameters.routingDepth copies groups dimension width) <=
        2 * routingRecords := by
    exact Nat.le_of_lt <| by
      simpa [FiniteParameters.routingDepth, routingRecords]
        using FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          routingRecords routingRecordsPositive
  have routingRecordsBound : routingRecords <=
      copies * 2 ^ width + groups * 2 ^ (dimension * width) := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords FiniteParameters.incidenceCount
    exact Nat.add_le_add
      (Nat.mul_le_mul_left copies scalarBound) slotBound
  unfold OverheadBound.overheadVolume
  dsimp only [groupSize]
  calc
    groups * requestGroupSize copies groups *
          (networkRecords
              (FiniteParameters.schedulerDepth copies groups width) +
            2 ^ width) +
        2 * (copies * 2 ^ width) +
        2 * networkRecords
          (FiniteParameters.routingDepth copies groups dimension width) <=
      groups * groupSize *
          (2 * (groupSize * scalarCount) + 2 ^ width) +
        2 * (copies * 2 ^ width) + 2 * (2 * routingRecords) := by
      gcongr
    _ <= groups * groupSize *
          (2 * (groupSize * 2 ^ width) + 2 ^ width) +
        2 * (copies * 2 ^ width) +
          2 * (2 * (copies * 2 ^ width +
            groups * 2 ^ (dimension * width))) := by
      gcongr
    _ = 2 * groups * groupSize * groupSize * 2 ^ width +
        groups * groupSize * 2 ^ width +
        6 * copies * 2 ^ width +
        4 * groups * 2 ^ (dimension * width) := by ring

/-! ## Strict exponent margin for the complete overhead -/

/-- Denominator of the strict common overhead exponent. -/
def stepMarginDenominator (level denominator : Nat) : Nat :=
  24 * denominator * (level + 1)

/-- Floored exponent appearing in the extension-field cardinality bound. -/
def stepFieldExponent (denominator blockWidth : Nat) : Nat :=
  blockWidth / stepDimension denominator

/-- One strict subunit exponent dominating all non-resource volumes. -/
def stepCommonExponent
    (level denominator blockWidth : Nat) : Nat :=
  (stepMarginDenominator level denominator - 1) *
      stepInputWidth level blockWidth /
    stepMarginDenominator level denominator

theorem stepMarginDenominator_positive
    (level denominator : Nat)
    (denominatorPositive : 0 < denominator) :
    0 < stepMarginDenominator level denominator := by
  unfold stepMarginDenominator
  positivity

/-- A scaled block-unit margin implies the common strict subunit exponent on
the complete `(level + 1)`-block input. -/
theorem exponent_le_stepCommonExponent
    (level denominator blockWidth exponent : Nat)
    (denominatorPositive : 0 < denominator)
    (scaledMargin :
      exponent * (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth) :
    exponent <= stepCommonExponent level denominator blockWidth := by
  let marginDenominator := stepMarginDenominator level denominator
  let inputWidth := stepInputWidth level blockWidth
  have marginPositive : 0 < marginDenominator :=
    stepMarginDenominator_positive level denominator denominatorPositive
  have multiplied := Nat.mul_le_mul_right (level + 1) scaledMargin
  have plusInput :
      exponent * marginDenominator + inputWidth <=
        marginDenominator * inputWidth := by
    dsimp [marginDenominator, inputWidth, stepMarginDenominator,
      stepInputWidth]
    convert multiplied using 1 <;> ring
  have marginDecomposition : marginDenominator - 1 + 1 =
      marginDenominator := Nat.sub_add_cancel marginPositive
  apply (Nat.le_div_iff_mul_le marginPositive).2
  change exponent * marginDenominator <=
    (marginDenominator - 1) * inputWidth
  have rhsDecomposition :
      (marginDenominator - 1) * inputWidth + inputWidth =
        marginDenominator * inputWidth := by
    calc
      (marginDenominator - 1) * inputWidth + inputWidth =
          ((marginDenominator - 1) + 1) * inputWidth := by ring
      _ = marginDenominator * inputWidth := by rw [marginDecomposition]
  rw [← rhsDecomposition] at plusInput
  exact Nat.le_of_add_le_add_right plusInput

/-- All four live-volume exponents fit under one fixed exponent strictly
below the total input width. -/
theorem step_volume_exponents_le
    (level numerator denominator blockWidth : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator) :
    let groupExponent := groupExponent level denominator blockWidth
    let loadExponent := groupLoadExponent denominator blockWidth
    let fieldExponent := stepFieldExponent denominator blockWidth
    let requestExponent :=
      numerator * stepInputWidth level blockWidth / denominator
    let commonExponent :=
      stepCommonExponent level denominator blockWidth
    groupExponent + loadExponent + loadExponent + fieldExponent <=
        commonExponent ∧
      groupExponent + loadExponent + fieldExponent <= commonExponent ∧
      requestExponent + fieldExponent <= commonExponent ∧
      groupExponent + blockWidth <= commonExponent := by
  dsimp only
  let groupExp := groupExponent level denominator blockWidth
  let loadExp := groupLoadExponent denominator blockWidth
  let fieldExp := stepFieldExponent denominator blockWidth
  let requestExp :=
    numerator * stepInputWidth level blockWidth / denominator
  let groupNumerator := groupRateNumerator level denominator
  have groupBase : groupExp * (2 * denominator) <=
      groupNumerator * blockWidth := by
    dsimp [groupExp]
    unfold groupExponent groupRateDenominator
    exact Nat.div_mul_le_self _ _
  have loadBase : loadExp * (4 * denominator) <=
      (4 * denominator - 1) * blockWidth := by
    dsimp [loadExp]
    unfold groupLoadExponent
    exact Nat.div_mul_le_self _ _
  have fieldBase : fieldExp * (12 * denominator) <= blockWidth := by
    dsimp [fieldExp]
    unfold stepFieldExponent stepDimension
    exact Nat.div_mul_le_self _ _
  have requestBase : requestExp * denominator <=
      numerator * stepInputWidth level blockWidth := by
    dsimp [requestExp]
    exact Nat.div_mul_le_self _ _
  have groupScaled : groupExp * (24 * denominator) <=
      12 * (groupNumerator * blockWidth) := by
    calc
      groupExp * (24 * denominator) =
          12 * (groupExp * (2 * denominator)) := by ring
      _ <= 12 * (groupNumerator * blockWidth) := by gcongr
  have twiceLoadScaled : (loadExp + loadExp) * (24 * denominator) <=
      12 * ((4 * denominator - 1) * blockWidth) := by
    calc
      (loadExp + loadExp) * (24 * denominator) =
          12 * (loadExp * (4 * denominator)) := by ring
      _ <= 12 * ((4 * denominator - 1) * blockWidth) := by gcongr
  have fieldScaled : fieldExp * (24 * denominator) <=
      2 * blockWidth := by
    calc
      fieldExp * (24 * denominator) =
          2 * (fieldExp * (12 * denominator)) := by ring
      _ <= 2 * blockWidth := by gcongr
  have requestScaled : requestExp * (24 * denominator) <=
      24 * (numerator * stepInputWidth level blockWidth) := by
    calc
      requestExp * (24 * denominator) =
          24 * (requestExp * denominator) := by ring
      _ <= 24 * (numerator * stepInputWidth level blockWidth) := by gcongr
  have groupStep := groupRateNumerator_add_one level denominator
    levelAtLeastTwo denominatorPositive
  have fourStep : 4 * denominator - 1 + 1 = 4 * denominator :=
    Nat.sub_add_cancel (by omega)
  have levelDecomposition : level + 1 = (level - 1) + 2 := by omega
  have targetCoefficientIdentity :
      24 * denominator * (level + 1) =
        12 * (2 * denominator * (level - 1)) +
          12 * (4 * denominator) := by
    rw [levelDecomposition]
    ring
  have schedulerCoefficient :
      12 * groupNumerator + 12 * (4 * denominator - 1) + 3 <=
        24 * denominator * (level + 1) := by
    omega
  have schedulerMargin :
      (groupExp + loadExp + loadExp + fieldExp) *
          (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth := by
    calc
      (groupExp + loadExp + loadExp + fieldExp) *
            (24 * denominator) + blockWidth =
          groupExp * (24 * denominator) +
            (loadExp + loadExp) * (24 * denominator) +
            fieldExp * (24 * denominator) + blockWidth := by ring
      _ <= 12 * (groupNumerator * blockWidth) +
          12 * ((4 * denominator - 1) * blockWidth) +
          2 * blockWidth + blockWidth :=
        Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add groupScaled twiceLoadScaled) fieldScaled)
          le_rfl
      _ = (12 * groupNumerator +
          12 * (4 * denominator - 1) + 3) * blockWidth := by ring
      _ <= 24 * denominator * (level + 1) * blockWidth := by gcongr
  have schedulerBound := exponent_le_stepCommonExponent level denominator
    blockWidth (groupExp + loadExp + loadExp + fieldExp)
    denominatorPositive schedulerMargin
  have groupLineBound : groupExp + loadExp + fieldExp <=
      stepCommonExponent level denominator blockWidth := by
    exact (show groupExp + loadExp + fieldExp <=
        groupExp + loadExp + loadExp + fieldExp by omega).trans
      schedulerBound
  have targetStep : (level + 1) * numerator + 1 <=
      level * denominator := by omega
  have targetScaled := Nat.mul_le_mul_left 24 targetStep
  have requestCoefficient :
      24 * ((level + 1) * numerator) + 3 <=
        24 * denominator * (level + 1) := by
    calc
      24 * ((level + 1) * numerator) + 3 <=
          24 * ((level + 1) * numerator) + 24 := by omega
      _ = 24 * ((level + 1) * numerator + 1) := by ring
      _ <= 24 * (level * denominator) := targetScaled
      _ <= 24 * ((level + 1) * denominator) := by
        gcongr
        exact Nat.le_succ level
      _ = 24 * denominator * (level + 1) := by ring
  have requestMargin :
      (requestExp + fieldExp) * (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth := by
    calc
      (requestExp + fieldExp) * (24 * denominator) + blockWidth =
          requestExp * (24 * denominator) +
            fieldExp * (24 * denominator) + blockWidth := by ring
      _ <= 24 * (numerator * stepInputWidth level blockWidth) +
          2 * blockWidth + blockWidth :=
        Nat.add_le_add
          (Nat.add_le_add requestScaled fieldScaled) le_rfl
      _ = (24 * ((level + 1) * numerator) + 3) * blockWidth := by
        unfold stepInputWidth
        ring
      _ <= 24 * denominator * (level + 1) * blockWidth := by gcongr
  have requestBound := exponent_le_stepCommonExponent level denominator
    blockWidth (requestExp + fieldExp) denominatorPositive requestMargin
  have groupCoefficient :
      12 * groupNumerator + 24 * denominator + 1 <=
        24 * denominator * (level + 1) := by
    omega
  have groupMargin :
      (groupExp + blockWidth) * (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth := by
    calc
      (groupExp + blockWidth) * (24 * denominator) + blockWidth =
          groupExp * (24 * denominator) +
            24 * denominator * blockWidth + blockWidth := by ring
      _ <= 12 * (groupNumerator * blockWidth) +
          24 * denominator * blockWidth + blockWidth := by gcongr
      _ = (12 * groupNumerator + 24 * denominator + 1) *
          blockWidth := by ring
      _ <= 24 * denominator * (level + 1) * blockWidth := by gcongr
  have groupBound := exponent_le_stepCommonExponent level denominator
    blockWidth (groupExp + blockWidth) denominatorPositive groupMargin
  exact ⟨schedulerBound, groupLineBound, requestBound, groupBound⟩

/-- Fixed multiplicative loss in the field-cardinality estimate. -/
def stepFieldConstant (denominator : Nat) : Nat :=
  2 ^ (4 * stepDimension denominator + 3)

/-- Fixed multiplicative loss in the affine resource-slot estimate. -/
def stepSlotConstant (denominator : Nat) : Nat :=
  2 ^ (stepDimension denominator *
    (4 * stepDimension denominator + 3))

/-- Common constant multiplying the strict live-volume exponential. -/
def stepVolumeConstant (denominator : Nat) : Nat :=
  9 * stepFieldConstant denominator + 4 * stepSlotConstant denominator

/-- The complete canonical live-record volume is a fixed constant times a
strict subunit exponential. -/
theorem step_overheadVolume_exponential_le
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator)) :
    let dimension := stepDimension denominator
    let dimensionPositive := stepDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let groups := groupCount level denominator blockWidth
    let schedulerDepth :=
      FiniteParameters.schedulerDepth copies groups width
    let routingDepth :=
      FiniteParameters.routingDepth copies groups dimension width
    OverheadBound.overheadVolume copies groups width schedulerDepth
        routingDepth <=
      stepVolumeConstant denominator *
        2 ^ stepCommonExponent level denominator blockWidth := by
  dsimp only
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let groupSize := requestGroupSize copies groups
  let groupExp := groupExponent level denominator blockWidth
  let loadExp := groupLoadExponent denominator blockWidth
  let fieldExp := stepFieldExponent denominator blockWidth
  let requestExp :=
    numerator * stepInputWidth level blockWidth / denominator
  let commonExp := stepCommonExponent level denominator blockWidth
  let fieldConstant := stepFieldConstant denominator
  let slotConstant := stepSlotConstant denominator
  have groupSizeBound : groupSize <= 2 ^ loadExp := by
    dsimp [groupSize, loadExp]
    exact requestGroupSize_le level numerator denominator blockWidth copies
      levelAtLeastTwo denominatorPositive rateBelowLevel blockLarge
      (by simpa [stepInputWidth, Nat.add_mul, Nat.add_comm] using copiesBound)
  have fieldBound : 2 ^ width <= fieldConstant * 2 ^ fieldExp := by
    have selected := fieldCard_le blockWidth dimension dimensionPositive
    dsimp [fieldConstant, fieldExp, stepFieldConstant, stepFieldExponent]
    exact selected
  have slotBound : 2 ^ (dimension * width) <=
      slotConstant * 2 ^ blockWidth := by
    have selected := fieldCard_pow_dimension_le blockWidth dimension
      dimensionPositive
    dsimp [slotConstant, stepSlotConstant]
    exact selected
  obtain ⟨schedulerExponent, groupLineExponent, incidenceExponent,
      slotExponent⟩ := step_volume_exponents_le level numerator denominator
        blockWidth levelAtLeastTwo denominatorPositive rateBelowLevel
  have groupsPower : groups = 2 ^ groupExp := by rfl
  have groupsBound : groups <= 2 ^ groupExp := groupsPower.le
  have schedulerPower :
      groups * groupSize * groupSize * 2 ^ width <=
        fieldConstant * 2 ^ commonExp := by
    calc
      groups * groupSize * groupSize * 2 ^ width <=
          2 ^ groupExp * 2 ^ loadExp * 2 ^ loadExp *
            (fieldConstant * 2 ^ fieldExp) := by
        gcongr
      _ = fieldConstant *
          2 ^ (groupExp + loadExp + loadExp + fieldExp) := by
        rw [Nat.pow_add, Nat.pow_add, Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) schedulerExponent)
  have groupLinePower : groups * groupSize * 2 ^ width <=
      fieldConstant * 2 ^ commonExp := by
    calc
      groups * groupSize * 2 ^ width <=
          2 ^ groupExp * 2 ^ loadExp *
            (fieldConstant * 2 ^ fieldExp) := by gcongr
      _ = fieldConstant * 2 ^ (groupExp + loadExp + fieldExp) := by
        rw [Nat.pow_add, Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) groupLineExponent)
  have incidencePower : copies * 2 ^ width <=
      fieldConstant * 2 ^ commonExp := by
    calc
      copies * 2 ^ width <=
          2 ^ requestExp * (fieldConstant * 2 ^ fieldExp) := by gcongr
      _ = fieldConstant * 2 ^ (requestExp + fieldExp) := by
        rw [Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) incidenceExponent)
  have slotsPower : groups * 2 ^ (dimension * width) <=
      slotConstant * 2 ^ commonExp := by
    calc
      groups * 2 ^ (dimension * width) <=
          2 ^ groupExp * (slotConstant * 2 ^ blockWidth) := by gcongr
      _ = slotConstant * 2 ^ (groupExp + blockWidth) := by
        rw [Nat.pow_add]
        ring
      _ <= slotConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left slotConstant
          (Nat.pow_le_pow_right (by omega) slotExponent)
  have rawVolume := step_overheadVolume_le level denominator blockWidth
    copies denominatorPositive copiesPositive
  calc
    OverheadBound.overheadVolume copies groups width
        (FiniteParameters.schedulerDepth copies groups width)
        (FiniteParameters.routingDepth copies groups dimension width) <=
      2 * groups * groupSize * groupSize * 2 ^ width +
        groups * groupSize * 2 ^ width +
        6 * copies * 2 ^ width +
        4 * groups * 2 ^ (dimension * width) := rawVolume
    _ <= 2 * (fieldConstant * 2 ^ commonExp) +
        fieldConstant * 2 ^ commonExp +
        6 * (fieldConstant * 2 ^ commonExp) +
        4 * (slotConstant * 2 ^ commonExp) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (show 2 * groups * groupSize * groupSize * 2 ^ width <=
                2 * (fieldConstant * 2 ^ commonExp) by
              calc
                2 * groups * groupSize * groupSize * 2 ^ width =
                    2 * (groups * groupSize * groupSize * 2 ^ width) := by
                  ring
                _ <= 2 * (fieldConstant * 2 ^ commonExp) :=
                  Nat.mul_le_mul_left 2 schedulerPower)
            groupLinePower)
          (show 6 * copies * 2 ^ width <=
              6 * (fieldConstant * 2 ^ commonExp) by
            calc
              6 * copies * 2 ^ width = 6 * (copies * 2 ^ width) := by ring
              _ <= 6 * (fieldConstant * 2 ^ commonExp) :=
                Nat.mul_le_mul_left 6 incidencePower))
        (show 4 * groups * 2 ^ (dimension * width) <=
            4 * (slotConstant * 2 ^ commonExp) by
          calc
            4 * groups * 2 ^ (dimension * width) =
                4 * (groups * 2 ^ (dimension * width)) := by ring
            _ <= 4 * (slotConstant * 2 ^ commonExp) :=
              Nat.mul_le_mul_left 4 slotsPower)
    _ = stepVolumeConstant denominator * 2 ^ commonExp := by
      unfold stepVolumeConstant
      dsimp [fieldConstant, slotConstant]
      ring

/-! ## Absorbing the polynomial ledger -/

/-- Slope relating ledger widths to the complete input width. -/
def stepParameterSlope (denominator : Nat) : Nat :=
  let dimension := stepDimension denominator
  3 + (dimension + 1) * (4 * dimension + 4)

/-- Constant coefficient of the degree-ten polynomial ledger envelope. -/
def stepCoefficientConstant (denominator : Nat) : Nat :=
  let slope := stepParameterSlope denominator
  1000000 * (slope + 1) ^ 10 + 5 * slope

theorem step_parameterBound_le
    (level denominator blockWidth : Nat) :
    stepParameterBound level denominator blockWidth <=
      stepParameterSlope denominator *
        (stepInputWidth level blockWidth + 1) := by
  let dimension := stepDimension denominator
  let inputWidth := stepInputWidth level blockWidth
  let widthBound := stepWidthBound level denominator blockWidth
  let slope := stepParameterSlope denominator
  have widthLinear : widthBound <=
      (4 * dimension + 4) * (inputWidth + 1) := by
    dsimp [widthBound, stepWidthBound]
    change inputWidth + 4 * dimension + 3 <= _
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

theorem step_coefficient_le
    (level denominator blockWidth : Nat) :
    let parameterBound := stepParameterBound level denominator blockWidth
    let inputWidth := stepInputWidth level blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      stepCoefficientConstant denominator * (inputWidth + 1) ^ 10 := by
  dsimp only
  let parameterBound := stepParameterBound level denominator blockWidth
  let inputWidth := stepInputWidth level blockWidth
  let slope := stepParameterSlope denominator
  have parameterLinear : parameterBound <= slope * (inputWidth + 1) :=
    step_parameterBound_le level denominator blockWidth
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
    _ = stepCoefficientConstant denominator *
        (inputWidth + 1) ^ 10 := by
      unfold stepCoefficientConstant
      dsimp [slope]
      ring

theorem step_coefficient_le_monomial
    (level denominator blockWidth : Nat)
    (blockPositive : 0 < blockWidth) :
    let parameterBound := stepParameterBound level denominator blockWidth
    let inputWidth := stepInputWidth level blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      (stepCoefficientConstant denominator * 2 ^ 10) *
        inputWidth ^ 10 := by
  dsimp only
  let inputWidth := stepInputWidth level blockWidth
  have inputPositive : 0 < inputWidth := by
    dsimp [inputWidth, stepInputWidth]
    positivity
  have successorBound : inputWidth + 1 <= 2 * inputWidth := by omega
  exact (step_coefficient_le level denominator blockWidth).trans <| by
    calc
      stepCoefficientConstant denominator * (inputWidth + 1) ^ 10 <=
          stepCoefficientConstant denominator * (2 * inputWidth) ^ 10 := by
        gcongr
      _ = (stepCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10 := by
        rw [mul_pow]
        ring

/-- Fixed coefficient of the polynomial-times-exponential overhead bound. -/
def stepOverheadConstant (denominator : Nat) : Nat :=
  stepVolumeConstant denominator *
    (stepCoefficientConstant denominator * 2 ^ 10)

/-- Pointwise composition of the exact ledger, the live-volume estimate, and
the common polynomial coefficient estimate. -/
theorem step_overhead_le_of_growth
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator))
    (growthBound :
      stepOverheadConstant denominator *
          stepInputWidth level blockWidth ^ 10 *
          2 ^ stepCommonExponent level denominator blockWidth <=
        2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) :
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
    CompositionBound.overheadCostBound copies groups blockWidth dimension width
        (stepSuffixWidth level blockWidth) schedulerDepth groupBitWidth
        orderWidth routingDepth routingDepth <=
      2 ^ stepInputWidth level blockWidth /
        stepInputWidth level blockWidth := by
  dsimp only
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let schedulerDepth := FiniteParameters.schedulerDepth copies groups width
  let groupBitWidth := FiniteParameters.groupBitWidth groups
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth :=
    FiniteParameters.routingDepth copies groups dimension width
  let parameterBound := stepParameterBound level denominator blockWidth
  let inputWidth := stepInputWidth level blockWidth
  let commonExponent := stepCommonExponent level denominator blockWidth
  obtain ⟨dimensionBound, widthBound, schedulerBound, prefixBound,
      keyBound, suffixBound, orderBound, routingBound⟩ :=
    step_parameters_bounded level numerator denominator blockWidth copies
      levelAtLeastTwo denominatorPositive rateBelowLevel copiesBound
  have factored := OverheadBound.overheadCostBound_le_factored
    copies groups blockWidth dimension width suffixWidth schedulerDepth
    groupBitWidth orderWidth routingDepth
    (fieldWidth_positive blockWidth dimension dimensionPositive)
  have byVolume := OverheadBound.factoredOverhead_le_volume_mul_envelope
    copies groups blockWidth dimension width suffixWidth schedulerDepth
    groupBitWidth orderWidth routingDepth parameterBound dimensionBound
    widthBound schedulerBound prefixBound keyBound suffixBound orderBound
    routingBound
  have volumeBound := step_overheadVolume_exponential_le level numerator
    denominator blockWidth copies levelAtLeastTwo denominatorPositive
    rateBelowLevel blockLarge copiesPositive copiesBound
  have coefficientBound := step_coefficient_le_monomial level denominator
    blockWidth (by omega)
  calc
    CompositionBound.overheadCostBound copies groups blockWidth dimension width
        suffixWidth schedulerDepth groupBitWidth orderWidth routingDepth
        routingDepth <=
      OverheadBound.factoredOverhead copies groups blockWidth dimension width
        suffixWidth schedulerDepth groupBitWidth orderWidth routingDepth :=
      factored
    _ <= OverheadBound.overheadVolume copies groups width schedulerDepth
          routingDepth *
        (OverheadBound.coefficientEnvelope parameterBound +
          5 * parameterBound) := byVolume
    _ <= (stepVolumeConstant denominator * 2 ^ commonExponent) *
        ((stepCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10) := Nat.mul_le_mul volumeBound coefficientBound
    _ = stepOverheadConstant denominator * inputWidth ^ 10 *
        2 ^ commonExponent := by
      unfold stepOverheadConstant
      ring
    _ <= 2 ^ inputWidth / inputWidth := growthBound

/-- All non-resource work is eventually at most one Shannon-scale unit,
uniformly over every permitted batch. -/
theorem eventually_step_overhead_le
    (level numerator denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator) :
    ∀ᶠ blockWidth in Filter.atTop,
      ∀ copies : Nat,
        0 < copies ->
        copies <=
          2 ^ (numerator * stepInputWidth level blockWidth / denominator) ->
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
            stepInputWidth level blockWidth := by
  let marginDenominator := stepMarginDenominator level denominator
  have marginPositive : 0 < marginDenominator :=
    stepMarginDenominator_positive level denominator denominatorPositive
  have marginProper : marginDenominator - 1 < marginDenominator := by omega
  have growth := Growth.eventually_mul_two_pow_rational_le_shannonScale
    (stepOverheadConstant denominator) 10 (marginDenominator - 1)
    marginDenominator marginPositive marginProper
  obtain ⟨cutoff, pastCutoff⟩ := Filter.eventually_atTop.1 growth
  apply Filter.eventually_atTop.2
  refine ⟨max cutoff (max 1 (4 * denominator)),
    fun blockWidth blockLarge copies copiesPositive copiesBound => ?_⟩
  have blockPositive : 0 < blockWidth := by omega
  have inputPastCutoff : cutoff <= stepInputWidth level blockWidth := by
    have blockPast : cutoff <= blockWidth := by omega
    unfold stepInputWidth
    omega
  have growthBound := pastCutoff (stepInputWidth level blockWidth)
    inputPastCutoff
  exact step_overhead_le_of_growth level numerator denominator blockWidth
    copies levelAtLeastTwo denominatorPositive rateBelowLevel (by omega)
    copiesPositive copiesBound
    (by simpa [stepCommonExponent, marginDenominator] using growthBound)

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
  have exponentMonotone : numerator * inputWidth / denominator <=
      numerator * paddedWidth / denominator :=
    Nat.div_le_div_right (Nat.mul_le_mul_left numerator fits)
  have paddedCopiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator) := by
    unfold rationalCopyBudget at copiesBound
    exact copiesBound.trans <| Nat.pow_le_pow_right (by omega) <| by
      simpa only [paddedWidth, nextEqualBlockWidth] using exponentMonotone
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
  have exponentMonotone : numerator * inputWidth / denominator <=
      numerator * paddedWidth / denominator :=
    Nat.div_le_div_right (Nat.mul_le_mul_left numerator fits)
  have paddedCopiesBound : copies <=
      rationalCopyBudget numerator denominator paddedWidth := by
    unfold rationalCopyBudget at copiesBound ⊢
    exact copiesBound.trans
      (Nat.pow_le_pow_right (by omega) exponentMonotone)
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
