import Algebraic.MassProduction.EqualBlockFiniteStep
import Algebraic.MassProduction.Growth
import Algebraic.MassProduction.InputSplit

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
