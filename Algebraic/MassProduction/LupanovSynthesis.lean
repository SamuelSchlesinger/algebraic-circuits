import Algebraic.MassProduction.LupanovCircuit
import Algebraic.MassProduction.UhligTheorem

/-!
# Sharp Lupanov synthesis

This module selects uniform parameters for the finite circuit in
`LupanovCircuit` and proves the coefficient-one one-copy estimate. It then
feeds that explicit synthesis family into the sharp Uhlig theorem.

All synthesis data is passed explicitly.  In particular, this module adds no
type-class instances.
-/

namespace Algebraic
namespace MassProduction
namespace LupanovSynthesis

open scoped BigOperators
open ShannonSynthesis

/-! ## Uniform sharp parameters -/

/-- Three logarithmic address variables.  The cap only handles the finite
initial segment. -/
def lupanovAddressWidth (inputs : Nat) : Nat :=
  min (3 * Nat.log 2 inputs) inputs

/-- Remaining data variables. -/
def lupanovDataWidth (inputs : Nat) : Nat :=
  inputs - lupanovAddressWidth inputs

/-- Pattern block length.  The lower clamp makes the finite construction
well-typed for every input length and disappears asymptotically. -/
def lupanovBlockSize (inputs : Nat) : Nat :=
  max 1 (inputs - 5 * Nat.log 2 inputs)

theorem lupanovAddressDataSum (inputs : Nat) :
    lupanovAddressWidth inputs + lupanovDataWidth inputs = inputs := by
  unfold lupanovDataWidth
  exact Nat.add_sub_of_le (min_le_right _ _)

theorem lupanovBlockSize_positive (inputs : Nat) :
    0 < lupanovBlockSize inputs := by
  unfold lupanovBlockSize
  omega

/-- A fixed multiple of the binary logarithm is eventually below the input
length. -/
theorem eventually_const_mul_log_le_self (constant : Nat) :
    ∀ᶠ inputs in Filter.atTop,
      constant * Nat.log 2 inputs <= inputs := by
  obtain ⟨cutoff, pastCutoff⟩ := Filter.eventually_atTop.1
    (Growth.eventually_const_mul_pow_le_two_pow constant 1)
  apply Filter.eventually_atTop.2
  refine ⟨2 ^ cutoff, fun inputs inputsLarge => ?_⟩
  have inputPositive : 0 < inputs :=
    (pow_pos (by omega : 0 < 2) cutoff).trans_le inputsLarge
  have logPastCutoff : cutoff <= Nat.log 2 inputs :=
    Nat.le_log_of_pow_le (by omega) inputsLarge
  calc
    constant * Nat.log 2 inputs =
        constant * (Nat.log 2 inputs) ^ 1 := by simp
    _ <= 2 ^ Nat.log 2 inputs := pastCutoff _ logPastCutoff
    _ <= inputs := Nat.pow_log_le_self 2 (Nat.ne_of_gt inputPositive)

theorem lupanov_parameters_eventually :
    ∀ᶠ inputs in Filter.atTop,
      5 * Nat.log 2 inputs < inputs /\
      lupanovAddressWidth inputs = 3 * Nat.log 2 inputs /\
      lupanovDataWidth inputs = inputs - 3 * Nat.log 2 inputs /\
      lupanovBlockSize inputs = inputs - 5 * Nat.log 2 inputs := by
  filter_upwards [eventually_const_mul_log_le_self 6,
    Filter.eventually_ge_atTop 2] with inputs logBound inputsLarge
  have logPositive : 0 < Nat.log 2 inputs :=
    Nat.log_pos (by omega) inputsLarge
  have fiveLogStrict : 5 * Nat.log 2 inputs < inputs := by omega
  have threeLogBound : 3 * Nat.log 2 inputs <= inputs := by omega
  refine ⟨fiveLogStrict, ?_, ?_, ?_⟩
  · simp [lupanovAddressWidth, threeLogBound]
  · simp [lupanovDataWidth, lupanovAddressWidth, threeLogBound]
  · simp [lupanovBlockSize, Nat.one_le_iff_ne_zero,
      Nat.ne_of_gt (Nat.sub_pos_of_lt fiveLogStrict)]

/-! ## Finite arithmetic for the sharp estimate -/

theorem blockCount_mul_blockSize_le
    (addressWidth blockSize : Nat)
    (blockSizePositive : 0 < blockSize) :
    blockCount addressWidth blockSize * blockSize <=
      2 ^ addressWidth + blockSize := by
  have ceiling := CodeParameters.ceilDiv_le_div_add_one
    (2 ^ addressWidth) blockSize blockSizePositive
  calc
    blockCount addressWidth blockSize * blockSize <=
        ((2 ^ addressWidth) / blockSize + 1) * blockSize := by
      exact Nat.mul_le_mul_right blockSize ceiling
    _ = ((2 ^ addressWidth) / blockSize) * blockSize + blockSize := by
      ring
    _ <= 2 ^ addressWidth + blockSize := by
      gcongr
      exact Nat.div_mul_le_self _ _

/-- After selecting the classical logarithmic parameters, every term except
the data-fiber term is smaller by at least three logarithmic powers. -/
theorem parameterCostBound_le
    (inputs : Nat)
    (fiveLogStrict : 5 * Nat.log 2 inputs < inputs) :
    costBound
        (3 * Nat.log 2 inputs)
        (inputs - 3 * Nat.log 2 inputs)
        (inputs - 5 * Nat.log 2 inputs) <=
      blockCount (3 * Nat.log 2 inputs)
          (inputs - 5 * Nat.log 2 inputs) *
            2 ^ (inputs - 3 * Nat.log 2 inputs) +
        4 * inputs ^ 3 +
          10 * inputs * 2 ^ (inputs - 3 * Nat.log 2 inputs) := by
  let logarithm := Nat.log 2 inputs
  let addressWidth := 3 * logarithm
  let dataWidth := inputs - 3 * logarithm
  let blockSize := inputs - 5 * logarithm
  let blocks := blockCount addressWidth blockSize
  let dataPower := 2 ^ dataWidth
  have inputsPositive : 0 < inputs := by omega
  have blockSizePositive : 0 < blockSize := by
    dsimp [blockSize, logarithm]
    exact Nat.sub_pos_of_lt fiveLogStrict
  have threeLogFits : 3 * logarithm <= inputs := by
    dsimp [logarithm]
    omega
  have addressData : addressWidth + dataWidth = inputs := by
    dsimp [addressWidth, dataWidth]
    exact Nat.add_sub_of_le threeLogFits
  have powerLogBound : 2 ^ logarithm <= inputs := by
    dsimp [logarithm]
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt inputsPositive)
  have addressPowerBound : 2 ^ addressWidth <= inputs ^ 3 := by
    dsimp [addressWidth]
    rw [Nat.mul_comm 3 logarithm, pow_mul]
    exact Nat.pow_le_pow_left powerLogBound 3
  have blockCapacity : blocks * blockSize <= 2 ^ addressWidth + blockSize := by
    dsimp [blocks]
    exact blockCount_mul_blockSize_le addressWidth blockSize blockSizePositive
  have blockLeCapacity : blocks <= blocks * blockSize := by
    exact Nat.le_mul_of_pos_right blocks blockSizePositive
  have blockExponentLeData : blockSize <= dataWidth := by
    dsimp [blockSize, dataWidth]
    omega
  have splitPower : 2 ^ addressWidth * dataPower = 2 ^ inputs := by
    dsimp [dataPower]
    rw [← Nat.pow_add, addressData]
  have shiftedPower : 2 ^ addressWidth * 2 ^ blockSize =
      2 ^ logarithm * dataPower := by
    dsimp [addressWidth, blockSize, dataWidth, dataPower]
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have addressBlockTerm :
      (2 ^ addressWidth + blockSize) * 2 ^ blockSize <=
        2 * inputs * dataPower := by
    calc
      (2 ^ addressWidth + blockSize) * 2 ^ blockSize =
          2 ^ addressWidth * 2 ^ blockSize +
            blockSize * 2 ^ blockSize := by ring
      _ <= inputs * dataPower + inputs * dataPower := by
        apply Nat.add_le_add
        · rw [shiftedPower]
          exact Nat.mul_le_mul_right dataPower powerLogBound
        · exact Nat.mul_le_mul
            (Nat.sub_le inputs _) (Nat.pow_le_pow_right (by omega)
              blockExponentLeData)
      _ = 2 * inputs * dataPower := by ring
  have leftTermBound :
      blocks * (2 ^ blockSize * blockSize) <=
        2 * inputs * dataPower := by
    calc
      blocks * (2 ^ blockSize * blockSize) =
          (blocks * blockSize) * 2 ^ blockSize := by ring
      _ <= (2 ^ addressWidth + blockSize) * 2 ^ blockSize := by
        gcongr
      _ <= 2 * inputs * dataPower := addressBlockTerm
  have finalTermBound :
      2 * (blocks * 2 ^ blockSize) <=
        4 * inputs * dataPower := by
    calc
      2 * (blocks * 2 ^ blockSize) <=
          2 * ((blocks * blockSize) * 2 ^ blockSize) := by
        gcongr
      _ <= 2 * ((2 ^ addressWidth + blockSize) * 2 ^ blockSize) := by
        gcongr
      _ <= 2 * (2 * inputs * dataPower) := by
        gcongr
      _ = 4 * inputs * dataPower := by ring
  have dataMintermBound : 4 * dataPower <= 4 * inputs * dataPower := by
    have oneLeInputs : 1 <= inputs := by omega
    simpa only [Nat.mul_assoc, Nat.mul_one] using
      Nat.mul_le_mul_right dataPower (Nat.mul_le_mul_left 4 oneLeInputs)
  change costBound addressWidth dataWidth blockSize <= _
  change _ <= blocks * dataPower + 4 * inputs ^ 3 +
    10 * inputs * dataPower
  unfold costBound bankWidth patternCount
  calc
    4 * 2 ^ addressWidth + 4 * dataPower +
          blocks * (2 ^ blockSize * blockSize) +
        blocks * dataPower + 2 * (blocks * 2 ^ blockSize) <=
        4 * inputs ^ 3 + 4 * inputs * dataPower +
          2 * inputs * dataPower + blocks * dataPower +
            4 * inputs * dataPower := by
      gcongr
    _ = blocks * dataPower + 4 * inputs ^ 3 +
        10 * inputs * dataPower := by ring

/-- Finite leading-term estimate.  If the block length is close enough to
the full input width at precision `precision`, the data-fiber bank contributes
coefficient one plus an explicitly lower-order term. -/
theorem scaledMainTerm_le
    (precision inputs : Nat)
    (fiveLogStrict : 5 * Nat.log 2 inputs < inputs)
    (removedSmall :
      (precision + 1) * (5 * Nat.log 2 inputs) <= inputs) :
    precision * inputs *
          (blockCount (3 * Nat.log 2 inputs)
              (inputs - 5 * Nat.log 2 inputs) *
            2 ^ (inputs - 3 * Nat.log 2 inputs)) <=
      (precision + 1) * 2 ^ inputs +
        (precision + 1) * inputs *
          2 ^ (inputs - 3 * Nat.log 2 inputs) := by
  let logarithm := Nat.log 2 inputs
  let addressWidth := 3 * logarithm
  let dataWidth := inputs - 3 * logarithm
  let blockSize := inputs - 5 * logarithm
  let blocks := blockCount addressWidth blockSize
  let dataPower := 2 ^ dataWidth
  have blockSizePositive : 0 < blockSize := by
    dsimp [blockSize, logarithm]
    exact Nat.sub_pos_of_lt fiveLogStrict
  have threeLogFits : addressWidth <= inputs := by
    dsimp [addressWidth, logarithm]
    omega
  have addressData : addressWidth + dataWidth = inputs := by
    dsimp [dataWidth]
    exact Nat.add_sub_of_le threeLogFits
  have blockCapacity : blocks * blockSize <=
      2 ^ addressWidth + blockSize := by
    dsimp [blocks]
    exact blockCount_mul_blockSize_le addressWidth blockSize blockSizePositive
  have precisionInputLeBlock :
      precision * inputs <= (precision + 1) * blockSize := by
    dsimp [blockSize, logarithm]
    rw [Nat.mul_sub_left_distrib]
    apply Nat.le_sub_of_add_le
    calc
      precision * inputs +
            (precision + 1) * (5 * Nat.log 2 inputs) <=
          precision * inputs + inputs := by gcongr
      _ = (precision + 1) * inputs := by ring
  have splitPower : 2 ^ addressWidth * dataPower = 2 ^ inputs := by
    dsimp [dataPower]
    rw [← Nat.pow_add, addressData]
  change precision * inputs * (blocks * dataPower) <= _
  change _ <= (precision + 1) * 2 ^ inputs +
    (precision + 1) * inputs * dataPower
  calc
    precision * inputs * (blocks * dataPower) <=
        (precision + 1) * blockSize * (blocks * dataPower) := by
      gcongr
    _ = (precision + 1) * (blocks * blockSize) * dataPower := by
      ring
    _ <= (precision + 1) *
        (2 ^ addressWidth + blockSize) * dataPower := by
      gcongr
    _ = (precision + 1) * (2 ^ addressWidth * dataPower) +
        (precision + 1) * blockSize * dataPower := by ring
    _ <= (precision + 1) * 2 ^ inputs +
        (precision + 1) * inputs * dataPower := by
      rw [splitPower]
      gcongr
      exact Nat.sub_le _ _

/-- Three logarithmic powers absorb a fixed coefficient times `n^2`. -/
theorem const_mul_square_mul_two_pow_sub_three_log_le
    (constant inputs : Nat)
    (constantFits : 8 * constant <= inputs)
    (threeLogFits : 3 * Nat.log 2 inputs <= inputs) :
    constant * inputs ^ 2 *
        2 ^ (inputs - 3 * Nat.log 2 inputs) <=
      2 ^ inputs := by
  let logarithm := Nat.log 2 inputs
  let logarithmicPower := 2 ^ logarithm
  have inputBelowDouble : inputs < 2 * logarithmicPower := by
    have bound := Nat.lt_pow_succ_log_self (by omega : 1 < 2) inputs
    simpa only [pow_succ, logarithm, logarithmicPower, Nat.mul_comm] using bound
  have fourConstantLePower : 4 * constant <= logarithmicPower := by
    omega
  have inputLeDouble : inputs <= 2 * logarithmicPower :=
    Nat.le_of_lt inputBelowDouble
  have polynomialBound :
      constant * inputs ^ 2 <= logarithmicPower ^ 3 := by
    calc
      constant * inputs ^ 2 <=
          constant * (2 * logarithmicPower) ^ 2 := by gcongr
      _ = (4 * constant) * logarithmicPower ^ 2 := by ring
      _ <= logarithmicPower * logarithmicPower ^ 2 := by gcongr
      _ = logarithmicPower ^ 3 := by ring
  have powerCube : logarithmicPower ^ 3 =
      2 ^ (3 * Nat.log 2 inputs) := by
    dsimp [logarithmicPower, logarithm]
    rw [Nat.mul_comm 3, pow_mul]
  calc
    constant * inputs ^ 2 *
          2 ^ (inputs - 3 * Nat.log 2 inputs) <=
        logarithmicPower ^ 3 *
          2 ^ (inputs - 3 * Nat.log 2 inputs) := by gcongr
    _ = 2 ^ (3 * Nat.log 2 inputs) *
          2 ^ (inputs - 3 * Nat.log 2 inputs) := by rw [powerCube]
    _ = 2 ^ inputs := by
      rw [← Nat.pow_add]
      congr 1
      omega

/-! ## The coefficient-one synthesis family -/

/-- Uniform width-indexed form of the finite Lupanov circuit. -/
noncomputable def lupanovCircuit
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    Circuit DeMorgan.signature inputs
      (synthesisGateCount
        (reindexFunction (lupanovAddressDataSum inputs) function)
        (lupanovBlockSize inputs)) 1 :=
  (circuit
      (addressWidth := lupanovAddressWidth inputs)
      (dataWidth := lupanovDataWidth inputs)
      (reindexFunction (lupanovAddressDataSum inputs) function)
      (lupanovBlockSize inputs)).castCounts
    (lupanovAddressDataSum inputs) rfl rfl

@[simp] theorem lupanovCircuit_eval
    (inputs : Nat)
    (function : ScalarFunction Bool inputs)
    (input : Fin inputs -> Bool) :
    (lupanovCircuit inputs function).eval DeMorgan.interpretation input 0 =
      function input := by
  rw [lupanovCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, id_eq]
  rw [circuit_eval (lupanovBlockSize_positive inputs)]
  unfold reindexFunction
  apply congrArg function
  funext index
  simp [Function.comp_apply]

theorem lupanovCircuit_computes
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    (lupanovCircuit inputs function).Computes DeMorgan.interpretation
      (scalarTarget function) := by
  intro input
  funext output
  have outputZero : output = 0 := Fin.eq_zero output
  subst output
  exact lupanovCircuit_eval inputs function input

theorem lupanovCircuit_cost_le
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    (lupanovCircuit inputs function).cost DeMorgan.standardCost <=
      costBound (lupanovAddressWidth inputs) (lupanovDataWidth inputs)
        (lupanovBlockSize inputs) := by
  rw [lupanovCircuit, Circuit.cost_castCounts]
  exact circuit_cost_le _ _

/-- Explicit one-copy synthesis data at every width. -/
noncomputable def lupanovScalarSynthesis
    (inputs : Nat) : ScalarSynthesis inputs where
  gateCount function :=
    synthesisGateCount
      (reindexFunction (lupanovAddressDataSum inputs) function)
      (lupanovBlockSize inputs)
  circuit := lupanovCircuit inputs
  computes := lupanovCircuit_computes inputs

/-- The Lupanov family as explicit dependent data, not a typeclass. -/
noncomputable def lupanovFamily : ScalarSynthesisFamily :=
  lupanovScalarSynthesis

@[simp] theorem lupanovFamily_circuit
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    (lupanovFamily inputs).circuit function =
      lupanovCircuit inputs function := rfl

/-- Lupanov's coefficient-one one-copy upper bound, in the exact integral
form consumed by the Uhlig recursion. -/
theorem lupanovFamily_hasSharpOneCopyCost :
    UhligTheorem.HasSharpOneCopyCost lupanovFamily := by
  intro precision precisionPositive
  let scaledPrecision := 4 * precision
  let logarithmicConstant := 11 * scaledPrecision + 1
  have parametersEventually := lupanov_parameters_eventually
  have removedEventually :=
    eventually_const_mul_log_le_self (5 * (scaledPrecision + 1))
  have polynomialEventually :=
    Growth.eventually_const_mul_pow_le_two_pow
      (4 * scaledPrecision) 4
  have sizeEventually :
      ∀ᶠ inputs in Filter.atTop,
        8 * logarithmicConstant <= inputs :=
    Filter.eventually_ge_atTop (8 * logarithmicConstant)
  have sharpEventually :
      ∀ᶠ inputs in Filter.atTop,
        forall function : ScalarFunction Bool inputs,
          precision *
                ((lupanovFamily inputs).circuit function).cost
                  DeMorgan.standardCost *
              inputs <=
            (precision + 1) * 2 ^ inputs := by
    filter_upwards [parametersEventually, removedEventually,
      polynomialEventually, sizeEventually] with inputs parameters
        removedBound polynomialBound sizeBound
    rintro function
    rcases parameters with
      ⟨fiveLogStrict, addressWidthIdentity, dataWidthIdentity,
        blockSizeIdentity⟩
    have inputsPositive : 0 < inputs := by omega
    have threeLogFits : 3 * Nat.log 2 inputs <= inputs := by omega
    have removedSmall :
        (scaledPrecision + 1) * (5 * Nat.log 2 inputs) <= inputs := by
      calc
        (scaledPrecision + 1) * (5 * Nat.log 2 inputs) =
            (5 * (scaledPrecision + 1)) * Nat.log 2 inputs := by ring
        _ <= inputs := removedBound
    have selectedCost := lupanovCircuit_cost_le inputs function
    conv_rhs at selectedCost =>
      rw [addressWidthIdentity, dataWidthIdentity, blockSizeIdentity]
    have constructionCost := selectedCost.trans
      (parameterCostBound_le inputs fiveLogStrict)
    let blocks := blockCount (3 * Nat.log 2 inputs)
      (inputs - 5 * Nat.log 2 inputs)
    let dataPower := 2 ^ (inputs - 3 * Nat.log 2 inputs)
    let mainTerm := blocks * dataPower
    have mainBound :
        scaledPrecision * inputs * mainTerm <=
          (scaledPrecision + 1) * 2 ^ inputs +
            (scaledPrecision + 1) * inputs * dataPower := by
      dsimp [mainTerm, blocks, dataPower]
      exact scaledMainTerm_le scaledPrecision inputs fiveLogStrict
        removedSmall
    have inputLeSquare : inputs <= inputs ^ 2 := by
      simpa only [pow_two] using
        Nat.le_mul_of_pos_left inputs inputsPositive
    have lowerOrderMerge :
        (scaledPrecision + 1) * inputs * dataPower +
            10 * scaledPrecision * inputs ^ 2 * dataPower <=
          (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
      calc
        (scaledPrecision + 1) * inputs * dataPower +
              10 * scaledPrecision * inputs ^ 2 * dataPower <=
            (scaledPrecision + 1) * inputs ^ 2 * dataPower +
              10 * scaledPrecision * inputs ^ 2 * dataPower := by
          gcongr
        _ = (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
          ring
    have scaledCost :
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
          (scaledPrecision + 1) * 2 ^ inputs +
            4 * scaledPrecision * inputs ^ 4 +
              (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
      calc
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
            scaledPrecision * inputs *
              (mainTerm + 4 * inputs ^ 3 +
                10 * inputs * dataPower) := by
          exact Nat.mul_le_mul_left (scaledPrecision * inputs) <| by
            simpa only [mainTerm, blocks, dataPower] using constructionCost
        _ = scaledPrecision * inputs * mainTerm +
              4 * scaledPrecision * inputs ^ 4 +
                10 * scaledPrecision * inputs ^ 2 * dataPower := by ring
        _ <= ((scaledPrecision + 1) * 2 ^ inputs +
              (scaledPrecision + 1) * inputs * dataPower) +
            4 * scaledPrecision * inputs ^ 4 +
              10 * scaledPrecision * inputs ^ 2 * dataPower := by
          gcongr
        _ = (scaledPrecision + 1) * 2 ^ inputs +
            4 * scaledPrecision * inputs ^ 4 +
              ((scaledPrecision + 1) * inputs * dataPower +
                10 * scaledPrecision * inputs ^ 2 * dataPower) := by ring
        _ <= (scaledPrecision + 1) * 2 ^ inputs +
            4 * scaledPrecision * inputs ^ 4 +
              (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
          gcongr
    have logarithmicError :
        (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower <=
          2 ^ inputs := by
      dsimp [dataPower]
      exact const_mul_square_mul_two_pow_sub_three_log_le
        (11 * scaledPrecision + 1) inputs
        (by simpa only [logarithmicConstant] using sizeBound)
        threeLogFits
    have scaledTotal :
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
          (scaledPrecision + 3) * 2 ^ inputs := by
      calc
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
            (scaledPrecision + 1) * 2 ^ inputs +
              4 * scaledPrecision * inputs ^ 4 +
                (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower :=
          scaledCost
        _ <= (scaledPrecision + 1) * 2 ^ inputs +
            2 ^ inputs + 2 ^ inputs := by gcongr
        _ = (scaledPrecision + 3) * 2 ^ inputs := by ring
    apply le_of_mul_le_mul_left (a := 4) _ (by omega)
    calc
      4 * (precision *
              ((lupanovFamily inputs).circuit function).cost
                DeMorgan.standardCost * inputs) =
          scaledPrecision * inputs *
            (lupanovCircuit inputs function).cost
              DeMorgan.standardCost := by
        dsimp [scaledPrecision, lupanovFamily, lupanovScalarSynthesis]
        ring
      _ <= (scaledPrecision + 3) * 2 ^ inputs := scaledTotal
      _ <= 4 * ((precision + 1) * 2 ^ inputs) := by
        have coefficientBound :
            scaledPrecision + 3 <= 4 * (precision + 1) := by
          dsimp [scaledPrecision]
          omega
        calc
          (scaledPrecision + 3) * 2 ^ inputs <=
              (4 * (precision + 1)) * 2 ^ inputs :=
            Nat.mul_le_mul_right _ coefficientBound
          _ = 4 * ((precision + 1) * 2 ^ inputs) := by ring
  exact Filter.eventually_atTop.1 sharpEventually

/-!
The following is the unconditional sharp Uhlig theorem.  It combines the
coefficient-one Lupanov family above with the exact recursive two-copy circuit
from `UhligRecursion`.  Its discrete `IsUhligDepth` premise is precisely the
denominator-free form of `depth(n) = o(n / log n)`, so it covers every batch
size `1 <= t <= 2 ^ depth(n)` with asymptotic leading coefficient one.
-/
theorem uhlig_massProduction
    (depth : Nat -> Nat)
    (depthSmall : UhligTheorem.IsUhligDepth depth) :
    UhligTheorem.HasSharpMassProduction depth :=
  UhligTheorem.uhlig_of_sharp_one_copy lupanovFamily
    lupanovFamily_hasSharpOneCopyCost depth depthSmall

end LupanovSynthesis
end MassProduction
end Algebraic
