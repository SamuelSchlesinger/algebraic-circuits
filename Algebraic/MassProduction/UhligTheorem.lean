import Algebraic.MassProduction.Growth
import Algebraic.MassProduction.UhligRecursion

/-!
# Uhlig's sharp mass-production theorem

This module turns the exact two-copy recursion into the classical
`2 ^ o(n / log n)` statement.  The asymptotic hypothesis is expressed by
ordinary natural-number inequalities, and synthesis data is passed explicitly
rather than through typeclass instances.

The first part of the file establishes the finite and polynomial estimates
needed by the asymptotic argument.  The final sharp theorem is parameterized
by a sharp one-copy synthesis family; the separate Lupanov module discharges
that premise.
-/

namespace Algebraic
namespace MassProduction
namespace UhligTheorem

open Filter
open UhligCircuit
open UhligRecursion

/-- We spend twice the binary logarithm of the ambient input length per
two-copy layer.  This makes the ordinary resource population at least the
ambient input length while still costing only `O(log n)` variables per
layer. -/
def uhligPrefixWidth (inputs : Nat) : Nat :=
  2 * Nat.log 2 inputs

/-- Inputs left for the terminal one-copy synthesis. -/
def uhligBaseWidth (depth inputs : Nat) : Nat :=
  inputs - depth * uhligPrefixWidth inputs

theorem two_pow_uhligPrefixWidth_le_square
    (inputs : Nat) (inputsPositive : 0 < inputs) :
    2 ^ uhligPrefixWidth inputs <= inputs ^ 2 := by
  unfold uhligPrefixWidth
  rw [Nat.mul_comm 2, pow_mul]
  exact Nat.pow_le_pow_left
    (Nat.pow_log_le_self 2 (Nat.ne_of_gt inputsPositive)) 2

theorem input_le_two_pow_uhligPrefixWidth
    (inputs : Nat) (inputsLarge : 2 <= inputs) :
    inputs <= 2 ^ uhligPrefixWidth inputs := by
  let logarithmicPower := 2 ^ Nat.log 2 inputs
  have logarithmicPowerAtLeastTwo : 2 <= logarithmicPower := by
    have logPositive : 0 < Nat.log 2 inputs :=
      Nat.log_pos (by omega) inputsLarge
    dsimp [logarithmicPower]
    exact Nat.one_lt_two_pow_iff.mpr (Nat.ne_of_gt logPositive)
  have inputBelowDouble :
      inputs < logarithmicPower * 2 := by
    have bound := Nat.lt_pow_succ_log_self (by omega : 1 < 2) inputs
    simpa only [pow_succ, logarithmicPower, Nat.mul_comm] using bound
  calc
    inputs <= logarithmicPower * 2 := Nat.le_of_lt inputBelowDouble
    _ <= logarithmicPower * logarithmicPower := by gcongr
    _ = 2 ^ uhligPrefixWidth inputs := by
      unfold uhligPrefixWidth logarithmicPower
      rw [Nat.mul_comm 2, pow_mul, pow_two]

theorem uhligPrefixWidth_le_twice
    (inputs : Nat) :
    uhligPrefixWidth inputs <= 2 * inputs := by
  unfold uhligPrefixWidth
  exact Nat.mul_le_mul_left 2 (Nat.log_le_self 2 inputs)

/-- Expanded polynomial for the cost of one pair-factored Uhlig layer. -/
theorem layerOverheadEnvelope_eq
    (prefixWidth suffixWidth : Nat) :
    layerOverheadEnvelope prefixWidth suffixWidth =
      let sources := 2 ^ prefixWidth
      let resources := sources + 1
      resources *
          (suffixWidth *
            (2 * sources * resources * (prefixWidth + 1))) +
        2 *
          (sources *
              (sources *
                  (4 * prefixWidth + 4 * resources + 2) +
                sources) +
            sources) := by
  have sourceCount := prefixCount_eq prefixWidth
  have resourceCountIdentity := resourceCount_eq prefixWidth
  unfold layerOverheadEnvelope routedSuffixCostBound
    sharedDecodedCostBound candidateRowCostBound candidateDecodedCostBound
  unfold resourceCount at resourceCountIdentity
  simp only
  rw [resourceCount_eq, sourceCount, resourceCountIdentity]
  ring

/-- With the chosen logarithmic prefix, the entire pair-factored layer
overhead is bounded by a fixed degree-eight monomial. -/
theorem layerOverheadEnvelope_uhligPrefixWidth_le
    (inputs : Nat) (inputsLarge : 2 <= inputs) :
    layerOverheadEnvelope (uhligPrefixWidth inputs) inputs <=
      64 * inputs ^ 8 := by
  let prefixWidth := uhligPrefixWidth inputs
  let sources := 2 ^ prefixWidth
  let resources := sources + 1
  have inputsPositive : 0 < inputs := by omega
  have squarePositive : 0 < inputs ^ 2 := pow_pos inputsPositive 2
  have sourcesBound : sources <= inputs ^ 2 := by
    dsimp [sources, prefixWidth]
    exact two_pow_uhligPrefixWidth_le_square inputs inputsPositive
  have resourcesBound : resources <= 2 * inputs ^ 2 := by
    dsimp [resources]
    calc
      sources + 1 <= inputs ^ 2 + 1 := Nat.add_le_add_right sourcesBound 1
      _ <= 2 * inputs ^ 2 := by omega
  have prefixBound : prefixWidth <= 2 * inputs := by
    dsimp [prefixWidth]
    exact uhligPrefixWidth_le_twice inputs
  have prefixSuccessorBound : prefixWidth + 1 <= 3 * inputs := by omega
  have routedBound :
      2 * sources * resources * (prefixWidth + 1) <=
        12 * inputs ^ 5 := by
    calc
      2 * sources * resources * (prefixWidth + 1) <=
          2 * inputs ^ 2 * (2 * inputs ^ 2) * (3 * inputs) := by
        gcongr
      _ = 12 * inputs ^ 5 := by ring
  have candidateBound :
      4 * prefixWidth + 4 * resources + 2 <= 18 * inputs ^ 2 := by
    have inputLeSquare : inputs <= inputs ^ 2 := by
      simpa only [pow_two] using Nat.le_mul_of_pos_left inputs inputsPositive
    calc
      4 * prefixWidth + 4 * resources + 2 <=
          4 * (2 * inputs) + 4 * (2 * inputs ^ 2) + 2 := by gcongr
      _ <= 18 * inputs ^ 2 := by omega
  have squareLeSixth : inputs ^ 2 <= inputs ^ 6 :=
    Nat.pow_le_pow_right inputsPositive (by omega)
  have fourthLeSixth : inputs ^ 4 <= inputs ^ 6 :=
    Nat.pow_le_pow_right inputsPositive (by omega)
  have decodedBound :
      sources * (sources *
          (4 * prefixWidth + 4 * resources + 2) + sources) + sources <=
        20 * inputs ^ 6 := by
    calc
      sources * (sources *
            (4 * prefixWidth + 4 * resources + 2) + sources) + sources <=
          inputs ^ 2 *
              (inputs ^ 2 * (18 * inputs ^ 2) + inputs ^ 2) +
            inputs ^ 2 := by gcongr
      _ = 18 * inputs ^ 6 + inputs ^ 4 + inputs ^ 2 := by ring
      _ <= 20 * inputs ^ 6 := by omega
  have sixthLeEighth : inputs ^ 6 <= inputs ^ 8 :=
    Nat.pow_le_pow_right inputsPositive (by omega)
  rw [layerOverheadEnvelope_eq]
  dsimp only
  change resources *
        (inputs * (2 * sources * resources * (prefixWidth + 1))) +
      2 *
        (sources *
            (sources * (4 * prefixWidth + 4 * resources + 2) + sources) +
          sources) <= _
  calc
    resources *
          (inputs * (2 * sources * resources * (prefixWidth + 1))) +
        2 *
          (sources *
              (sources * (4 * prefixWidth + 4 * resources + 2) + sources) +
            sources) <=
      (2 * inputs ^ 2) * (inputs * (12 * inputs ^ 5)) +
        2 * (20 * inputs ^ 6) := by gcongr
    _ = 24 * inputs ^ 8 + 40 * inputs ^ 6 := by ring
    _ <= 64 * inputs ^ 8 := by omega

/-! ## Finite end-to-end theorem -/

/-- Exact finite Uhlig construction for every positive sub-batch of the
power-of-two batch produced by the recursion. -/
theorem exists_finite_uhlig_circuit
    (prefixWidth baseWidth depth : Nat)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth))
    (copies : Nat)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <= 2 ^ depth) :
    exists gates,
      exists circuit : Circuit DeMorgan.signature
          (copies * recursiveWidth prefixWidth baseWidth depth) gates copies,
        circuit.Computes DeMorgan.interpretation
            (directProduct function copies) /\
          circuit.cost DeMorgan.standardCost <=
            resourceCount prefixWidth ^ depth *
              (baseBound + depth *
                layerOverheadEnvelope prefixWidth
                  (recursiveWidth prefixWidth baseWidth depth)) := by
  let fullCircuit := recursiveCircuit prefixWidth baseWidth base depth function
  have copiesLeFull : copies <= recursiveCopies depth := by
    rw [recursiveCopies_eq_two_pow]
    exact copiesBound
  let circuit := fullCircuit.takeDirectProductPrefix
    copies copiesPositive copiesLeFull
  refine ⟨_, circuit, ?_, ?_⟩
  · exact Circuit.takeDirectProductPrefix_computes fullCircuit function
      (recursiveCircuit_computes prefixWidth baseWidth base depth function)
      copiesPositive copiesLeFull
  · simpa [circuit] using
      recursiveCircuit_cost_le_closed prefixWidth baseWidth base baseBound
        baseCost depth (recursiveWidth prefixWidth baseWidth depth) le_rfl
        function

/-- Width-transported form of the finite construction. -/
theorem exists_finite_uhlig_circuit_at_width
    (prefixWidth baseWidth depth inputs : Nat)
    (widthIdentity :
      recursiveWidth prefixWidth baseWidth depth = inputs)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (function : ScalarFunction Bool inputs)
    (copies : Nat)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <= 2 ^ depth) :
    exists gates,
      exists circuit : Circuit DeMorgan.signature
          (copies * inputs) gates copies,
        circuit.Computes DeMorgan.interpretation
            (directProduct function copies) /\
          circuit.cost DeMorgan.standardCost <=
            resourceCount prefixWidth ^ depth *
              (baseBound + depth *
                layerOverheadEnvelope prefixWidth inputs) := by
  subst inputs
  exact exists_finite_uhlig_circuit prefixWidth baseWidth depth base
    baseBound baseCost function copies copiesPositive copiesBound

/-- Width-indexed one-copy synthesis data.  This is a dependent function, not
a typeclass, so using it introduces no synthesis instances. -/
abbrev ScalarSynthesisFamily :=
  (width : Nat) -> ScalarSynthesis width

/-- Denominator-free formulation of a sharp one-copy upper bound.  For every
positive integer precision `q`, the normalized coefficient is eventually at
most `(q + 1) / q`. -/
def HasSharpOneCopyCost (family : ScalarSynthesisFamily) : Prop :=
  forall precision : Nat, 0 < precision ->
    exists cutoff : Nat,
      forall width : Nat, cutoff <= width ->
        forall function : ScalarFunction Bool width,
          precision *
                (((family width).circuit function).cost
                  DeMorgan.standardCost) *
              width <=
            (precision + 1) * 2 ^ width

/-- Uniform integral bound extracted from one normalized sharp estimate. -/
def normalizedBaseBound (precision width : Nat) : Nat :=
  ((precision + 1) * 2 ^ width) / (precision * width)

theorem normalizedBaseBound_spec
    (precision width : Nat) :
    precision * normalizedBaseBound precision width * width <=
      (precision + 1) * 2 ^ width := by
  unfold normalizedBaseBound
  have divisionBound := Nat.mul_div_le
    ((precision + 1) * 2 ^ width) (precision * width)
  calc
    precision *
          (((precision + 1) * 2 ^ width) / (precision * width)) * width =
        (precision * width) *
          (((precision + 1) * 2 ^ width) / (precision * width)) := by ring
    _ <= (precision + 1) * 2 ^ width := divisionBound

theorem circuit_cost_le_normalizedBaseBound
    (family : ScalarSynthesisFamily)
    (precision width : Nat)
    (precisionPositive : 0 < precision)
    (widthPositive : 0 < width)
    (function : ScalarFunction Bool width)
    (sharpBound :
      precision *
            (((family width).circuit function).cost
              DeMorgan.standardCost) * width <=
        (precision + 1) * 2 ^ width) :
    ((family width).circuit function).cost DeMorgan.standardCost <=
      normalizedBaseBound precision width := by
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos precisionPositive widthPositive)).2
  simpa only [normalizedBaseBound, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using sharpBound

/-- Exact discrete reading of `depth(n) = o(n / log n)`.  Quantifying over
every fixed positive multiplier avoids division and real-valued side
conditions. -/
def IsUhligDepth (depth : Nat -> Nat) : Prop :=
  forall multiplier : Nat, 0 < multiplier ->
    Filter.Eventually
      (fun inputs =>
        multiplier * depth inputs * Nat.log 2 inputs <= inputs)
      atTop

/-- Sharp mass production through the copy budget `2 ^ depth(n)`, stated
directly for minimum De Morgan cost. -/
def HasSharpMassProduction (depth : Nat -> Nat) : Prop :=
  forall precision : Nat, 0 < precision ->
    Filter.Eventually
      (fun inputs =>
        forall (function : ScalarFunction Bool inputs) (copies : Nat),
          0 < copies -> copies <= 2 ^ depth inputs ->
            (precision * inputs : ENat) *
                booleanMassComplexity function copies <=
              ((precision + 1) * 2 ^ inputs : Nat))
      atTop

/-! ## Finite leading-term arithmetic -/

theorem recursiveWidth_uhligBaseWidth
    (depth inputs : Nat)
    (blocksFit : depth * uhligPrefixWidth inputs <= inputs) :
    recursiveWidth (uhligPrefixWidth inputs)
        (uhligBaseWidth depth inputs) depth = inputs := by
  rw [recursiveWidth_eq]
  unfold uhligBaseWidth
  exact Nat.add_sub_of_le blocksFit

/-- Three coefficient losses are kept separate: the terminal sharp
synthesis, the extra resource per layer, and replacing the terminal width in
the denominator by the full width. -/
theorem precision_cube_mul_mainTerm_le
    (precision prefixWidth baseWidth depth baseBound : Nat)
    (baseSharp :
      precision * baseBound * baseWidth <=
        (precision + 1) * 2 ^ baseWidth)
    (resourceSmall :
      (precision + 1) * depth <= 2 ^ prefixWidth)
    (removedWidthSmall :
      precision * depth * prefixWidth <= baseWidth) :
    precision ^ 3 *
          (resourceCount prefixWidth ^ depth * baseBound) *
          (depth * prefixWidth + baseWidth) <=
      (precision + 1) ^ 3 *
        2 ^ (depth * prefixWidth + baseWidth) := by
  have denominatorBound :
      precision * (depth * prefixWidth + baseWidth) <=
        (precision + 1) * baseWidth := by
    nlinarith
  have baseAtFullWidth :
      precision ^ 2 * baseBound *
          (depth * prefixWidth + baseWidth) <=
        (precision + 1) ^ 2 * 2 ^ baseWidth := by
    calc
      precision ^ 2 * baseBound *
            (depth * prefixWidth + baseWidth) =
          precision * baseBound *
            (precision * (depth * prefixWidth + baseWidth)) := by ring
      _ <= precision * baseBound *
          ((precision + 1) * baseWidth) := by gcongr
      _ = (precision + 1) *
          (precision * baseBound * baseWidth) := by ring
      _ <= (precision + 1) *
          ((precision + 1) * 2 ^ baseWidth) := by gcongr
      _ = (precision + 1) ^ 2 * 2 ^ baseWidth := by ring
  have resourceSharp := precision_mul_resourcePower_le
    precision prefixWidth depth resourceSmall
  calc
    precision ^ 3 *
          (resourceCount prefixWidth ^ depth * baseBound) *
          (depth * prefixWidth + baseWidth) =
        (precision * resourceCount prefixWidth ^ depth) *
          (precision ^ 2 * baseBound *
            (depth * prefixWidth + baseWidth)) := by ring
    _ <= ((precision + 1) * (2 ^ prefixWidth) ^ depth) *
        ((precision + 1) ^ 2 * 2 ^ baseWidth) :=
      Nat.mul_le_mul resourceSharp baseAtFullWidth
    _ = (precision + 1) ^ 3 *
        2 ^ (depth * prefixWidth + baseWidth) := by
      rw [← pow_mul]
      rw [show prefixWidth * depth = depth * prefixWidth by ring]
      rw [Nat.pow_add]
      ring

/-- A convenient internal precision large enough to allocate half of the
final coefficient slack to the main term. -/
def internalPrecision (precision : Nat) : Nat :=
  16 * (precision + 1)

theorem internalPrecision_positive (precision : Nat) :
    0 < internalPrecision precision := by
  unfold internalPrecision
  positivity

theorem twice_mul_succ_cube_le
    (precision : Nat) :
    2 * precision * (internalPrecision precision + 1) ^ 3 <=
      (2 * precision + 1) * internalPrecision precision ^ 3 := by
  let internal := internalPrecision precision
  have internalPositive : 0 < internal := internalPrecision_positive precision
  have internalAtLeastPrecision : 14 * precision <= internal := by
    unfold internal internalPrecision
    omega
  have internalLeSquare : internal <= internal ^ 2 := by
    simpa only [pow_two] using
      Nat.le_mul_of_pos_left internal internalPositive
  have oneLeSquare : 1 <= internal ^ 2 := by
    exact (by omega : 1 <= internal).trans internalLeSquare
  have successorCubeBound :
      (internal + 1) ^ 3 <= internal ^ 3 + 7 * internal ^ 2 := by
    calc
      (internal + 1) ^ 3 =
          internal ^ 3 + 3 * internal ^ 2 + 3 * internal + 1 := by ring
      _ <= internal ^ 3 + 7 * internal ^ 2 := by omega
  change 2 * precision * (internal + 1) ^ 3 <=
    (2 * precision + 1) * internal ^ 3
  calc
    2 * precision * (internal + 1) ^ 3 <=
        2 * precision * (internal ^ 3 + 7 * internal ^ 2) := by gcongr
    _ = 2 * precision * internal ^ 3 +
        14 * precision * internal ^ 2 := by ring
    _ <= 2 * precision * internal ^ 3 +
        internal * internal ^ 2 := by gcongr
    _ = (2 * precision + 1) * internal ^ 3 := by ring

theorem mainTerm_with_allocated_slack
    (precision mainTerm inputs : Nat)
    (normalized :
      internalPrecision precision ^ 3 * mainTerm * inputs <=
        (internalPrecision precision + 1) ^ 3 * 2 ^ inputs) :
    2 * precision * mainTerm * inputs <=
      (2 * precision + 1) * 2 ^ inputs := by
  let internal := internalPrecision precision
  have internalPositive : 0 < internal := internalPrecision_positive precision
  have coefficient := twice_mul_succ_cube_le precision
  apply le_of_mul_le_mul_left (a := internal ^ 3) _ (pow_pos internalPositive 3)
  calc
    internal ^ 3 * (2 * precision * mainTerm * inputs) =
        2 * precision *
          (internal ^ 3 * mainTerm * inputs) := by ring
    _ <= 2 * precision *
        ((internal + 1) ^ 3 * 2 ^ inputs) := by
      gcongr
    _ = (2 * precision * (internal + 1) ^ 3) * 2 ^ inputs := by ring
    _ <= ((2 * precision + 1) * internal ^ 3) * 2 ^ inputs := by
      gcongr
    _ = internal ^ 3 *
        ((2 * precision + 1) * 2 ^ inputs) := by ring

theorem combine_main_and_overhead
    (precision cost mainTerm overhead inputs : Nat)
    (costBound : cost <= mainTerm + overhead)
    (mainBound :
      2 * precision * mainTerm * inputs <=
        (2 * precision + 1) * 2 ^ inputs)
    (overheadBound :
      2 * precision * inputs * overhead <= 2 ^ inputs) :
    precision * cost * inputs <=
      (precision + 1) * 2 ^ inputs := by
  apply le_of_mul_le_mul_left (a := 2) _ (by omega)
  calc
    2 * (precision * cost * inputs) =
        2 * precision * cost * inputs := by ring
    _ <= 2 * precision * (mainTerm + overhead) * inputs := by gcongr
    _ = 2 * precision * mainTerm * inputs +
        2 * precision * inputs * overhead := by ring
    _ <= (2 * precision + 1) * 2 ^ inputs + 2 ^ inputs :=
      Nat.add_le_add mainBound overheadBound
    _ = 2 * ((precision + 1) * 2 ^ inputs) := by ring

/-! ## Negligibility of the explicit overhead -/

theorem resourcePower_le_two_mul
    (prefixWidth depth : Nat)
    (depthSmall : 2 * depth <= 2 ^ prefixWidth) :
    resourceCount prefixWidth ^ depth <=
      2 * (2 ^ prefixWidth) ^ depth := by
  have bound := precision_mul_resourcePower_le
    1 prefixWidth depth (by simpa using depthSmall)
  simpa only [one_mul] using bound

theorem normalized_overhead_le_of_growth
    (precision inputs depth : Nat)
    (inputsLarge : 2 <= inputs)
    (depthLe : depth <= inputs)
    (resourceSmall :
      2 * depth <= 2 ^ uhligPrefixWidth inputs)
    (removedExponentSmall :
      uhligPrefixWidth inputs * depth <= inputs / 2)
    (polynomialAbsorbed :
      256 * precision * inputs ^ 10 <= 2 ^ (inputs / 2)) :
    2 * precision * inputs *
          (resourceCount (uhligPrefixWidth inputs) ^ depth *
            (depth *
              layerOverheadEnvelope (uhligPrefixWidth inputs) inputs)) <=
      2 ^ inputs := by
  have resourceBound := resourcePower_le_two_mul
    (uhligPrefixWidth inputs) depth resourceSmall
  have envelopeBound := layerOverheadEnvelope_uhligPrefixWidth_le
    inputs inputsLarge
  have exponentBound :
      inputs / 2 + uhligPrefixWidth inputs * depth <= inputs := by
    have twiceFloor : 2 * (inputs / 2) <= inputs := Nat.mul_div_le inputs 2
    omega
  calc
    2 * precision * inputs *
          (resourceCount (uhligPrefixWidth inputs) ^ depth *
            (depth *
              layerOverheadEnvelope (uhligPrefixWidth inputs) inputs)) <=
        2 * precision * inputs *
          ((2 * (2 ^ uhligPrefixWidth inputs) ^ depth) *
            (inputs * (64 * inputs ^ 8))) := by gcongr
    _ = (256 * precision * inputs ^ 10) *
        (2 ^ uhligPrefixWidth inputs) ^ depth := by ring
    _ <= 2 ^ (inputs / 2) *
        (2 ^ uhligPrefixWidth inputs) ^ depth := by gcongr
    _ = 2 ^ (inputs / 2 + uhligPrefixWidth inputs * depth) := by
      rw [← pow_mul, Nat.pow_add]
    _ <= 2 ^ inputs := Nat.pow_le_pow_right (by omega) exponentBound

/-- For every fixed coefficient precision, the complete explicit routing and
decoding overhead is eventually smaller than the reserved half-unit of
coefficient slack. -/
theorem eventually_normalized_overhead_le
    (depth : Nat -> Nat)
    (depthSmall : IsUhligDepth depth)
    (precision : Nat) :
    Filter.Eventually
      (fun inputs =>
        2 * precision * inputs *
              (resourceCount (uhligPrefixWidth inputs) ^ depth inputs *
                (depth inputs *
                  layerOverheadEnvelope
                    (uhligPrefixWidth inputs) inputs)) <=
          2 ^ inputs)
      atTop := by
  have polynomialGrowth :=
    Growth.eventually_const_mul_pow_le_two_pow_div
      (256 * precision) 10 2 (by omega)
  have depthGrowth := depthSmall 4 (by omega)
  filter_upwards [polynomialGrowth, depthGrowth,
    eventually_ge_atTop 2] with inputs polynomialBound depthBound inputsLarge
  have logPositive : 1 <= Nat.log 2 inputs := by
    exact Nat.log_pos (by omega) inputsLarge
  have depthLe : depth inputs <= inputs := by
    calc
      depth inputs = depth inputs * 1 := by ring
      _ <= depth inputs * (4 * Nat.log 2 inputs) := by
        have oneLeFourLog : 1 <= 4 * Nat.log 2 inputs := by omega
        exact Nat.mul_le_mul_left (depth inputs) oneLeFourLog
      _ = 4 * depth inputs * Nat.log 2 inputs := by ring
      _ <= inputs := depthBound
  have twoDepthLeInputs : 2 * depth inputs <= inputs := by
    calc
      2 * depth inputs <= 4 * depth inputs * Nat.log 2 inputs := by
        nlinarith
      _ <= inputs := depthBound
  have resourceSmall :
      2 * depth inputs <= 2 ^ uhligPrefixWidth inputs :=
    twoDepthLeInputs.trans
      (input_le_two_pow_uhligPrefixWidth inputs inputsLarge)
  have removedExponentSmall :
      uhligPrefixWidth inputs * depth inputs <= inputs / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    unfold uhligPrefixWidth
    calc
      (2 * Nat.log 2 inputs * depth inputs) * 2 =
          4 * depth inputs * Nat.log 2 inputs := by ring
      _ <= inputs := depthBound
  apply normalized_overhead_le_of_growth precision inputs (depth inputs)
    inputsLarge depthLe resourceSmall removedExponentSmall
  simpa only [Nat.mul_assoc] using polynomialBound

/-! ## Conditional sharp Uhlig theorem -/

/-- Uhlig's theorem, reduced exactly to sharp one-copy synthesis.  Any
explicit synthesis family with normalized coefficient one remains sharp for
every copy budget `2 ^ depth(n)` with
`depth(n) * log_2(n) = o(n)`. -/
theorem uhlig_of_sharp_one_copy
    (family : ScalarSynthesisFamily)
    (oneCopySharp : HasSharpOneCopyCost family)
    (depth : Nat -> Nat)
    (depthSmall : IsUhligDepth depth) :
    HasSharpMassProduction depth := by
  intro precision precisionPositive
  let internal := internalPrecision precision
  have internalPositive : 0 < internal := internalPrecision_positive precision
  obtain ⟨baseCutoff, baseSharp⟩ :=
    oneCopySharp internal internalPositive
  have overheadEventually := eventually_normalized_overhead_le
    depth depthSmall precision
  have removedEventually :=
    depthSmall (2 * (internal + 1)) (by positivity)
  have resourceEventually :=
    depthSmall (internal + 1) (by positivity)
  filter_upwards [overheadEventually, removedEventually, resourceEventually,
    eventually_ge_atTop (max 2 (2 * baseCutoff))] with
      inputs overheadBound removedBound resourceBound inputThreshold
  intro function copies copiesPositive copiesBound
  let prefixWidth := uhligPrefixWidth inputs
  let recursionDepth := depth inputs
  let baseWidth := uhligBaseWidth recursionDepth inputs
  have inputsLarge : 2 <= inputs :=
    (le_max_left 2 (2 * baseCutoff)).trans inputThreshold
  have logPositive : 1 <= Nat.log 2 inputs :=
    Nat.log_pos (by omega) inputsLarge
  have removedAll :
      (internal + 1) * recursionDepth * prefixWidth <= inputs := by
    calc
      (internal + 1) * recursionDepth * prefixWidth =
          2 * (internal + 1) * depth inputs * Nat.log 2 inputs := by
        dsimp [recursionDepth, prefixWidth, uhligPrefixWidth]
        ring
      _ <= inputs := removedBound
  have blocksFit : recursionDepth * prefixWidth <= inputs := by
    calc
      recursionDepth * prefixWidth <=
          (internal + 1) * recursionDepth * prefixWidth := by
        have oneLeInternal : 1 <= internal + 1 := by omega
        calc
          recursionDepth * prefixWidth =
              1 * (recursionDepth * prefixWidth) := by ring
          _ <= (internal + 1) * (recursionDepth * prefixWidth) :=
            Nat.mul_le_mul_right _ oneLeInternal
          _ = (internal + 1) * recursionDepth * prefixWidth := by ring
      _ <= inputs := removedAll
  have twiceRemoved : 2 * (recursionDepth * prefixWidth) <= inputs := by
    calc
      2 * (recursionDepth * prefixWidth) <=
          (internal + 1) * recursionDepth * prefixWidth := by
        have internalAtLeastTwo : 2 <= internal + 1 := by
          unfold internal internalPrecision
          omega
        calc
          2 * (recursionDepth * prefixWidth) <=
              (internal + 1) * (recursionDepth * prefixWidth) :=
            Nat.mul_le_mul_right _ internalAtLeastTwo
          _ = (internal + 1) * recursionDepth * prefixWidth := by ring
      _ <= inputs := removedAll
  have halfInputLeBase : inputs / 2 <= baseWidth := by
    have removedLeHalf : recursionDepth * prefixWidth <= inputs / 2 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 <| by
        simpa only [Nat.mul_comm] using twiceRemoved
    change inputs / 2 <= inputs - recursionDepth * prefixWidth
    apply Nat.le_sub_of_add_le
    calc
      inputs / 2 + recursionDepth * prefixWidth <=
          inputs / 2 + inputs / 2 := Nat.add_le_add_left removedLeHalf _
      _ = 2 * (inputs / 2) := by ring
      _ <= inputs := Nat.mul_div_le inputs 2
  have cutoffLeHalf : baseCutoff <= inputs / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    simpa only [Nat.mul_comm] using
      (le_max_right 2 (2 * baseCutoff)).trans inputThreshold
  have basePastCutoff : baseCutoff <= baseWidth :=
    cutoffLeHalf.trans halfInputLeBase
  have basePositive : 0 < baseWidth := by
    have halfPositive : 0 < inputs / 2 :=
      Nat.div_pos inputsLarge (by omega)
    omega
  have resourceSmall :
      (internal + 1) * recursionDepth <= 2 ^ prefixWidth := by
    have beforeInputs :
        (internal + 1) * recursionDepth <= inputs := by
      calc
        (internal + 1) * recursionDepth <=
            (internal + 1) * recursionDepth * Nat.log 2 inputs := by
          have oneLeLogProduct :
              (internal + 1) * recursionDepth <=
                (internal + 1) * recursionDepth * Nat.log 2 inputs := by
            exact Nat.le_mul_of_pos_right _ (by omega)
          exact oneLeLogProduct
        _ <= inputs := by
          dsimp [recursionDepth]
          exact resourceBound
    exact beforeInputs.trans
      (input_le_two_pow_uhligPrefixWidth inputs inputsLarge)
  have removedWidthSmall :
      internal * recursionDepth * prefixWidth <= baseWidth := by
    unfold baseWidth uhligBaseWidth
    apply Nat.le_sub_of_add_le
    calc
      internal * recursionDepth * prefixWidth +
          recursionDepth * prefixWidth =
        (internal + 1) * recursionDepth * prefixWidth := by ring
      _ <= inputs := removedAll
  have widthIdentity :
      recursiveWidth prefixWidth baseWidth recursionDepth = inputs := by
    dsimp [prefixWidth, baseWidth]
    exact recursiveWidth_uhligBaseWidth recursionDepth inputs blocksFit
  let baseBound := normalizedBaseBound internal baseWidth
  have baseCost : forall baseFunction : ScalarFunction Bool baseWidth,
      ((family baseWidth).circuit baseFunction).cost
          DeMorgan.standardCost <= baseBound := by
    intro baseFunction
    exact circuit_cost_le_normalizedBaseBound family internal baseWidth
      internalPositive basePositive baseFunction
      (baseSharp baseWidth basePastCutoff baseFunction)
  obtain ⟨gates, circuit, computes, circuitBound⟩ :=
    exists_finite_uhlig_circuit_at_width prefixWidth baseWidth
      recursionDepth inputs widthIdentity (family baseWidth) baseBound
      baseCost function copies copiesPositive (by
        dsimp [recursionDepth]
        exact copiesBound)
  let mainTerm := resourceCount prefixWidth ^ recursionDepth * baseBound
  let overheadTerm :=
    resourceCount prefixWidth ^ recursionDepth *
      (recursionDepth * layerOverheadEnvelope prefixWidth inputs)
  have splitCost :
      resourceCount prefixWidth ^ recursionDepth *
          (baseBound + recursionDepth *
            layerOverheadEnvelope prefixWidth inputs) =
        mainTerm + overheadTerm := by
    unfold mainTerm overheadTerm
    ring
  have costBound :
      circuit.cost DeMorgan.standardCost <= mainTerm + overheadTerm :=
    circuitBound.trans_eq splitCost
  have widthSum :
      recursionDepth * prefixWidth + baseWidth = inputs := by
    unfold baseWidth uhligBaseWidth
    exact Nat.add_sub_of_le blocksFit
  have normalizedMain :
      internal ^ 3 * mainTerm * inputs <=
        (internal + 1) ^ 3 * 2 ^ inputs := by
    have finiteMain := precision_cube_mul_mainTerm_le internal prefixWidth
      baseWidth recursionDepth baseBound
      (normalizedBaseBound_spec internal baseWidth)
      resourceSmall removedWidthSmall
    simpa only [mainTerm, widthSum] using finiteMain
  have mainBound :
      2 * precision * mainTerm * inputs <=
        (2 * precision + 1) * 2 ^ inputs :=
    mainTerm_with_allocated_slack precision mainTerm inputs <| by
      simpa only [internal] using normalizedMain
  have finiteOverhead :
      2 * precision * inputs * overheadTerm <= 2 ^ inputs := by
    dsimp [overheadTerm, prefixWidth, recursionDepth]
    exact overheadBound
  have normalizedCost :
      precision * circuit.cost DeMorgan.standardCost * inputs <=
        (precision + 1) * 2 ^ inputs :=
    combine_main_and_overhead precision
      (circuit.cost DeMorgan.standardCost) mainTerm overheadTerm inputs
      costBound mainBound finiteOverhead
  have complexityBound :
      booleanMassComplexity function copies <=
        (circuit.cost DeMorgan.standardCost : ENat) := by
    unfold booleanMassComplexity
    exact circuit.costComplexity_le DeMorgan.standardCost computes
  calc
    (precision * inputs : ENat) * booleanMassComplexity function copies <=
        (precision * inputs : ENat) *
          (circuit.cost DeMorgan.standardCost : ENat) := by gcongr
    _ = (precision * circuit.cost DeMorgan.standardCost * inputs : Nat) := by
      norm_num
      ring
    _ <= ((precision + 1) * 2 ^ inputs : Nat) := by
      exact_mod_cast normalizedCost

end UhligTheorem
end MassProduction
end Algebraic
