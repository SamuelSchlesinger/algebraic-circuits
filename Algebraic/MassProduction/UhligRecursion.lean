import Algebraic.MassProduction.ScalarSynthesis
import Algebraic.MassProduction.UhligCircuit

/-!
# Recursive Uhlig mass production

This module iterates the exact finite two-copy layer. Scalar synthesis data is
passed explicitly, so the recursion introduces no global or local
instance-search burden.
-/

namespace Algebraic
namespace MassProduction
namespace UhligRecursion

open UhligCircuit
open scoped BigOperators

/-- Width left after `depth` equal prefix blocks have been restored. -/
@[reducible] def recursiveWidth
    (prefixWidth baseWidth : Nat) : Nat -> Nat
  | 0 => baseWidth
  | depth + 1 => prefixWidth + recursiveWidth prefixWidth baseWidth depth

/-- Number of copies after `depth` two-copy layers. -/
@[reducible] def recursiveCopies : Nat -> Nat
  | 0 => 1
  | depth + 1 => 2 * recursiveCopies depth

theorem recursiveCopies_eq_two_pow (depth : Nat) :
    recursiveCopies depth = 2 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [recursiveCopies, inductionHypothesis, pow_succ, Nat.mul_comm]

theorem recursiveWidth_eq (prefixWidth baseWidth depth : Nat) :
    recursiveWidth prefixWidth baseWidth depth =
      depth * prefixWidth + baseWidth := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      simp [recursiveWidth, inductionHypothesis, Nat.succ_mul,
        Nat.add_left_comm, Nat.add_comm]

/-- Gate count determined by the chosen base synthesis and every explicit
routing/decoding layer above it. -/
noncomputable def recursiveGateCount
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth) :
    (depth : Nat) ->
      ScalarFunction Bool (recursiveWidth prefixWidth baseWidth depth) -> Nat
  | 0, function => 1 * base.gateCount function
  | depth + 1, function =>
      let suffixWidth := recursiveWidth prefixWidth baseWidth depth
      let pairs := recursiveCopies depth
      let resourceGateCounts :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveGateCount prefixWidth baseWidth base depth
            (resourceFunction function resource)
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          routedResourceGateCount prefixWidth suffixWidth pairs
            resourceGateCounts resource) +
        (Finset.univ.sum fun output : Fin (2 * pairs) =>
          sharedDecoderOutputGateCount
            prefixWidth suffixWidth pairs output)

/-- The recursive circuit obtained by using the supplied synthesis at the
base and one exact Uhlig layer per recursive step. -/
noncomputable def recursiveCircuit
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth) :
    (depth : Nat) ->
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) ->
    Circuit DeMorgan.signature
      (recursiveCopies depth *
        recursiveWidth prefixWidth baseWidth depth)
      (recursiveGateCount prefixWidth baseWidth base depth function)
      (recursiveCopies depth)
  | 0, function => (base.circuit function).replicateScalar 1
  | depth + 1, function =>
      let pairs := recursiveCopies depth
      let resourceGateCounts :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveGateCount prefixWidth baseWidth base depth
            (resourceFunction function resource)
      let resourceCircuits :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource)
      sharedUhligLayerCircuit pairs resourceGateCounts resourceCircuits

/-- Iterating the finite layer computes exactly `2 ^ depth` independent
copies of the original function. -/
theorem recursiveCircuit_computes
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (depth : Nat)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) :
    (recursiveCircuit prefixWidth baseWidth base depth function).Computes
      DeMorgan.interpretation
      (directProduct function (recursiveCopies depth)) := by
  induction depth with
  | zero =>
      have outputFunction :
          (base.circuit function).outputFunction
              DeMorgan.interpretation 0 = function :=
        Circuit.outputFunction_eq_of_computes_scalarTarget
          (base.computes function)
      exact Circuit.replicateScalar_computes_directProduct outputFunction 1
  | succ depth inductionHypothesis =>
      exact sharedUhligLayerCircuit_computes function (recursiveCopies depth)
        (fun resource =>
          recursiveGateCount prefixWidth baseWidth base depth
            (resourceFunction function resource))
        (fun resource =>
          recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource))
        (fun resource => inductionHypothesis
          (resourceFunction function resource))

@[simp] theorem recursiveCircuit_cost_zero
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (function : ScalarFunction Bool baseWidth) :
    (recursiveCircuit prefixWidth baseWidth base 0 function).cost
        DeMorgan.standardCost =
      (base.circuit function).cost DeMorgan.standardCost := by
  change ((base.circuit function).replicateScalar 1).cost
      DeMorgan.standardCost =
    (base.circuit function).cost DeMorgan.standardCost
  have costIdentity := Circuit.cost_replicateScalar
    (base.circuit function) 1 DeMorgan.standardCost
  simpa only [Nat.one_mul] using costIdentity

/-- Exact recursive cost identity.  The first summand at each resource is
explicit routing overhead, and the second is the recursively shared resource
computation. -/
@[simp] theorem recursiveCircuit_cost_succ
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (depth : Nat)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth (depth + 1))) :
    (recursiveCircuit prefixWidth baseWidth base (depth + 1) function).cost
        DeMorgan.standardCost =
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin (recursiveCopies depth) =>
            (resourceRouterCircuit
              (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
              resource).cost DeMorgan.standardCost) +
          (recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource)).cost
              DeMorgan.standardCost)) +
      (Finset.univ.sum fun output : Fin (2 * recursiveCopies depth) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
          pairSide.1 pairSide.2).cost DeMorgan.standardCost) := by
  change
    (sharedUhligLayerCircuit (recursiveCopies depth)
      (fun resource =>
        recursiveGateCount prefixWidth baseWidth base depth
          (resourceFunction function resource))
      (fun resource =>
        recursiveCircuit prefixWidth baseWidth base depth
          (resourceFunction function resource))).cost
        DeMorgan.standardCost = _
  have costIdentity := sharedUhligLayerCircuit_cost
    (prefixWidth := prefixWidth)
    (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
    (pairs := recursiveCopies depth)
    (resourceGateCounts := fun resource =>
      recursiveGateCount prefixWidth baseWidth base depth
        (resourceFunction function resource))
    (resourceCircuits := fun resource =>
      recursiveCircuit prefixWidth baseWidth base depth
        (resourceFunction function resource))
  exact costIdentity

/-- Number of shorter resource functions created by one Uhlig layer. -/
def resourceCount (prefixWidth : Nat) : Nat :=
  prefixLast prefixWidth + 2

theorem resourceCount_eq (prefixWidth : Nat) :
    resourceCount prefixWidth = 2 ^ prefixWidth + 1 := by
  unfold resourceCount
  have count := prefixCount_eq prefixWidth
  omega

/-- Total nonrecursive overhead accumulated by the full resource tree. -/
def recursiveOverhead
    (prefixWidth baseWidth : Nat) : Nat -> Nat
  | 0 => 0
  | depth + 1 =>
      resourceCount prefixWidth *
          recursiveOverhead prefixWidth baseWidth depth +
        sharedLayerOverheadBound prefixWidth
          (recursiveWidth prefixWidth baseWidth depth)
          (recursiveCopies depth)

/-- The overhead of one layer after factoring out its number of request
pairs.  Keeping this as an explicit natural-number expression makes the
subsequent recurrence bounds independent of asymptotic notation. -/
def layerOverheadEnvelope (prefixWidth suffixWidth : Nat) : Nat :=
  resourceCount prefixWidth *
      (suffixWidth * routedSuffixCostBound prefixWidth) +
    2 * sharedDecodedCostBound prefixWidth

theorem sharedLayerOverheadBound_eq
    (prefixWidth suffixWidth pairs : Nat) :
    sharedLayerOverheadBound prefixWidth suffixWidth pairs =
      pairs * layerOverheadEnvelope prefixWidth suffixWidth := by
  unfold sharedLayerOverheadBound layerOverheadEnvelope resourceCount
  ring

theorem layerOverheadEnvelope_mono_suffix
    (prefixWidth small large : Nat)
    (bounded : small <= large) :
    layerOverheadEnvelope prefixWidth small <=
      layerOverheadEnvelope prefixWidth large := by
  unfold layerOverheadEnvelope
  gcongr

theorem resourceCount_positive (prefixWidth : Nat) :
    0 < resourceCount prefixWidth := by
  rw [resourceCount_eq]
  positivity

theorem recursiveCopies_le_resourcePower
    (prefixWidth depth : Nat) :
    recursiveCopies depth <= resourceCount prefixWidth ^ depth := by
  rw [recursiveCopies_eq_two_pow]
  exact Nat.pow_le_pow_left (by
    rw [resourceCount_eq]
    have powerPositive := Nat.two_pow_pos prefixWidth
    omega) depth

/-- A denominator-free upper estimate for `(base + 1)^depth`.  It is the
finite inequality behind the fact that the extra one resource per layer does
not alter Uhlig's leading coefficient when `depth / base` tends to zero. -/
theorem sub_mul_succ_pow_le_pow_succ
    (base depth : Nat)
    (depthLe : depth <= base) :
    (base - depth) * (base + 1) ^ depth <= base ^ (depth + 1) := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      have priorDepthLe : depth <= base := by omega
      have coefficientBound :
          (base - (depth + 1)) * (base + 1) <=
            (base - depth) * base := by
        let remainder := base - (depth + 1)
        have baseSplit :
            base = remainder + (depth + 1) :=
          (Nat.sub_add_cancel depthLe).symm
        have priorSub :
            base - depth = remainder + 1 := by
          dsimp only [remainder]
          omega
        change remainder * (base + 1) <= (base - depth) * base
        rw [priorSub, baseSplit]
        nlinarith
      calc
        (base - (depth + 1)) * (base + 1) ^ (depth + 1) =
            ((base - (depth + 1)) * (base + 1)) *
              (base + 1) ^ depth := by
          rw [pow_succ]
          ring
        _ <= ((base - depth) * base) * (base + 1) ^ depth := by
          gcongr
        _ = base * ((base - depth) * (base + 1) ^ depth) := by ring
        _ <= base * base ^ (depth + 1) := by
          gcongr
          exact inductionHypothesis priorDepthLe
        _ = base ^ ((depth + 1) + 1) := by
          rw [pow_succ]
          ring

/-- Quantitative leading-coefficient control for the resource tree.  If the
base resource count `2^p` dominates `(precision + 1) * depth`, then the extra
resource at each layer costs at most the factor
`(precision + 1) / precision`. -/
theorem precision_mul_resourcePower_le
    (precision prefixWidth depth : Nat)
    (depthSmall : (precision + 1) * depth <= 2 ^ prefixWidth) :
    precision * resourceCount prefixWidth ^ depth <=
      (precision + 1) * (2 ^ prefixWidth) ^ depth := by
  let base := 2 ^ prefixWidth
  have basePositive : 0 < base := by
    dsimp [base]
    positivity
  have depthLeBase : depth <= base := by
    exact (Nat.le_mul_of_pos_left depth (by omega : 0 < precision + 1)).trans
      depthSmall
  have powerBound :
      (base - depth) * (base + 1) ^ depth <= base ^ (depth + 1) :=
    sub_mul_succ_pow_le_pow_succ base depth depthLeBase
  have coefficientBound :
      precision * base <= (precision + 1) * (base - depth) := by
    let remainder := base - (precision + 1) * depth
    have baseSplit :
        base = remainder + (precision + 1) * depth :=
      (Nat.sub_add_cancel depthSmall).symm
    have differenceSplit :
        base - depth = remainder + precision * depth := by
      have productSplit :
          (precision + 1) * depth = precision * depth + depth := by ring
      dsimp only [remainder]
      omega
    rw [differenceSplit, baseSplit]
    nlinarith
  apply le_of_mul_le_mul_left (a := base) _ basePositive
  calc
    base * (precision * resourceCount prefixWidth ^ depth) =
        precision * base * (base + 1) ^ depth := by
      rw [resourceCount_eq]
      dsimp [base]
      ring
    _ <= (precision + 1) * (base - depth) *
          (base + 1) ^ depth := by
      gcongr
    _ <= (precision + 1) * base ^ (depth + 1) := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_left (precision + 1) powerBound
    _ = base * ((precision + 1) * base ^ depth) := by
      rw [pow_succ]
      ring

/-- Closed finite bound for all routing and decoding accumulated through the
resource tree.  The chosen `maxWidth` may be any upper bound on the final
recursive width; in applications it is the original input width. -/
theorem recursiveOverhead_le
    (prefixWidth baseWidth depth maxWidth : Nat)
    (widthBound :
      recursiveWidth prefixWidth baseWidth depth <= maxWidth) :
    recursiveOverhead prefixWidth baseWidth depth <=
      depth * resourceCount prefixWidth ^ depth *
        layerOverheadEnvelope prefixWidth maxWidth := by
  induction depth with
  | zero => simp [recursiveOverhead]
  | succ depth inductionHypothesis =>
      have priorWidthBound :
          recursiveWidth prefixWidth baseWidth depth <= maxWidth := by
        exact (Nat.le_add_left _ _).trans widthBound
      have priorBound := inductionHypothesis priorWidthBound
      have layerBound :
          sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) <=
            resourceCount prefixWidth ^ depth *
              layerOverheadEnvelope prefixWidth maxWidth := by
        rw [sharedLayerOverheadBound_eq]
        exact Nat.mul_le_mul
          (recursiveCopies_le_resourcePower prefixWidth depth)
          (layerOverheadEnvelope_mono_suffix prefixWidth _ _ priorWidthBound)
      have resourceAtLeastOne : 1 <= resourceCount prefixWidth :=
        resourceCount_positive prefixWidth
      rw [recursiveOverhead]
      calc
        resourceCount prefixWidth *
              recursiveOverhead prefixWidth baseWidth depth +
            sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) <=
            resourceCount prefixWidth *
                (depth * resourceCount prefixWidth ^ depth *
                  layerOverheadEnvelope prefixWidth maxWidth) +
              resourceCount prefixWidth ^ depth *
                layerOverheadEnvelope prefixWidth maxWidth :=
          Nat.add_le_add (Nat.mul_le_mul_left _ priorBound) layerBound
        _ <= resourceCount prefixWidth *
                (depth * resourceCount prefixWidth ^ depth *
                  layerOverheadEnvelope prefixWidth maxWidth) +
              resourceCount prefixWidth *
                (resourceCount prefixWidth ^ depth *
                  layerOverheadEnvelope prefixWidth maxWidth) := by
          exact Nat.add_le_add_left
            (Nat.le_mul_of_pos_left _ (resourceCount_positive prefixWidth)) _
        _ = (depth + 1) * resourceCount prefixWidth ^ (depth + 1) *
              layerOverheadEnvelope prefixWidth maxWidth := by
          rw [pow_succ]
          ring

/-- Finite quantitative Uhlig recurrence.  A uniform scalar base bound `B`
lifts to `(2^p + 1)^d * B` plus the fully explicit routing/decoding
overhead. -/
theorem recursiveCircuit_cost_le
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (depth : Nat)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) :
    (recursiveCircuit prefixWidth baseWidth base depth function).cost
        DeMorgan.standardCost <=
      resourceCount prefixWidth ^ depth * baseBound +
        recursiveOverhead prefixWidth baseWidth depth := by
  induction depth with
  | zero =>
      rw [recursiveCircuit_cost_zero]
      simpa [recursiveOverhead] using baseCost function
  | succ depth inductionHypothesis =>
      let resourceGateCounts :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveGateCount prefixWidth baseWidth base depth
            (resourceFunction function resource)
      let resourceCircuits :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource)
      change
        (sharedUhligLayerCircuit (recursiveCopies depth)
          resourceGateCounts resourceCircuits).cost
            DeMorgan.standardCost <= _
      calc
        (sharedUhligLayerCircuit (recursiveCopies depth)
            resourceGateCounts resourceCircuits).cost
              DeMorgan.standardCost <=
            (Finset.univ.sum fun resource :
                Fin (prefixLast prefixWidth + 2) =>
              (resourceCircuits resource).cost DeMorgan.standardCost) +
            sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) :=
          sharedUhligLayerCircuit_cost_le_resource_sum_add_overhead
            (prefixWidth := prefixWidth)
            (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
            (pairs := recursiveCopies depth)
            (resourceGateCounts := resourceGateCounts)
            (resourceCircuits := resourceCircuits)
        _ <=
            (Finset.univ.sum fun _resource :
                Fin (prefixLast prefixWidth + 2) =>
              resourceCount prefixWidth ^ depth * baseBound +
                recursiveOverhead prefixWidth baseWidth depth) +
            sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) := by
          gcongr with resource
          exact inductionHypothesis (resourceFunction function resource)
        _ = resourceCount prefixWidth ^ (depth + 1) * baseBound +
              recursiveOverhead prefixWidth baseWidth (depth + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.nsmul_eq_mul, recursiveOverhead]
          rw [pow_succ]
          unfold resourceCount
          ring_nf

/-- The recursive cost recurrence with the accumulated overhead replaced by
its closed envelope bound. -/
theorem recursiveCircuit_cost_le_closed
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (depth maxWidth : Nat)
    (widthBound :
      recursiveWidth prefixWidth baseWidth depth <= maxWidth)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) :
    (recursiveCircuit prefixWidth baseWidth base depth function).cost
        DeMorgan.standardCost <=
      resourceCount prefixWidth ^ depth *
        (baseBound + depth *
          layerOverheadEnvelope prefixWidth maxWidth) := by
  have recurrence := recursiveCircuit_cost_le prefixWidth baseWidth base
    baseBound baseCost depth function
  have overhead := recursiveOverhead_le prefixWidth baseWidth depth maxWidth
    widthBound
  calc
    (recursiveCircuit prefixWidth baseWidth base depth function).cost
        DeMorgan.standardCost <=
      resourceCount prefixWidth ^ depth * baseBound +
        recursiveOverhead prefixWidth baseWidth depth := recurrence
    _ <= resourceCount prefixWidth ^ depth * baseBound +
        depth * resourceCount prefixWidth ^ depth *
          layerOverheadEnvelope prefixWidth maxWidth := by gcongr
    _ = resourceCount prefixWidth ^ depth *
        (baseBound + depth *
          layerOverheadEnvelope prefixWidth maxWidth) := by ring

end UhligRecursion
end MassProduction
end Algebraic
