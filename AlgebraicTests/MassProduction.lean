import Algebraic.Basis.DeMorgan
import Algebraic.MassProduction

/-!
# Mass-production API regressions

These tests instantiate the generic direct-product construction with a
one-gate Boolean conjunction circuit. They check the row-major semantics and
the exact cost and gate-count accounting for two disjoint copies.
-/

namespace AlgebraicTests.MassProduction

open Algebraic
open Algebraic.MassProduction
open scoped LinearAlgebra.Projectivization

/-- The two-input conjunction as a scalar Boolean function. -/
def conjunctionFunction : ScalarFunction Bool 2 :=
  fun input => input 0 && input 1

/-- A one-gate circuit computing `conjunctionFunction`. -/
def conjunctionCircuit : Circuit DeMorgan.signature 2 1 1 where
  program := .gate .empty {
    op := .and
    wires := Fin.cases (Wire.input 0) fun _ => Wire.input 1
  }
  outputs := fun _ => Wire.gate 0

example :
    conjunctionCircuit.outputFunction DeMorgan.interpretation 0 =
      conjunctionFunction := by
  funext input
  rfl

example :
    (conjunctionCircuit.replicateScalar 2).Computes
      DeMorgan.interpretation (directProduct conjunctionFunction 2) := by
  apply Circuit.replicateScalar_computes_directProduct
  funext input
  rfl

/-- Two row-major input blocks: `(true, true)` and `(true, false)`. -/
def twoConjunctionInputs : Fin 4 -> Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => true
  | ⟨3, _⟩ => false

example :
    (conjunctionCircuit.replicateScalar 2).eval
      DeMorgan.interpretation twoConjunctionInputs 0 = true := by
  native_decide

example :
    (conjunctionCircuit.replicateScalar 2).eval
      DeMorgan.interpretation twoConjunctionInputs 1 = false := by
  native_decide

example :
    (conjunctionCircuit.replicateScalar 2).cost DeMorgan.binaryCost = 2 := by
  native_decide

example : (conjunctionCircuit.replicateScalar 2).size = 2 := by
  native_decide

set_option maxHeartbeats 1000000 in
/-- The native shared-minterm Shannon construction computes an arbitrary
split-input function, independently of the target truth table. -/
example (input : Fin 2 -> Bool) :
    (ShannonSynthesis.circuit
      (addressWidth := 1) (dataWidth := 1) conjunctionFunction).eval
        DeMorgan.interpretation input 0 = conjunctionFunction input := by
  exact ShannonSynthesis.circuit_eval
    (addressWidth := 1) (dataWidth := 1) conjunctionFunction input

example :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (directProduct conjunctionFunction 2) <=
      (2 : ENat) *
        Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
          (scalarTarget conjunctionFunction) :=
  Circuit.costComplexity_directProduct_le
    (σ := DeMorgan.signature) (U := Bool) (n := 2)
    DeMorgan.interpretation DeMorgan.binaryCost conjunctionFunction 2

/-- Two source coordinates for a concrete three-resource Uhlig codeword. -/
def uhligSourceValues : Fin 2 -> Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false

example : uhligResource uhligSourceValues 0 = true := by native_decide

example : uhligResource uhligSourceValues 1 = true := by native_decide

example : uhligResource uhligSourceValues 2 = false := by native_decide

/-- Abstract punctured-line data depends only on field finiteness, without a
chosen `Fintype` enumeration. -/
noncomputable example
    {K V : Type*}
    [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (target : V)
    (direction : ℙ K V) : Finset V :=
  puncturedLine target direction

/-- Regression: packed prefixes range over genuine data types, not merely
propositions, and occupied lookup uses embedding injectivity. -/
example
    (placement : Fin 2 ↪ PackedBitPosition dimension width)
    (values : Fin 2 -> Bool)
    (source : Fin 2) :
    packedBit placement values (placement source) = values source := by
  exact packedBit_at_placement placement values source

/-- Runtime request splitting agrees with the standard row-major direct
product operation. -/
example
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (input : Fin (requests *
      RuntimePipeline.requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin requests) :
    directProduct (RuntimePipeline.requestFunction function) requests
        input request =
      function (RuntimePipeline.requestSource input request)
        (RuntimePipeline.requestSuffix input request) := by
  exact RuntimePipeline.directProduct_requestFunction_apply
    function input request

/-- Reversed request order selects the suffix for coordinate `1` and the
prefix for coordinate `0`, while preserving output order. -/
example :
    Disjoint (uhligRecoveryPair (1 : Fin 2) 0).1
        (uhligRecoveryPair (1 : Fin 2) 0).2 ∧
      (∑ resource ∈ (uhligRecoveryPair (1 : Fin 2) 0).1,
          uhligResource uhligSourceValues resource) = uhligSourceValues 1 ∧
      (∑ resource ∈ (uhligRecoveryPair (1 : Fin 2) 0).2,
          uhligResource uhligSourceValues resource) = uhligSourceValues 0 := by
  apply uhlig_two_copy_disjoint_recovery
  intro value
  exact neg_add_cancel value

/-- A concrete nonzero two-coordinate vector over `GF(4)`. -/
noncomputable def gfFourVector : Fin 2 -> BinaryExtension 2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1

theorem gfFourVector_ne_zero : gfFourVector ≠ 0 := by
  intro equal
  have atZero := congrFun equal (0 : Fin 2)
  simp [gfFourVector] at atZero

/-- The concrete vector determines a projective direction over `GF(4)`. -/
noncomputable def gfFourDirection :
    ℙ (BinaryExtension 2) (Fin 2 -> BinaryExtension 2) :=
  Projectivization.mk (BinaryExtension 2) gfFourVector
    gfFourVector_ne_zero

/-- The explicit shared projective normalizer specializes to a checked
`GF(4)^2` circuit. -/
example :
    (normalizeBinaryExtensionVectorCircuit 2 (by omega : 0 < 2)).eval
        DeMorgan.interpretation
        (binaryExtensionVectorBits (by omega : 0 < 2) gfFourVector) =
      binaryExtensionVectorBits (by omega : 0 < 2)
        (normalizeBinaryExtensionVector gfFourVector) := by
  exact normalizeBinaryExtensionVectorCircuit_eval_vectorBits
    (by omega) (by omega) gfFourVector gfFourVector_ne_zero

/-- The same concrete normalizer inherits the proved polynomial ledger. -/
example :
    (normalizeBinaryExtensionVectorCircuit 2 (by omega : 0 < 2)).cost
        DeMorgan.standardCost <=
      projectiveNormalizationCircuitBound 2 2 := by
  exact normalizeBinaryExtensionVectorCircuit_cost_le (by omega)

/-- Rank compilation agrees with the injective projective block rank. -/
example :
    (projectiveDirectionRankCircuit 2 (by omega : 0 < 2)).eval
        DeMorgan.interpretation
        (binaryExtensionVectorBits (by omega : 0 < 2)
          gfFourDirection.rep) =
      projectiveDirectionRankBits (by omega : 0 < 2) gfFourDirection := by
  exact projectiveDirectionRankCircuit_eval_projective
    (by omega) (by omega) gfFourDirection

/-- The explicit unrank circuit reconstructs the canonical direction key. -/
example :
    (projectiveUnrankPackedCircuit 2 (by omega : 0 < 2)).eval
        DeMorgan.interpretation
        (projectiveDirectionRankBits (by omega : 0 < 2) gfFourDirection) =
      projectiveDirectionKey (by omega : 0 < 2) gfFourDirection := by
  exact projectiveUnrankPackedCircuit_eval_directionRank
    (by omega) gfFourDirection

/-- The explicit four-record Batcher circuit sorts one-bit keys. -/
example
    (input : Fin (Sorting.networkBits 2 2) -> Bool) :
    Sorting.FlatKeysSorted (by omega : 1 <= 2) true
      ((Sorting.bitonicSortCircuit (by omega : 1 <= 2) 2 true).eval
        DeMorgan.interpretation input) := by
  exact Sorting.bitonicSortCircuit_keysSorted
    (by omega) 2 true input

/-- Sorting moves the second bit as payload with its complete record. -/
example
    (input : Fin (Sorting.networkBits 2 2) -> Bool) :
    Sorting.FlatRecordsPermute
      ((Sorting.bitonicSortCircuit (by omega : 1 <= 2) 2 true).eval
        DeMorgan.interpretation input) input := by
  exact Sorting.bitonicSortCircuit_recordsPermute
    (by omega) 2 true input

/-- Generic uniqueness transport is exposed by sorting semantics rather than
the routing implementation that first needed it. -/
example
    {alpha : Type*}
    {output input : Fin 4 -> alpha}
    {predicate : alpha -> Prop}
    (permuted : Sorting.Semantics.SequencePermutes output input)
    (uniqueInput :
      Sorting.Semantics.UniqueIndexWhere input predicate) :
    Sorting.Semantics.UniqueIndexWhere output predicate :=
  uniqueInput.of_sequencePermutes permuted

/-- The four-record instance exposes the proved polynomial cost ledger. -/
example :
    (Sorting.bitonicSortCircuit (by omega : 1 <= 2) 2 true).cost
        DeMorgan.standardCost <=
      2 * 2 * Sorting.networkRecords 2 *
        ((2 * 2) * (2 * (1 * (6 * 1 + 4)) + 4)) := by
  exact Sorting.bitonicSortCircuit_cost_le (by omega) 2 true

/-- A free within-record swap lets the same sorter order records by their
second physical bit while returning the original record layout. -/
example
    (input : Fin (Sorting.networkBits 2 2) -> Bool) :
    Sorting.FlatKeysSortedBy
      (Equiv.swap (0 : Fin 2) 1) (by omega : 1 <= 2) true
      ((Sorting.bitonicSortByCircuit
        (Equiv.swap (0 : Fin 2) 1) (by omega : 1 <= 2) 2 true).eval
          DeMorgan.interpretation input) := by
  exact Sorting.bitonicSortByCircuit_keysSorted
    (Equiv.swap (0 : Fin 2) 1) (by omega) 2 true input

/-- Sorting by a rearranged key still permutes complete physical records. -/
example
    (input : Fin (Sorting.networkBits 2 2) -> Bool) :
    Sorting.FlatRecordsPermute
      ((Sorting.bitonicSortByCircuit
        (Equiv.swap (0 : Fin 2) 1) (by omega : 1 <= 2) 2 true).eval
          DeMorgan.interpretation input) input := by
  exact Sorting.bitonicSortByCircuit_recordsPermute
    (Equiv.swap (0 : Fin 2) 1) (by omega) 2 true input

/-- The shared scatter/gather local pass has exact compiled semantics. -/
example
    (input : Fin (Sorting.networkBits 2 (Routing.recordWidth 2 3)) ->
      Bool) :
    (Routing.sortedPredecessorCopyCircuit 2 2 3 false true).eval
        DeMorgan.interpretation input =
      Routing.predecessorCopyBits 2 2 3 false true
        (Sorting.bitonicSortBits
          (Routing.keyAndTagFitsRecord 2 3) 2 true input) := by
  exact Routing.sortedPredecessorCopyCircuit_eval false true input

/-- The same pass exposes its complete sorting-plus-scan gate ledger. -/
example :
    (Routing.sortedPredecessorCopyCircuit 2 2 3 false true).cost
        DeMorgan.standardCost <=
      2 * 2 * Sorting.networkRecords 2 *
          ((2 * Routing.recordWidth 2 3) *
            (2 * ((2 + 1) * (6 * (2 + 1) + 4)) + 4)) +
        Sorting.networkBits 2 (Routing.recordWidth 2 3) *
          (12 * 2 + 12) := by
  exact Routing.sortedPredecessorCopyCircuit_cost_le false true

/-- A complete match-then-canonical-order pair has verified circuit
semantics; the same construction is instantiated for scatter and gather. -/
example
    (input : Fin (Sorting.networkBits 2 (Routing.recordWidth 2 3)) ->
      Bool) :
    Sorting.FlatKeysSortedBy
      (Equiv.refl (Fin (Routing.recordWidth 2 3)))
      (Routing.keyAndTagFitsRecord 2 3) true
      ((Routing.matchThenOrderCircuit 2 2 3 3
        (Equiv.refl (Fin (Routing.recordWidth 2 3)))
        (Routing.keyAndTagFitsRecord 2 3) false true).eval
          DeMorgan.interpretation input) := by
  exact Routing.matchThenOrderCircuit_keysSorted
    (Equiv.refl (Fin (Routing.recordWidth 2 3)))
    (Routing.keyAndTagFitsRecord 2 3) false true input

/-- The explicit carry/XOR increment is the immediate lexicographic
successor whenever it does not roll over. -/
example :
    toLex (![false, true] : Fin 2 -> Bool) ⋖
      toLex (LeastMissing.binaryIncrement
        (![false, true] : Fin 2 -> Bool)) := by
  apply LeastMissing.binaryIncrement_covBy_of_lt
  change Pi.Lex (· < ·) (· < ·)
    (![false, true] : Fin 2 -> Bool)
    (LeastMissing.binaryIncrement (![false, true] : Fin 2 -> Bool))
  refine ⟨0, ?_, ?_⟩
  · intro previous previousBefore
    exact False.elim (Fin.not_lt_zero previous previousBefore)
  · native_decide

/-- The least-missing circuit exposes a theorem with exactly the finite
capacity premise needed by the projective scheduler. -/
example
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (Sorting.networkBits depth rankWidth) -> Bool)
    (sorted : Sorting.FlatKeysSorted (le_refl rankWidth) true input)
    (capacity : Sorting.networkRecords depth <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    toLex ((LeastMissing.leastMissingCircuit upperBound depth).eval
        DeMorgan.interpretation input) < toLex upperBound ∧
      ∀ index : Fin (Sorting.networkRecords depth),
        (LeastMissing.leastMissingCircuit upperBound depth).eval
            DeMorgan.interpretation input ≠
          LeastMissing.rankAt input index := by
  exact LeastMissing.leastMissingCircuit_sound_of_capacity
    upperBound depth input sorted capacity

/-- The packed block ranks are exactly, not merely injectively contained in,
the initial interval below the projective sentinel. -/
example
    (widthPositive : 0 < width) :
    Nat.card {rank : Lex (Fin (dimension * width) -> Bool) //
        rank < toLex (projectiveRankSentinel dimension width)} =
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := by
  exact card_projectiveRankInterval widthPositive

/-- Sorting and least-missing selection produce a genuine fresh projective
direction whenever the packed array is smaller than direction space. -/
example
    (widthPositive : 0 < width)
    (input : Fin (Sorting.networkBits depth (dimension * width)) -> Bool)
    (capacity : Sorting.networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (FreshDirection.freshProjectiveDirectionCircuit
          dimension widthPositive depth).eval DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      ∀ index : Fin (Sorting.networkRecords depth),
        projectiveDirectionRankBits widthPositive direction ≠
          LeastMissing.rankAt input index := by
  exact FreshDirection.freshProjectiveDirectionCircuit_sound
    widthPositive input capacity

/-- A complete scheduler stage, including fixed-wire difference generation,
returns a line disjoint from every represented occupied point. -/
example
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (Sorting.networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (capacity : Sorting.networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (SchedulerStage.schedulerStageCircuit
          dimension widthPositive depth).eval DeMorgan.interpretation
          (SchedulerStage.schedulerStageInputBits
            widthPositive points target) =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        (SchedulerStage.pointArraySet points) := by
  exact SchedulerStage.schedulerStageCircuit_disjoint_all_points
    widthPositive widthAtLeastTwo points target capacity

/-- The complete stage can be followed by exact line enumeration without
losing the geometric disjointness guarantee. -/
example
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (Sorting.networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (capacity : Sorting.networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        (SchedulerStage.pointArraySet points) := by
  obtain ⟨direction, _, _, disjoint⟩ :=
    LineEnumeration.scheduledLineEnumerationCircuit_sound
      widthPositive widthAtLeastTwo points target capacity
  exact ⟨direction, disjoint⟩

/-- Direction selection plus exact line enumeration retains an explicit
polynomial gate ledger. -/
example
    (widthPositive : 0 < width) :
    (LineEnumeration.scheduledLineEnumerationCircuit
      dimension widthPositive depth).cost DeMorgan.standardCost ≤
      LineEnumeration.scheduledLineEnumerationCostBound
        dimension width depth := by
  exact LineEnumeration.scheduledLineEnumerationCircuit_cost_le
    widthPositive

/-- The recursively unrolled greedy circuit realizes the manuscript's
pairwise-disjoint recovery-line scheduler for an arbitrary target multiset. -/
example
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (allFit : requests * LineEnumeration.nonzeroScalarCount width ≤
      Sorting.networkRecords depth)
    (capacity : requests * LineEnumeration.nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width) :
    ∃ directions : Fin requests ->
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width),
      (∀ request,
        SchedulerIteration.scheduledLineSet widthPositive
            (SchedulerIteration.greedyScheduleOutput dimension widthPositive
              depth requests allFit targets) request =
          ForbiddenRanks.binaryExtensionPuncturedLine
            (targets request) (directions request)) ∧
      SchedulerIteration.PairwiseDisjointFamily
        (SchedulerIteration.scheduledLineSet widthPositive
          (SchedulerIteration.greedyScheduleOutput dimension widthPositive
            depth requests allFit targets)) := by
  obtain ⟨directions, _, setCorrect, pairwise⟩ :=
    SchedulerIteration.greedyScheduleCircuit_correct widthPositive
      widthAtLeastTwo requests allFit capacity targets
  exact ⟨directions, setCorrect, pairwise⟩

/-- Unrolling uses one fixed-capacity stage per request; structural retention
and target wiring add no gates. -/
example
    (widthPositive : 0 < width)
    (allFit : requests * LineEnumeration.nonzeroScalarCount width ≤
      Sorting.networkRecords depth) :
    (SchedulerIteration.greedyScheduleCircuit dimension widthPositive depth
      requests allFit).cost DeMorgan.standardCost ≤
      requests * LineEnumeration.scheduledLineEnumerationCostBound
        dimension width depth := by
  exact SchedulerIteration.greedyScheduleCircuit_cost_le
    widthPositive requests allFit

/-- Reading any punctured-line-recoverable resource in the circuit's emitted
record order recovers every request. -/
example
    {valueType : Type*}
    [AddCommMonoid valueType]
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (allFit : requests * LineEnumeration.nonzeroScalarCount width ≤
      Sorting.networkRecords depth)
    (capacity : requests * LineEnumeration.nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width)
    (resource : (Fin dimension -> BinaryExtension width) -> valueType)
    (lineRecovery : ∀ target direction,
      resource target =
        ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
          target direction, resource point) :
    ∃ _directions : Fin requests ->
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width),
      SchedulerIteration.PairwiseDisjointFamily
          (SchedulerIteration.scheduledLineSet widthPositive
            (SchedulerIteration.greedyScheduleOutput dimension widthPositive
              depth requests allFit targets)) ∧
        ∀ request,
          (∑ scalar, resource
            (SchedulerIteration.scheduledLinePoint widthPositive
              (SchedulerIteration.greedyScheduleOutput dimension widthPositive
                depth requests allFit targets) request scalar)) =
            resource (targets request) := by
  obtain ⟨directions, _, _, pairwise, recovers⟩ :=
    ScheduledRecovery.greedyScheduleCircuit_recovers widthPositive
      widthAtLeastTwo requests allFit capacity targets resource lineRecovery
  exact ⟨directions, pairwise, recovers⟩

/-! The public umbrella exports both the exact two-block base and the complete
fixed-rate exponential-range theorem. -/

example (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator) :
    MassProducesAt numerator denominator :=
  EqualBlock.massProducesAt_of_rateBelowHalf numerator denominator
    denominatorPositive rateBelowHalf

example : ExponentialMassProduction :=
  BlockInduction.exponentialMassProduction

/-- The public umbrella exports the unconditional coefficient-one synthesis
premise and hence the sharp Uhlig theorem. -/
example : UhligTheorem.HasSharpOneCopyCost
    LupanovSynthesis.lupanovFamily :=
  LupanovSynthesis.lupanovFamily_hasSharpOneCopyCost

example (depth : Nat -> Nat)
    (depthSmall : UhligTheorem.IsUhligDepth depth) :
    UhligTheorem.HasSharpMassProduction depth :=
  LupanovSynthesis.uhlig_massProduction depth depthSmall

end AlgebraicTests.MassProduction
