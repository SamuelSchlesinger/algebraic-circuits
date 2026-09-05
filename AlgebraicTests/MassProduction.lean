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

/-- Eventual mass-production bounds extend uniformly to every positive input
length through the generic padding API. -/
example {numerator denominator : Nat}
    (production : MassProducesAt numerator denominator) :
    MassProducesAtAllLengths numerator denominator :=
  production.allLengths

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

/-! The nonuniform modules expose checked scheduler and code components.
These tests do not assert the unfinished end-to-end nonuniform cost bound. -/

/-- The GF(4) plane admits seven information symbols in sixteen positions,
with systematic encoding and recovery along every punctured line. -/
example : ∃ code : HighRate.LineCode (BinaryExtension 2) (Fin 2),
    Nat.card code.information = 7 := by
  classical
  let _ := Fintype.ofFinite (BinaryExtension 2)
  have fieldCard : Fintype.card (BinaryExtension 2) = 2 ^ (1 * 2) := by
    simpa only [Nat.card_eq_fintype_card] using
      card_binaryExtension (by decide : 0 < 2)
  simpa using HighRate.existsHighRateLineCode
    (K := BinaryExtension 2) (Coordinate := Fin 2)
    1 2 (by decide) (by decide) fieldCard

/-- The next field width gives the exact dimension thirty-seven. -/
example : ∃ code : HighRate.LineCode (BinaryExtension 3) (Fin 2),
    Nat.card code.information = 37 := by
  classical
  let _ := Fintype.ofFinite (BinaryExtension 3)
  have fieldCard : Fintype.card (BinaryExtension 3) = 2 ^ (1 * 3) := by
    simpa only [Nat.card_eq_fintype_card] using
      card_binaryExtension (by decide : 0 < 3)
  simpa using HighRate.existsHighRateLineCode
    (K := BinaryExtension 3) (Coordinate := Fin 2)
    1 3 (by decide) (by decide) fieldCard

/-- A concrete high-precision rate guarantee avoids approximate arithmetic. -/
example (blocks : Nat) (large : 300 ≤ blocks) :
    100 * 4 ^ blocks ≤ 101 * HighRate.retainedDimension 4 blocks := by
  exact HighRate.retainedDimension_rate 4 blocks 100
    (by decide) (by omega) (by simpa using large)

/-- A source reaches the end of a linked run through shared circuit gates. -/
example :
    (Nonuniform.Propagation.circuit 4).eval DeMorgan.interpretation
      (Fin.append ![false, true, false, false] ![false, false, true, true]) =
        ![false, true, true, true] := by decide

/-- A broken link prevents the source from crossing into another run. -/
example :
    (Nonuniform.Propagation.circuit 4).eval DeMorgan.interpretation
      (Fin.append ![true, false, false, false] ![false, true, false, true]) =
        ![true, true, false, false] := by decide

example :
    (Nonuniform.Propagation.circuit 4).cost DeMorgan.standardCost = 8 :=
  Nonuniform.Propagation.circuit_cost 4

/-- Batched table lookup exports an unconditional circuit-existence theorem
with explicit polynomial overhead and arbitrary repeated query addresses. -/
example (keyWidth valueWidth requests : Nat)
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool) :
    ∃ gates, ∃ lookup : Circuit DeMorgan.signature (requests * keyWidth) gates
        (requests * valueWidth),
      (∀ input request bit, lookup.eval DeMorgan.interpretation input
        (finProdFinEquiv (request, bit)) =
          table (fun addressBit => input (finProdFinEquiv (request, addressBit))) bit) ∧
      lookup.cost DeMorgan.standardCost ≤
        256 * (2 ^ keyWidth + requests) *
          (FiniteParameters.binaryDepth (2 ^ keyWidth + requests) + keyWidth + valueWidth + 2) ^ 5 :=
  Nonuniform.BatchLookup.existsCircuit keyWidth valueWidth requests table

/-- Repeated addresses return separate outputs in their original query
positions. The third query has a different first address bit. -/
example :
    let table := fun address : Fin 2 → Bool => address
    let lookup := Nonuniform.BatchLookup.circuit table
      (by decide : 2 ^ 2 + 3 + 1 = Sorting.networkRecords 3)
    let input : Fin 6 → Bool := ![true, false, true, false, false, true]
    lookup.eval DeMorgan.interpretation input (finProdFinEquiv (1, 0)) = true ∧
      lookup.eval DeMorgan.interpretation input (finProdFinEquiv (2, 0)) = false := by
  dsimp only
  constructor <;> rw [Nonuniform.BatchLookup.circuit_eval] <;> rfl

/-- Equal keys set both duplicate flags, after restoration to input order. -/
example (input : Fin 0 → Bool) (index : Fin (Sorting.networkRecords 1)) :
    (Nonuniform.DuplicateFlags.circuit
      (fun _ : Fin (Sorting.networkRecords 1) => fun _ : Fin 1 =>
        (DeMorgan.Wiring.constant true : DeMorgan.Wiring 0))).eval
      DeMorgan.interpretation input index = true := by
  rw [Nonuniform.DuplicateFlags.circuit_eval_iff]
  fin_cases index
  · exact ⟨⟨1, by decide⟩, by decide, rfl⟩
  · exact ⟨⟨0, by decide⟩, by decide, rfl⟩

/-- Different keys leave both duplicate flags false. -/
example (input : Fin 0 → Bool) (index : Fin (Sorting.networkRecords 1)) :
    (Nonuniform.DuplicateFlags.circuit
      (fun record : Fin (Sorting.networkRecords 1) => fun _ : Fin 1 =>
        (DeMorgan.Wiring.constant (decide (record.val = 1)) : DeMorgan.Wiring 0))).eval
      DeMorgan.interpretation input index = false := by
  apply Bool.eq_false_iff.mpr
  intro isTrue
  obtain ⟨other, different, sameKey⟩ :=
    (Nonuniform.DuplicateFlags.circuit_eval_iff _ input index).mp isTrue
  have sameBit := congrFun sameKey 0
  fin_cases index <;> fin_cases other
  all_goals first | exact different rfl | cases sameBit

/-- Repeated source keys are aggregated, repeated queries agree, and an
absent key returns false. -/
example (input : Fin 0 → Bool) (request : Fin 3) :
    (Nonuniform.BatchOr.circuit
      (fun _ : Fin 2 => fun _ : Fin 1 => DeMorgan.Wiring.constant true)
      (fun source : Fin 2 => fun _ : Fin 1 => DeMorgan.Wiring.constant (decide (source.val = 1)))
      (fun query : Fin 3 => fun _ : Fin 1 => DeMorgan.Wiring.constant (decide (query.val ≠ 0)))
      (show 2 + 3 + 3 = Sorting.networkRecords 3 from rfl)).eval
        DeMorgan.interpretation input (finProdFinEquiv (request, (0 : Fin 1))) =
      decide (request.val ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [Nonuniform.BatchOr.circuit_eval_iff]
  simp only [DeMorgan.Wiring.eval_constant, funext_iff]
  fin_cases request <;> decide

/-- An empty source array produces false even for a valid query. -/
example (input : Fin 0 → Bool) :
    (Nonuniform.BatchOr.circuit
      (fun source : Fin 0 => Fin.elim0 source : Fin 0 → Fin 1 → DeMorgan.Wiring 0)
      (fun source : Fin 0 => Fin.elim0 source : Fin 0 → Fin 1 → DeMorgan.Wiring 0)
      (fun _ : Fin 1 => fun _ : Fin 1 => DeMorgan.Wiring.constant true)
      (show 0 + 1 + 0 = Sorting.networkRecords 0 from rfl)).eval
        DeMorgan.interpretation input (finProdFinEquiv ((0 : Fin 1), (0 : Fin 1))) = false := by
  apply Bool.eq_false_iff.mpr
  intro isTrue
  obtain ⟨source, _⟩ :=
    (Nonuniform.BatchOr.circuit_eval_iff _ _ _ _ input (0 : Fin 1) (0 : Fin 1)).mp isTrue
  exact Fin.elim0 source

/-- Invalid padding slots and equal points from different candidates do not
create conflicts. Each candidate has only one valid point here. -/
example (input : Fin 0 → Bool) (index : Fin (Sorting.networkRecords 2)) :
    (Nonuniform.PointConflicts.circuit
      (fun point : Fin (Sorting.networkRecords 2) => fun _ : Fin 1 => decide (2 ≤ point.val))
      (fun point : Fin (Sorting.networkRecords 2) => DeMorgan.Wiring.constant (decide (point.val % 2 = 0)))
      (fun _ : Fin (Sorting.networkRecords 2) => fun _ : Fin 1 => DeMorgan.Wiring.constant true)
      (fun source : Fin 0 => Fin.elim0 source : Fin 0 → Fin 1 → DeMorgan.Wiring 0)
      (fun source : Fin 0 => Fin.elim0 source : Fin 0 → DeMorgan.Wiring 0)
      (show 0 + Sorting.networkRecords 2 + 0 = Sorting.networkRecords 2 by omega)).eval
        DeMorgan.interpretation input index = false := by
  apply Bool.eq_false_iff.mpr
  intro flagged
  obtain ⟨validIndex, collision | occupied⟩ :=
    (Nonuniform.PointConflicts.circuit_eval_iff _ _ _ _ _ _ input index).mp flagged
  · obtain ⟨other, different, sameGroup, validOther, _⟩ := collision
    have sameGroupBit := congrFun sameGroup 0
    fin_cases index <;> fin_cases other
    all_goals solve | exact different rfl | cases validIndex | cases validOther | cases sameGroupBit
  · obtain ⟨source, _⟩ := occupied
    exact Fin.elim0 source

/-- Empty point lists are clean, including when the shared input is empty. -/
example (input : Fin 0 → Bool) (request : Fin 2) :
    (Nonuniform.GroupClean.flagsCircuit
      (fun _ : Fin 2 => fun slot : Fin 0 => Fin.elim0 slot : Fin 2 → Fin 0 → Fin 0)).eval
      DeMorgan.interpretation input request = true := by
  exact (Nonuniform.GroupClean.flagsCircuit_eval_iff _ input request).mpr (fun slot => Fin.elim0 slot)

/-- Fixed offsets translate both source bits with at most one gate per bit. -/
example (input : Fin 2 → Bool) (point : Fin 2) (bit : Fin 2) :
    (Nonuniform.ConstantTranslations.circuit
      (fun point : Fin 2 => fun _ : Fin 2 => decide (point.val = 1))
      (fun _ : Fin 2 => fun bit : Fin 2 => DeMorgan.Wiring.input bit)).eval
        DeMorgan.interpretation input (finProdFinEquiv (point, bit)) =
      (input bit ^^ decide (point.val = 1)) :=
  Nonuniform.ConstantTranslations.circuit_eval _ _ input point bit

/-- Exact phase sizes include the final singleton phase. -/
example :
    Nonuniform.acceptedCount 0 = 1 ∧ Nonuniform.pendingCount 0 = 0 ∧
    Nonuniform.acceptedCount 3 = 4 ∧ Nonuniform.pendingCount 3 = 4 := by decide

/-- The concrete GF(4)^8 regime admits the budget for eight simultaneous requests. -/
example :
    512 * 8 * Nat.card (BinaryExtension 2) ≤
      Nat.card (ℙ (BinaryExtension 2) (Fin 8 → BinaryExtension 2)) := by
  rw [card_projectiveDirections_div, card_binaryExtension (by decide : 0 < 2)]
  norm_num

/-- Power-of-two padding preserves each actual menu entry before the repeated suffix. -/
example (menu : Fin 3 → Bool) :
    Nonuniform.padMenu menu (by decide) (show 3 ≤ 4 by decide) (0 : Fin 4) = menu 0 ∧
    Nonuniform.padMenu menu (by decide) (show 3 ≤ 4 by decide) (2 : Fin 4) = menu 2 ∧
    Nonuniform.padMenu menu (by decide) (show 3 ≤ 4 by decide) (3 : Fin 4) = menu 0 := by
  simp [Nonuniform.padMenu]

/-- Fixed identity prefixes distinguish requests even when every payload repeats. -/
example (input : Fin 0 → Bool) :
    Function.Injective (Nonuniform.TaggedBuffer.data
      (fun _ : Fin (Sorting.networkRecords 3) => fun _ : Fin 1 =>
        (DeMorgan.Wiring.constant false : DeMorgan.Wiring 0)) input) :=
  Nonuniform.TaggedBuffer.data_injective _ input

/-- Compaction preserves the selected order after a nontrivial request swap. -/
example :
    Nonuniform.BufferOrder.advance (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)
      (Equiv.swap (0 : Fin 3) 2) (show 2 + 1 = 3 from rfl) (.inl (1 : Fin 3)) = 3 ∧
    Nonuniform.BufferOrder.advance (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)
      (Equiv.swap (0 : Fin 3) 2) (show 2 + 1 = 3 from rfl) (.inr (0 : Fin 1)) = 1 := by
  constructor
  · change Nonuniform.BufferOrder.advance _ _ _ (.inl (Fin.natAdd 1 (0 : Fin 2))) = _
    rw [Nonuniform.BufferOrder.advance_accepted]
    decide
  · rw [Nonuniform.BufferOrder.advance_pending]
    decide

/-- The complete scheduler handles eight identical targets in GF(4)^8.
This uses the semantic endpoint, without evaluating a huge sorting circuit. -/
example :
    ∃ gates, ∃ scheduler : Circuit DeMorgan.signature 0 gates
      (Nonuniform.BufferInput.inputWidth 8 0 19 4 16),
      scheduler.cost DeMorgan.standardCost ≤
        8 * 4 * Nonuniform.BufferIteration.polynomialFactor 8 8 2 19 ∧
      ∀ input : Fin 0 → Bool,
        ∃ state : Nonuniform.BufferModel.State 8 8 0 8 2,
          scheduler.eval DeMorgan.interpretation input =
            Nonuniform.BufferModel.input (by decide : 0 < 2) state
              (Nonuniform.TaggedBuffer.data (depth := 3)
                (fun _ : Fin 8 => fun bit : Fin 16 =>
                  DeMorgan.Wiring.constant (binaryExtensionVectorBits (by decide : 0 < 2)
                    (0 : Fin 8 → BinaryExtension 2) bit)) input)
              (fun _ => 0) ∧
          Nonuniform.BufferModel.WellScheduled state (fun _ => 0) := by
  have budget : 512 * Sorting.networkRecords 3 * Nat.card (BinaryExtension 2) ≤
      Nat.card (ℙ (BinaryExtension 2) (Fin 8 → BinaryExtension 2)) := by
    rw [card_projectiveDirections_div, card_binaryExtension (by decide : 0 < 2)]
    norm_num [Sorting.networkRecords]
  obtain ⟨gates, scheduler, bound, correct⟩ := Nonuniform.Scheduler.existsCircuit
    (by decide : 0 < 2) (by decide : 0 < 8) budget
    (fun _ : Fin (Sorting.networkRecords 3) => fun bit : Fin 16 =>
      (DeMorgan.Wiring.constant (binaryExtensionVectorBits (by decide : 0 < 2)
        (0 : Fin 8 → BinaryExtension 2) bit) : DeMorgan.Wiring 0)) id
  exact ⟨gates, scheduler, bound, fun input => correct input (fun _ => 0) (fun _ _ => rfl)⟩

/-- Resource indexing charges three actual copies and three actual basis
bits, without rounding either dimension to a power of two. -/
example : HighRate.ResourceLayout.count 3 2 3 = 576 := rfl

/-- Exact resource indexing preserves each copy, point, and basis-bit coordinate. -/
example (copy : Fin 3) (point : Fin 64) (bit : Fin 3) :
    HighRate.ResourceLayout.atIndex (HighRate.ResourceLayout.index (dimension := 2) copy point bit) =
      (copy, point, bit) := HighRate.ResourceLayout.atIndex_index (dimension := 2) copy point bit

/-- A masked XOR fold ignores the middle slot for both request rows. -/
example (input : Fin (2 * 3) → Bool) (request : Fin 2) :
    (Nonuniform.MaskedXor.circuit (fun slot : Fin 3 => decide (slot.val ≠ 1)) 2).eval
      DeMorgan.interpretation input request =
        (input (finProdFinEquiv (request, (0 : Fin 3))) ^^ input (finProdFinEquiv (request, (2 : Fin 3)))) := by
  rw [Nonuniform.MaskedXor.circuit_eval]
  simp [Fin.sum_univ_succ, Bool.add_eq_xor]

/-- Shared scatter/evaluate/gather ignores an inactive duplicate key while
returning the two active incidences' own inputs through the resource bank. -/
example :
    ∃ gates, ∃ evaluated : Circuit DeMorgan.signature 2 gates 3,
      ∀ (input : Fin 2 → Bool) (incidence : Fin 3), incidence.val ≠ 1 →
        evaluated.eval DeMorgan.interpretation input incidence =
          input (if incidence.val = 0 then (0 : Fin 2) else 1) := by
  let keys := fun incidence : Fin 3 => fun _ : Fin 1 =>
    (DeMorgan.Wiring.constant (decide (incidence.val = 2)) : DeMorgan.Wiring 2)
  let suffixes := fun incidence : Fin 3 => fun _ : Fin 1 =>
    (DeMorgan.Wiring.input (if incidence.val = 0 then (0 : Fin 2) else 1) : DeMorgan.Wiring 2)
  let resourceKeys := fun resource : Fin 2 => fun _ : Fin 1 => decide (resource.val = 1)
  have distinct : Function.Injective resourceKeys := by
    intro left right equal
    have bit := congrFun equal 0
    fin_cases left <;> fin_cases right <;> first | rfl | cases bit
  obtain ⟨gates, evaluated, _, correct⟩ := Nonuniform.IncidenceEvaluation.existsCircuit
    (fun incidence : Fin 3 => decide (incidence.val ≠ 1)) keys suffixes resourceKeys distinct
    (fun _ : Fin 2 => Circuit.id DeMorgan.signature 1)
  refine ⟨gates, evaluated, ?_⟩
  intro input incidence active
  let resource : Fin 2 := if incidence.val = 0 then 0 else 1
  have matching : (fun bit => (keys incidence bit).eval input) = resourceKeys resource := by
    funext bit
    fin_cases incidence <;> simp_all [keys, resourceKeys, resource]
  have unique : ∀ other : Fin 3, decide (other.val ≠ 1) = true →
      (fun bit => (keys other bit).eval input) = (fun bit => (keys incidence bit).eval input) → other = incidence := by
    intro other otherActive equal
    have bit := congrFun equal 0
    fin_cases incidence <;> fin_cases other <;> simp_all [keys]
  have output := correct input incidence resource (by simpa using active) matching unique
  simpa only [Circuit.eval_id, suffixes, DeMorgan.Wiring.eval_input] using output

end AlgebraicTests.MassProduction
