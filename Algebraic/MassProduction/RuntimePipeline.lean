import Algebraic.MassProduction.DynamicGatherDecoder
import Algebraic.MassProduction.RuntimePacking
import Algebraic.MassProduction.RoutingAssembly

/-!
# Runtime-prefix mass-production pipeline

This module replaces the hardwired-prefix front end of `RoutingAssembly` by
the canonical runtime packing circuit.  Every request supplies its prefix and
suffix at runtime.  The prefix determines both its tensor-code target point
and a one-hot basis-coordinate selector; the suffix is passed unchanged to
the routed resource bank.

All reindexing and padding layers are explicit zero-gate wiring circuits.  No
type-class instances are introduced.
-/

namespace Algebraic
namespace MassProduction
namespace RuntimePipeline

universe u

variable {Prefix : Type u}

open scoped LinearAlgebra.Projectivization
open CanonicalPacking
open DynamicGatherDecoder
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open ResourceEvaluation
open RoutingAssembly
open RuntimePacking
open SchedulerIteration
open Sorting

/-! ## Per-request runtime data -/

/-- One request contains a little-endian prefix followed by its suffix. -/
@[reducible] def requestInputCount
    (prefixWidth suffixWidth : Nat) : Nat :=
  prefixWidth + suffixWidth

/-- One processed request contains target bits, selector bits, then suffix. -/
@[reducible] def requestDataCount
    (dimension width suffixWidth : Nat) : Nat :=
  RuntimePacking.outputCount dimension width + suffixWidth

/-- Select the prefix block of one request. -/
def requestPrefixInputIndex
    (prefixWidth suffixWidth : Nat) :
    Fin prefixWidth -> Fin (requestInputCount prefixWidth suffixWidth) :=
  Fin.castAdd suffixWidth

/-- Select the suffix block of one request. -/
def requestSuffixInputIndex
    (prefixWidth suffixWidth : Nat) :
    Fin suffixWidth -> Fin (requestInputCount prefixWidth suffixWidth) :=
  Fin.natAdd prefixWidth

/-- Process one runtime prefix and retain its suffix. -/
noncomputable def requestDataCircuit
    (prefixWidth dimension suffixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :=
  ((RuntimePacking.circuit prefixWidth dimension widthPositive
    gridPositive).mapInputs
      (requestPrefixInputIndex prefixWidth suffixWidth)).parallel
    ((Circuit.id DeMorgan.signature
      (requestInputCount prefixWidth suffixWidth)).mapOutputs
        (requestSuffixInputIndex prefixWidth suffixWidth))

/-- Process all request rows independently. -/
noncomputable def requestDataArrayCircuit
    (totalRequests prefixWidth dimension suffixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :=
  (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
    gridPositive).replicate totalRequests

/-- Read one request row from the complete runtime input. -/
def requestInput
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) :
    Fin (requestInputCount prefixWidth suffixWidth) -> Bool :=
  directProductInput input request

/-- Read one request's runtime prefix. -/
def requestPrefix
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin prefixWidth -> Bool :=
  fun bit => requestInput input request
    (requestPrefixInputIndex prefixWidth suffixWidth bit)

/-- Read one request's runtime suffix. -/
def requestSuffix
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin suffixWidth -> Bool :=
  fun bit => requestInput input request
    (requestSuffixInputIndex prefixWidth suffixWidth bit)

/-- Local processed-request index of one target-point bit. -/
def requestDataTargetIndex
    (dimension width suffixWidth : Nat)
    (bit : Fin (pointBitWidth dimension width)) :
    Fin (requestDataCount dimension width suffixWidth) :=
  ⟨bit.val, by
    unfold requestDataCount RuntimePacking.outputCount pointBitWidth
    omega⟩

/-- Local processed-request index of one selector bit. -/
def requestDataSelectorIndex
    (dimension width suffixWidth : Nat)
    (bit : Fin width) : Fin (requestDataCount dimension width suffixWidth) :=
  ⟨pointBitWidth dimension width + bit.val, by
    unfold requestDataCount RuntimePacking.outputCount pointBitWidth
    omega⟩

/-- Local processed-request index of one suffix bit. -/
def requestDataSuffixIndex
    (dimension width suffixWidth : Nat)
    (bit : Fin suffixWidth) :
    Fin (requestDataCount dimension width suffixWidth) :=
  ⟨RuntimePacking.outputCount dimension width + bit.val, by
    unfold requestDataCount
    omega⟩

theorem requestDataCircuit_eval_target
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (requestInputCount prefixWidth suffixWidth) -> Bool)
    (coordinate : Fin dimension)
    (bit : Fin width) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).eval DeMorgan.interpretation input
        (requestDataTargetIndex dimension width suffixWidth
          (finProdFinEquiv (coordinate, bit))) =
      finiteIndexBits width
        (CanonicalPacking.symbolDigits packingFits
          (RuntimePacking.source
            (fun prefixBit => input
              (requestPrefixInputIndex prefixWidth suffixWidth prefixBit)))
          coordinate) bit := by
  rw [requestDataCircuit, Circuit.eval_parallel]
  rw [show requestDataTargetIndex dimension width suffixWidth
        (finProdFinEquiv (coordinate, bit)) =
      Fin.castAdd suffixWidth
        (Fin.castAdd width (finProdFinEquiv (coordinate, bit))) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Circuit.eval_mapInputs]
  exact RuntimePacking.circuit_eval_target widthPositive gridPositive
    packingFits _ coordinate bit

theorem requestDataCircuit_eval_selector
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (requestInputCount prefixWidth suffixWidth) -> Bool)
    (candidate : Fin width) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).eval DeMorgan.interpretation input
        (requestDataSelectorIndex dimension width suffixWidth candidate) =
      decide (candidate =
        CanonicalPacking.bitIndex packingFits
          (RuntimePacking.source
            (fun prefixBit => input
              (requestPrefixInputIndex prefixWidth suffixWidth prefixBit)))) := by
  rw [requestDataCircuit, Circuit.eval_parallel]
  rw [show requestDataSelectorIndex dimension width suffixWidth candidate =
      Fin.castAdd suffixWidth
        (Fin.natAdd (dimension * width) candidate) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Circuit.eval_mapInputs]
  exact RuntimePacking.circuit_eval_selector widthPositive gridPositive
    packingFits _ candidate

theorem requestDataCircuit_eval_suffix
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (input : Fin (requestInputCount prefixWidth suffixWidth) -> Bool)
    (bit : Fin suffixWidth) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).eval DeMorgan.interpretation input
        (requestDataSuffixIndex dimension width suffixWidth bit) =
      input (requestSuffixInputIndex prefixWidth suffixWidth bit) := by
  rw [requestDataCircuit, Circuit.eval_parallel]
  rw [show requestDataSuffixIndex dimension width suffixWidth bit =
      Fin.natAdd (RuntimePacking.outputCount dimension width) bit by
    apply Fin.ext
    rfl]
  rw [Fin.append_right, Circuit.eval_mapOutputs, Circuit.eval_id]
  rfl

/-- Prefix index represented by one runtime request row. -/
def requestSource
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin (2 ^ prefixWidth) :=
  RuntimePacking.source (requestPrefix input request)

/-- Canonical packed target selected by one runtime request row. -/
noncomputable def requestTarget
    (widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) :
    Fin dimension -> BinaryExtension width :=
  packedTargetPoint widthPositive
    (CanonicalPacking.packedPlacement widthPositive packingFits)
    (requestSource input request)

/-- Canonical basis coordinate selected by one runtime request row. -/
noncomputable def requestSelectedBit
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin width :=
  CanonicalPacking.bitIndex packingFits (requestSource input request)

theorem requestDataArrayCircuit_eval_target
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests)
    (bit : Fin (pointBitWidth dimension width)) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).eval DeMorgan.interpretation input
        (finProdFinEquiv
          (request, requestDataTargetIndex dimension width suffixWidth bit)) =
      binaryExtensionVectorBits widthPositive
        (requestTarget widthPositive packingFits input request) bit := by
  obtain ⟨⟨coordinate, coordinateBit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := dimension) (n := width)).surjective bit
  rw [requestDataArrayCircuit, Circuit.eval_replicate_apply,
    requestDataCircuit_eval_target widthPositive gridPositive packingFits]
  have packedBits := congrFun
    (CanonicalPacking.packedTargetPoint_bits widthPositive packingFits
      (requestSource input request))
    (finProdFinEquiv (coordinate, coordinateBit))
  change finiteIndexBits width
      (CanonicalPacking.symbolDigits packingFits
        (requestSource input request) coordinate) coordinateBit =
    binaryExtensionVectorBits widthPositive
      (requestTarget widthPositive packingFits input request)
      (finProdFinEquiv (coordinate, coordinateBit))
  simpa [requestTarget] using packedBits.symm

theorem requestDataArrayCircuit_eval_selector
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests)
    (candidate : Fin width) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).eval DeMorgan.interpretation input
        (finProdFinEquiv
          (request,
            requestDataSelectorIndex dimension width suffixWidth candidate)) =
      decide (candidate = requestSelectedBit packingFits input request) := by
  rw [requestDataArrayCircuit, Circuit.eval_replicate_apply,
    requestDataCircuit_eval_selector widthPositive gridPositive packingFits]
  rfl

theorem requestDataArrayCircuit_eval_suffix
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests)
    (bit : Fin suffixWidth) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).eval DeMorgan.interpretation input
        (finProdFinEquiv
          (request, requestDataSuffixIndex dimension width suffixWidth bit)) =
      requestSuffix input request bit := by
  rw [requestDataArrayCircuit, Circuit.eval_replicate_apply,
    requestDataCircuit_eval_suffix]
  rfl

@[simp] theorem requestDataCircuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).cost DeMorgan.standardCost =
      (RuntimePacking.circuit prefixWidth dimension widthPositive
        gridPositive).cost DeMorgan.standardCost := by
  simp [requestDataCircuit]

@[simp] theorem requestDataArrayCircuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).cost DeMorgan.standardCost =
      totalRequests *
        (RuntimePacking.circuit prefixWidth dimension widthPositive
          gridPositive).cost DeMorgan.standardCost := by
  simp [requestDataArrayCircuit]

/-! ## Runtime target padding and scheduler input -/

/-- Wire actual runtime target bits into a rectangular grouped target array;
unused request slots receive a fixed dummy point. -/
noncomputable def paddedTargetSpecification
    (totalRequests groups requestsPerGroup dimension width suffixWidth : Nat)
    (widthPositive : 0 < width)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    Fin (groups *
      (requestsPerGroup * pointBitWidth dimension width)) ->
      DeMorgan.Wiring
        (totalRequests * requestDataCount dimension width suffixWidth) :=
  fun output =>
    let groupAndRest := (finProdFinEquiv
      (m := groups)
      (n := requestsPerGroup * pointBitWidth dimension width)).symm output
    let requestAndBit := (finProdFinEquiv
      (m := requestsPerGroup)
      (n := pointBitWidth dimension width)).symm groupAndRest.2
    let flatRequest := finProdFinEquiv
      (groupAndRest.1, requestAndBit.1)
    if live : flatRequest.val < totalRequests then
      .input (finProdFinEquiv
        (⟨flatRequest.val, live⟩,
          requestDataTargetIndex dimension width suffixWidth
            requestAndBit.2))
    else
      .constant
        (binaryExtensionVectorBits widthPositive dummyTarget requestAndBit.2)

/-- Zero-cost rectangular padding of the actual runtime target array. -/
noncomputable def paddedTargetCircuit
    (totalRequests groups requestsPerGroup dimension width suffixWidth : Nat)
    (widthPositive : 0 < width)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  DeMorgan.Wiring.circuit
    (paddedTargetSpecification totalRequests groups requestsPerGroup
      dimension width suffixWidth widthPositive dummyTarget)

@[simp] theorem paddedTargetCircuit_cost
    (widthPositive : 0 < width)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (paddedTargetCircuit totalRequests groups requestsPerGroup dimension width
      suffixWidth widthPositive dummyTarget).cost DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

theorem paddedTargetCircuit_eval
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool)
    (targetCorrect : forall request bit,
      input (finProdFinEquiv
        (request, requestDataTargetIndex dimension width suffixWidth bit)) =
      binaryExtensionVectorBits widthPositive (targets request) bit) :
    (paddedTargetCircuit totalRequests groups requestsPerGroup dimension width
      suffixWidth widthPositive dummyTarget).eval DeMorgan.interpretation
        input =
      groupedTargetArrayBits widthPositive
        (paddedGroupedTargets capacity targets dummyTarget) := by
  funext output
  obtain ⟨⟨group, rest⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := groups)
      (n := requestsPerGroup * pointBitWidth dimension width)).surjective
      output
  obtain ⟨⟨request, bit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := requestsPerGroup)
      (n := pointBitWidth dimension width)).surjective rest
  rw [paddedTargetCircuit, DeMorgan.Wiring.circuit_eval]
  by_cases live :
      (finProdFinEquiv (group, request)).val < totalRequests
  · have live' :
        request.val + requestsPerGroup * group.val < totalRequests := by
      simpa [finProdFinEquiv] using live
    simp [paddedTargetSpecification, groupedTargetArrayBits,
      targetArrayBits, paddedGroupedTargets, live', targetCorrect]
  · have live' :
        ¬request.val + requestsPerGroup * group.val < totalRequests := by
      simpa [finProdFinEquiv] using live
    simp [paddedTargetSpecification, groupedTargetArrayBits,
      targetArrayBits, paddedGroupedTargets, live']

/-! ## Schedule, suffix, and selector assembly -/

/-- Row-major suffix view of processed request data. -/
def processedSuffixArray
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool) :
    Fin (totalRequests * suffixWidth) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := suffixWidth)).symm flat
    input (finProdFinEquiv
      (requestAndBit.1,
        requestDataSuffixIndex dimension width suffixWidth requestAndBit.2))

/-- Row-major selector view of processed request data. -/
def processedSelectorArray
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool) :
    Fin (totalRequests * width) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := width)).symm flat
    input (finProdFinEquiv
      (requestAndBit.1,
        requestDataSelectorIndex dimension width suffixWidth requestAndBit.2))

/-- Processed suffixes followed by processed runtime selectors. -/
@[reducible] def suffixSelectorCount
    (totalRequests suffixWidth width : Nat) : Nat :=
  totalRequests * suffixWidth + totalRequests * width

/-- Zero-cost wiring specification that retains every processed suffix and
selector. -/
noncomputable def suffixSelectorSpecification
    (totalRequests dimension width suffixWidth : Nat) :
    Fin (suffixSelectorCount totalRequests suffixWidth width) ->
      DeMorgan.Wiring
        (totalRequests * requestDataCount dimension width suffixWidth) :=
  Fin.addCases
    (fun suffix =>
      let requestAndBit := (finProdFinEquiv
        (m := totalRequests) (n := suffixWidth)).symm suffix
      .input (finProdFinEquiv
        (requestAndBit.1,
          requestDataSuffixIndex dimension width suffixWidth
            requestAndBit.2)))
    (fun selector =>
      let requestAndBit := (finProdFinEquiv
        (m := totalRequests) (n := width)).symm selector
      .input (finProdFinEquiv
        (requestAndBit.1,
          requestDataSelectorIndex dimension width suffixWidth
            requestAndBit.2)))

/-- Wiring circuit that exposes processed suffixes and runtime selectors. -/
noncomputable def suffixSelectorCircuit
    (totalRequests dimension width suffixWidth : Nat) :=
  DeMorgan.Wiring.circuit
    (suffixSelectorSpecification totalRequests dimension width suffixWidth)

@[simp] theorem suffixSelectorCircuit_eval
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool) :
    (suffixSelectorCircuit totalRequests dimension width suffixWidth).eval
        DeMorgan.interpretation input =
      Fin.append (processedSuffixArray input)
        (processedSelectorArray input) := by
  funext output
  refine Fin.addCases (fun suffix => ?_) (fun selector => ?_) output
  · rw [suffixSelectorCircuit, DeMorgan.Wiring.circuit_eval]
    simp [suffixSelectorSpecification, processedSuffixArray]
  · rw [suffixSelectorCircuit, DeMorgan.Wiring.circuit_eval]
    simp [suffixSelectorSpecification, processedSelectorArray]

@[simp] theorem suffixSelectorCircuit_cost :
    (suffixSelectorCircuit totalRequests dimension width suffixWidth).cost
        DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

/-- Scheduler output followed by runtime suffixes and one-hot selectors. -/
noncomputable def scheduleSuffixSelectorCircuit
    (totalRequests groups requestsPerGroup dimension width
      suffixWidth schedulerDepth : Nat)
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  ((groupedScheduleCircuit dimension widthPositive schedulerDepth groups
      requestsPerGroup allFit).comp
    (paddedTargetCircuit totalRequests groups requestsPerGroup dimension width
      suffixWidth widthPositive dummyTarget)).parallel
    (suffixSelectorCircuit totalRequests dimension width suffixWidth)

theorem scheduleSuffixSelectorCircuit_eval
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords schedulerDepth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool)
    (targetCorrect : forall request bit,
      input (finProdFinEquiv
        (request, requestDataTargetIndex dimension width suffixWidth bit)) =
      binaryExtensionVectorBits widthPositive (targets request) bit) :
    (scheduleSuffixSelectorCircuit totalRequests groups requestsPerGroup
      dimension width suffixWidth schedulerDepth widthPositive
      allFit dummyTarget).eval DeMorgan.interpretation input =
      Fin.append
        (groupedScheduleOutput dimension widthPositive schedulerDepth groups
          requestsPerGroup allFit
          (paddedGroupedTargets capacity targets dummyTarget))
        (Fin.append (processedSuffixArray input)
          (processedSelectorArray input)) := by
  rw [scheduleSuffixSelectorCircuit, Circuit.eval_parallel,
    Circuit.eval_comp, paddedTargetCircuit_eval widthPositive capacity
      dummyTarget targets input targetCorrect,
    suffixSelectorCircuit_eval]
  rfl

@[simp] theorem scheduleSuffixSelectorCircuit_cost
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (scheduleSuffixSelectorCircuit totalRequests groups requestsPerGroup
      dimension width suffixWidth schedulerDepth widthPositive
      allFit dummyTarget).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        requestsPerGroup allFit).cost DeMorgan.standardCost := by
  simp [scheduleSuffixSelectorCircuit]

/-! ## Dynamic scatter, evaluation, gather, and decoding -/

/-- Scheduler output, then row-major suffixes, then row-major selectors. -/
@[reducible] noncomputable def scheduledDataCount
    (groups requestsPerGroup dimension width totalRequests suffixWidth : Nat) :
    Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    suffixSelectorCount totalRequests suffixWidth width

/-- Embed the scheduler-and-suffix prefix consumed by scatter routing. -/
noncomputable def scheduledScatterInputIndex
    (index : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth)) :
    Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.addCases
    (fun schedule => Fin.castAdd
      (suffixSelectorCount totalRequests suffixWidth width) schedule)
    (fun suffix => Fin.natAdd
      (scheduleBitCount groups requestsPerGroup dimension width)
      (Fin.castAdd (totalRequests * width) suffix))
    index

/-- Embed the final selector block. -/
noncomputable def scheduledSelectorInputIndex
    (selector : Fin (totalRequests * width)) :
    Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width)
    (Fin.natAdd (totalRequests * suffixWidth) selector)

/-- Scheduler-and-suffix view of scheduled runtime data. -/
noncomputable def scheduledScatterInput
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool) :
    Fin (scatterAssemblyInputCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool :=
  fun index => input (scheduledScatterInputIndex index)

/-- Selector view of scheduled runtime data. -/
noncomputable def scheduledSelectorInput
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool) :
    Fin (totalRequests * width) -> Bool :=
  fun selector => input (scheduledSelectorInputIndex selector)

@[simp] theorem scheduledScatterInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool)
    (selectors : Fin (totalRequests * width) -> Bool) :
    scheduledScatterInput
        (Fin.append schedule (Fin.append suffixes selectors)) =
      Fin.append schedule suffixes := by
  funext index
  refine Fin.addCases (fun scheduleIndex => ?_)
    (fun suffixIndex => ?_) index
  · simp [scheduledScatterInput, scheduledScatterInputIndex]
  · simp [scheduledScatterInput, scheduledScatterInputIndex]

@[simp] theorem scheduledSelectorInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool)
    (selectors : Fin (totalRequests * width) -> Bool) :
    scheduledSelectorInput
        (Fin.append schedule (Fin.append suffixes selectors)) =
      selectors := by
  funext selector
  simp [scheduledSelectorInput, scheduledSelectorInputIndex]

/-- Preserve runtime selectors alongside the gathered incidence records. -/
noncomputable def gatherWithSelectorsCircuit
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :=
  let scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth := by
    rw [← scatterRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  ((scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
    orderWidth incidenceFits capacity scatterRecordCount
    scatterDestinationFits gateCounts resourceCircuits
    gatherRecordCount).mapInputs scheduledScatterInputIndex).parallel
    ((Circuit.id DeMorgan.signature
      (scheduledDataCount groups requestsPerGroup dimension width
        totalRequests suffixWidth)).mapOutputs
        scheduledSelectorInputIndex)

theorem gatherWithSelectorsCircuit_eval
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool) :
    (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).eval DeMorgan.interpretation input =
      let scatterDestinationFits :
          2 ^ (groupBitWidth + dimension * width) <=
            networkRecords scatterDepth := by
        rw [← scatterRecordCount]
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      Fin.append
        ((scatterResourceGatherCircuit groupsPositive suffixWidth
          groupBitWidth orderWidth incidenceFits capacity scatterRecordCount
          scatterDestinationFits gateCounts resourceCircuits
          gatherRecordCount).eval DeMorgan.interpretation
            (scheduledScatterInput input))
        (scheduledSelectorInput input) := by
  rw [gatherWithSelectorsCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_mapOutputs, Circuit.eval_id]
  rfl

@[simp] theorem gatherWithSelectorsCircuit_cost
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount (by
          rw [← scatterRecordCount]
          exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
        gateCounts resourceCircuits gatherRecordCount).cost
          DeMorgan.standardCost := by
  simp [gatherWithSelectorsCircuit]

/-- Scatter, resource evaluation, gather, and runtime-selected decoding. -/
noncomputable def dynamicAssembledPipelineCircuit
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :=
  let gatherDestinationFits :
      totalRequests * nonzeroScalarCount width <=
        networkRecords gatherDepth := by
    rw [← gatherRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  (DynamicGatherDecoder.circuit
    (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
    (metadataWidth := orderWidth + 1)
    (valueWidth := width) gatherDestinationFits).comp
      (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount gateCounts
        resourceCircuits gatherRecordCount)

set_option maxHeartbeats 1500000 in
/-- When the appended selectors are one-hot at the specified coordinates,
the dynamic pipeline is exactly the established fixed-selector pipeline. -/
theorem dynamicAssembledPipelineCircuit_eq_fixed
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool)
    (selectorCorrect : forall request bit,
      scheduledSelectorInput input (finProdFinEquiv (request, bit)) =
        decide (bit = (placement (requestSource request)).2)) :
    (dynamicAssembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).eval DeMorgan.interpretation input =
      (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity placement requestSource
        scatterRecordCount gateCounts resourceCircuits
        gatherRecordCount).eval DeMorgan.interpretation
          (scheduledScatterInput input) := by
  let selectedBit : Fin totalRequests -> Fin width :=
    fun request => (placement (requestSource request)).2
  have selectorsEqual :
      scheduledSelectorInput input =
        fun flat =>
          let requestAndBit := (finProdFinEquiv
            (m := totalRequests) (n := width)).symm flat
          decide (requestAndBit.2 = selectedBit requestAndBit.1) := by
    funext flat
    obtain ⟨⟨request, bit⟩, rfl⟩ :=
      (finProdFinEquiv
        (m := totalRequests) (n := width)).surjective flat
    simpa [selectedBit] using selectorCorrect request bit
  rw [dynamicAssembledPipelineCircuit, Circuit.eval_comp,
    gatherWithSelectorsCircuit_eval]
  dsimp only
  rw [selectorsEqual,
    DynamicGatherDecoder.circuit_eval_append_oneHot]
  rw [assembledPipelineCircuit, Circuit.eval_comp]

@[simp] theorem dynamicAssembledPipelineCircuit_cost
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (dynamicAssembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount gateCounts
        resourceCircuits gatherRecordCount).cost DeMorgan.standardCost +
      totalRequests * (nonzeroScalarCount width * width * 5) := by
  rw [dynamicAssembledPipelineCircuit, Circuit.cost_comp,
    DynamicGatherDecoder.circuit_cost]

/-! ## Complete runtime-prefix assembly -/

/-- Row-major suffix array of the original runtime request input. -/
def runtimeSuffixArray
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    Fin (totalRequests * suffixWidth) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := suffixWidth)).symm flat
    requestSuffix input requestAndBit.1 requestAndBit.2

/-- Row-major one-hot selectors determined by all runtime prefixes. -/
noncomputable def runtimeSelectorArray
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    Fin (totalRequests * width) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := width)).symm flat
    decide (requestAndBit.2 =
      requestSelectedBit packingFits input requestAndBit.1)

theorem processedSuffixArray_requestDataArray
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    processedSuffixArray
        ((requestDataArrayCircuit totalRequests prefixWidth dimension
          suffixWidth widthPositive gridPositive).eval
            DeMorgan.interpretation input) =
      runtimeSuffixArray input := by
  funext flat
  obtain ⟨⟨request, bit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := totalRequests) (n := suffixWidth)).surjective flat
  rw [processedSuffixArray, runtimeSuffixArray]
  simp only [Equiv.symm_apply_apply]
  exact requestDataArrayCircuit_eval_suffix widthPositive gridPositive
    input request bit

theorem processedSelectorArray_requestDataArray
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    processedSelectorArray
        ((requestDataArrayCircuit totalRequests prefixWidth dimension
          suffixWidth widthPositive gridPositive).eval
            DeMorgan.interpretation input) =
      runtimeSelectorArray packingFits input := by
  funext flat
  obtain ⟨⟨request, bit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := totalRequests) (n := width)).surjective flat
  rw [processedSelectorArray, runtimeSelectorArray]
  simp only [Equiv.symm_apply_apply]
  exact requestDataArrayCircuit_eval_selector widthPositive gridPositive
    packingFits input request bit

/-- Runtime packing for every request, followed by deterministic grouped
scheduling and retention of every suffix and selector bit. -/
noncomputable def runtimeScheduleSuffixSelectorCircuit
    (totalRequests groups prefixWidth dimension width suffixWidth
      schedulerDepth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  let groupSize := requestGroupSize totalRequests groups
  (scheduleSuffixSelectorCircuit totalRequests groups groupSize dimension width
    suffixWidth schedulerDepth widthPositive allFit dummyTarget).comp
      (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
        widthPositive gridPositive)

theorem runtimeScheduleSuffixSelectorCircuit_eval
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    (runtimeScheduleSuffixSelectorCircuit totalRequests groups prefixWidth
      dimension width suffixWidth schedulerDepth widthPositive gridPositive
      allFit dummyTarget).eval DeMorgan.interpretation input =
      let groupSize := requestGroupSize totalRequests groups
      let capacity := requestGroupCapacity
        (totalRequests := totalRequests) groupsPositive
      let paddedTargets := paddedGroupedTargets capacity
        (requestTarget widthPositive packingFits input) dummyTarget
      Fin.append
        (groupedScheduleOutput dimension widthPositive schedulerDepth groups
          groupSize allFit paddedTargets)
        (Fin.append (runtimeSuffixArray input)
          (runtimeSelectorArray packingFits input)) := by
  rw [runtimeScheduleSuffixSelectorCircuit, Circuit.eval_comp]
  rw [scheduleSuffixSelectorCircuit_eval widthPositive allFit
    (requestGroupCapacity (totalRequests := totalRequests) groupsPositive)
    dummyTarget (requestTarget widthPositive packingFits input)
    _ (requestDataArrayCircuit_eval_target widthPositive gridPositive
      packingFits input)]
  rw [processedSuffixArray_requestDataArray,
    processedSelectorArray_requestDataArray]

@[simp] theorem runtimeScheduleSuffixSelectorCircuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (runtimeScheduleSuffixSelectorCircuit totalRequests groups prefixWidth
      dimension width suffixWidth schedulerDepth widthPositive gridPositive
      allFit dummyTarget).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost +
      totalRequests *
        (RuntimePacking.circuit prefixWidth dimension widthPositive
          gridPositive).cost DeMorgan.standardCost := by
  rw [runtimeScheduleSuffixSelectorCircuit, Circuit.cost_comp,
    scheduleSuffixSelectorCircuit_cost, requestDataArrayCircuit_cost]
  omega

/-- The complete exact mass-production circuit with runtime prefix and suffix
bits for every request. -/
def requestFunction
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool) :
    ScalarFunction Bool (requestInputCount prefixWidth suffixWidth) :=
  fun input =>
    function
      (RuntimePacking.source fun bit =>
        input (requestPrefixInputIndex prefixWidth suffixWidth bit))
      (fun bit =>
        input (requestSuffixInputIndex prefixWidth suffixWidth bit))

theorem directProduct_requestFunction_apply
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) :
    directProduct (requestFunction function) totalRequests input request =
      function (requestSource input request) (requestSuffix input request) :=
  rfl

/-- Complete runtime mass-production circuit: schedule, scatter, evaluate,
gather, and decode every requested output. -/
noncomputable def circuit
    (prefixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :=
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  (dynamicAssembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
    orderWidth incidenceFits capacity scatterRecordCount gateCounts
    resourceCircuits gatherRecordCount).comp
      (runtimeScheduleSuffixSelectorCircuit totalRequests groups prefixWidth
        dimension width suffixWidth schedulerDepth widthPositive gridPositive
        allFit dummyTarget)

set_option maxHeartbeats 2000000 in
/-- The complete runtime circuit returns every requested value in its original
request position.  In particular, the selected prefixes are runtime data,
not nonuniform parameters of the constructed circuit. -/
theorem circuit_recovers
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall
      (point : Fin (pointCount dimension width)) (bit : Fin width),
      (resourceCircuits (resourceMemberIndex point bit)).Computes
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction
            (Prefix := Fin (2 ^ prefixWidth))
            (dimension := dimension) (width := width)
            (suffixWidth := suffixWidth) widthPositive
            ((CanonicalPacking.packedPlacement widthPositive packingFits) :
              Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
            function point bit)
          groups))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).eval DeMorgan.interpretation input =
      fun request => function (requestSource input request)
        (requestSuffix input request) := by
  let groupSize := requestGroupSize totalRequests groups
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  let placement :=
    CanonicalPacking.packedPlacement widthPositive packingFits
  let sources : Fin totalRequests -> Fin (2 ^ prefixWidth) :=
    requestSource input
  let schedule := groupedScheduleOutput dimension widthPositive
    schedulerDepth groups groupSize allFit
      (paddedGroupedTargets capacity
        (requestTarget widthPositive packingFits input) dummyTarget)
  let suffixes := runtimeSuffixArray input
  let selectors := runtimeSelectorArray packingFits input
  have selectorCorrect : forall request bit,
      scheduledSelectorInput
          (Fin.append schedule (Fin.append suffixes selectors))
          (finProdFinEquiv (request, bit)) =
        decide (bit = (placement (sources request)).2) := by
    intro request bit
    rw [scheduledSelectorInput_append]
    simp [selectors, runtimeSelectorArray, placement, sources,
      requestSelectedBit, requestSource]
  rw [circuit, Circuit.eval_comp,
    runtimeScheduleSuffixSelectorCircuit_eval widthPositive gridPositive
      groupsPositive packingFits]
  dsimp only
  rw [dynamicAssembledPipelineCircuit_eq_fixed
    (placement := placement) (requestSource := sources)
    (selectorCorrect := selectorCorrect)]
  rw [scheduledScatterInput_append]
  have targetsEqual :
      requestTarget widthPositive packingFits input =
        fun request => packedTargetPoint widthPositive placement
          (sources request) := by
    rfl
  have scheduleEqual : schedule =
      groupedScheduleOutput dimension widthPositive schedulerDepth groups
        groupSize allFit
        (paddedGroupedTargets capacity
          (fun request => packedTargetPoint widthPositive placement
            (sources request)) dummyTarget) := by
    dsimp [schedule]
    rw [targetsEqual]
  rw [scheduleEqual]
  have fixedRecovery := finiteMassProductionCircuit_recovers
    (totalRequests := totalRequests) (width := width)
    (dimension := dimension) (groups := groups)
    (schedulerDepth := schedulerDepth) (suffixWidth := suffixWidth)
    (groupBitWidth := groupBitWidth) (orderWidth := orderWidth)
    (scatterDepth := scatterDepth)
    (scatterPaddingCount := scatterPaddingCount)
    (gatherDepth := gatherDepth)
    (gatherPaddingCount := gatherPaddingCount)
    widthPositive widthAtLeastTwo dimensionPositive groupsPositive
    groupFits allFit directionCapacity incidenceFits placement function
    sources dummyTarget scatterRecordCount gateCounts resourceCircuits
    computes gatherRecordCount suffixes
  rw [finiteMassProductionCircuit_eval] at fixedRecovery
  simpa [groupSize, capacity, placement, sources, schedule, suffixes,
    requestTarget, runtimeSuffixArray] using fixedRecovery

set_option maxHeartbeats 2000000 in
/-- Public direct-product form of `circuit_recovers`: the constructed circuit
computes the standard row-major `totalRequests`-fold direct product. -/
theorem circuit_computes
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall
      (point : Fin (pointCount dimension width)) (bit : Fin width),
      (resourceCircuits (resourceMemberIndex point bit)).Computes
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction
            (Prefix := Fin (2 ^ prefixWidth))
            (dimension := dimension) (width := width)
            (suffixWidth := suffixWidth) widthPositive
            ((CanonicalPacking.packedPlacement widthPositive packingFits) :
              Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
            function point bit)
          groups))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).Computes DeMorgan.interpretation
        (directProduct (requestFunction function) totalRequests) := by
  intro input
  rw [circuit_recovers widthPositive widthAtLeastTwo dimensionPositive
    gridPositive groupsPositive packingFits schedulerDepth suffixWidth
    groupBitWidth orderWidth groupFits allFit directionCapacity incidenceFits
    function dummyTarget scatterRecordCount gateCounts resourceCircuits
    computes gatherRecordCount input]
  funext request
  exact (directProduct_requestFunction_apply function input request).symm

@[simp] theorem circuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      ((groupedScheduleCircuit dimension widthPositive schedulerDepth groups
          (requestGroupSize totalRequests groups) allFit).cost
            DeMorgan.standardCost +
        totalRequests *
          (RuntimePacking.circuit prefixWidth dimension widthPositive
            gridPositive).cost DeMorgan.standardCost) +
      ((gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
          orderWidth incidenceFits
          (requestGroupCapacity (totalRequests := totalRequests)
            groupsPositive)
          scatterRecordCount gateCounts resourceCircuits
          gatherRecordCount).cost DeMorgan.standardCost +
        totalRequests * (nonzeroScalarCount width * width * 5)) := by
  rw [circuit, Circuit.cost_comp,
    runtimeScheduleSuffixSelectorCircuit_cost,
    dynamicAssembledPipelineCircuit_cost]

/-- Fully expanded finite ledger.  All zero-cost wiring has disappeared;
the only terms are packing, scheduling, the shorter resource circuits, two
routing passes, and runtime decoding. -/
theorem circuit_cost_expanded
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost +
      totalRequests *
        (RuntimePacking.circuit prefixWidth dimension widthPositive
          gridPositive).cost DeMorgan.standardCost +
      (CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
      (∑ member,
        (resourceCircuits member).cost DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost +
      totalRequests * (nonzeroScalarCount width * width * 5) := by
  rw [circuit_cost, gatherWithSelectorsCircuit_cost,
    scatterResourceGatherCircuit_cost]
  omega

end RuntimePipeline
end MassProduction
end Algebraic
