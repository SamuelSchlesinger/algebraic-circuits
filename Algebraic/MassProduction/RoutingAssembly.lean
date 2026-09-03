import Algebraic.MassProduction.GatherAssembly
import Algebraic.MassProduction.PackedPipeline
import Algebraic.MassProduction.ScatterAssembly

/-!
# Mass-production routing assembly

The scheduler emits every selected punctured-line point in packed row-major
form. Building on the focused scatter- and gather-assembly layers, this module
composes scatter, resource evaluation, gather, and decoding without
recomputing field operations.
-/

namespace Algebraic
namespace MassProduction
namespace RoutingAssembly

universe u

variable {Prefix : Type u}

open scoped LinearAlgebra.Projectivization
open GroupedScheduler
open CanonicalMetadataRouting
open CanonicalScatter
open GatherRouting
open IncidenceRouting
open LineEnumeration
open PackedPipeline
open ResourceEvaluation
open SchedulerIteration
open Sorting

/-! ## Sequential scatter and resource evaluation -/

/-- Preserve scheduler outputs alongside the routed scatter array. -/
noncomputable def scatterWithScheduleCircuit
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth) :=
  ((Circuit.id DeMorgan.signature
      (scheduleBitCount groups requestsPerGroup dimension width)).mapInputs
        (scatterScheduleInputIndex (totalRequests := totalRequests)
          (suffixWidth := suffixWidth))).parallel
    (scatterRoutingCircuit suffixWidth groupBitWidth capacity recordCount)

theorem scatterWithScheduleCircuit_eval
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    (scatterWithScheduleCircuit suffixWidth groupBitWidth capacity
      recordCount).eval DeMorgan.interpretation input =
      Fin.append (scatterScheduleInput input)
        (canonicalFullScatterBits widthPositive groupBitWidth capacity
          (scatterScheduleInput input) (scatterSuffixInput input)
          (fun _destination _bit => false)
          (fun _padding _bit => false) recordCount) := by
  rw [scatterWithScheduleCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_id,
    scatterRoutingCircuit_eval widthPositive]
  rfl

@[simp] theorem scatterWithScheduleCircuit_cost
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth) :
    (scatterWithScheduleCircuit suffixWidth groupBitWidth capacity
      recordCount).cost DeMorgan.standardCost =
      (CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost := by
  simp [scatterWithScheduleCircuit]

/-- Scheduler plus routed-scatter input consumed by resource evaluation. -/
@[reducible] noncomputable def resourceStageInputCount
    (groups requestsPerGroup dimension width scatterDepth groupBitWidth
      suffixWidth : Nat) : Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)

/-- Embed a scheduler bit into the combined resource-stage input. -/
noncomputable def resourceStageScheduleInputIndex
    (index : Fin (scheduleBitCount groups requestsPerGroup dimension width)) :
    Fin (resourceStageInputCount groups requestsPerGroup dimension width
      scatterDepth groupBitWidth suffixWidth) :=
  Fin.castAdd
    (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth))
    index

/-- Embed a routed-scatter bit into the combined resource-stage input. -/
noncomputable def resourceStageScatterInputIndex
    (index : Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth))) :
    Fin (resourceStageInputCount groups requestsPerGroup dimension width
      scatterDepth groupBitWidth suffixWidth) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width) index

/-- Project the scheduler portion of a combined resource-stage input. -/
noncomputable def resourceStageScheduleInput
    (input : Fin (resourceStageInputCount groups requestsPerGroup dimension
      width scatterDepth groupBitWidth suffixWidth) -> Bool) :
    Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool :=
  fun index => input (resourceStageScheduleInputIndex index)

/-- Project the routed-scatter portion of a combined resource-stage input. -/
noncomputable def resourceStageScatterInput
    (input : Fin (resourceStageInputCount groups requestsPerGroup dimension
      width scatterDepth groupBitWidth suffixWidth) -> Bool) :
    Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool :=
  fun index => input (resourceStageScatterInputIndex
    (groups := groups) (requestsPerGroup := requestsPerGroup) index)

@[simp] theorem resourceStageScheduleInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (scatter : Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool) :
    resourceStageScheduleInput (Fin.append schedule scatter) = schedule := by
  funext index
  simp [resourceStageScheduleInput, resourceStageScheduleInputIndex]

@[simp] theorem resourceStageScatterInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (scatter : Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool) :
    resourceStageScatterInput (Fin.append schedule scatter) = scatter := by
  funext index
  simp [resourceStageScatterInput, resourceStageScatterInputIndex]

/-- Preserve the schedule while evaluating every shorter resource circuit in
parallel on the routed scatter output. -/
noncomputable def resourceStageCircuit
    (requestsPerGroup : Nat)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups) :=
  ((Circuit.id DeMorgan.signature
      (scheduleBitCount groups requestsPerGroup dimension width)).mapInputs
        (resourceStageScheduleInputIndex
          (scatterDepth := scatterDepth) (groupBitWidth := groupBitWidth)
          (suffixWidth := suffixWidth))).parallel
    ((resourceBankCircuit destinationFits gateCounts resourceCircuits).mapInputs
      (resourceStageScatterInputIndex
        (groups := groups) (requestsPerGroup := requestsPerGroup)))

theorem resourceStageCircuit_eval
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (input : Fin (resourceStageInputCount groups requestsPerGroup dimension
      width scatterDepth groupBitWidth suffixWidth) -> Bool) :
    (resourceStageCircuit (requestsPerGroup := requestsPerGroup)
      destinationFits gateCounts resourceCircuits).eval
        DeMorgan.interpretation input =
      Fin.append (resourceStageScheduleInput input)
        ((resourceBankCircuit destinationFits gateCounts resourceCircuits).eval
          DeMorgan.interpretation (resourceStageScatterInput input)) := by
  rw [resourceStageCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_id, Circuit.eval_mapInputs]
  rfl

@[simp] theorem resourceStageCircuit_cost
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups) :
    (resourceStageCircuit (requestsPerGroup := requestsPerGroup)
      destinationFits gateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      ∑ member, (resourceCircuits member).cost DeMorgan.standardCost := by
  simp [resourceStageCircuit]

/-- Scatter, retain its schedule, and evaluate the complete resource bank. -/
noncomputable def scatterResourceCircuit
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups) :=
  (resourceStageCircuit (requestsPerGroup := requestsPerGroup)
    destinationFits gateCounts resourceCircuits).comp
      (scatterWithScheduleCircuit suffixWidth groupBitWidth capacity
        recordCount)

theorem scatterResourceCircuit_eval
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool) :
    (scatterResourceCircuit suffixWidth groupBitWidth capacity recordCount
      destinationFits gateCounts resourceCircuits).eval
        DeMorgan.interpretation input =
      Fin.append (scatterScheduleInput input)
        ((resourceBankCircuit destinationFits gateCounts resourceCircuits).eval
          DeMorgan.interpretation
          (canonicalFullScatterBits widthPositive groupBitWidth capacity
            (scatterScheduleInput input) (scatterSuffixInput input)
            (fun _destination _bit => false)
            (fun _padding _bit => false) recordCount)) := by
  rw [scatterResourceCircuit, Circuit.eval_comp,
    resourceStageCircuit_eval, scatterWithScheduleCircuit_eval widthPositive,
    resourceStageScheduleInput_append, resourceStageScatterInput_append]

@[simp] theorem scatterResourceCircuit_cost
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups) :
    (scatterResourceCircuit suffixWidth groupBitWidth capacity recordCount
      destinationFits gateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      (CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost := by
  rw [scatterResourceCircuit, Circuit.cost_comp,
    scatterWithScheduleCircuit_cost, resourceStageCircuit_cost]

/-! ## Complete assembled finite pipeline -/

/-- Scatter, resource evaluation, and gather as a single circuit. -/
noncomputable def scatterResourceGatherCircuit
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :=
  (gatherRoutingCircuit groupsPositive groupBitWidth orderWidth
    incidenceFits capacity gatherRecordCount).comp
      (scatterResourceCircuit suffixWidth groupBitWidth capacity
        scatterRecordCount scatterDestinationFits gateCounts resourceCircuits)

theorem scatterResourceGatherCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool) :
    (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      scatterDestinationFits gateCounts resourceCircuits
      gatherRecordCount).eval DeMorgan.interpretation input =
      let schedule := scatterScheduleInput input
      let scatterOutput := canonicalFullScatterBits widthPositive
        groupBitWidth capacity schedule (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) scatterRecordCount
      let bankOutput :=
        (resourceBankCircuit scatterDestinationFits gateCounts
          resourceCircuits).eval DeMorgan.interpretation scatterOutput
      canonicalGatherBits widthPositive groupBitWidth orderWidth incidenceFits
        capacity schedule
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          bankOutput)
        (fun _destination _bit => false)
        (fun _padding _bit => false) gatherRecordCount := by
  rw [scatterResourceGatherCircuit, Circuit.eval_comp,
    gatherRoutingCircuit_eval groupsPositive widthPositive,
    scatterResourceCircuit_eval widthPositive,
    gatherScheduleInput_append, gatherBankInput_append]

@[simp] theorem scatterResourceGatherCircuit_cost
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      scatterDestinationFits gateCounts resourceCircuits
      gatherRecordCount).cost DeMorgan.standardCost =
      ((CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost := by
  rw [scatterResourceGatherCircuit, Circuit.cost_comp,
    scatterResourceCircuit_cost, gatherRoutingCircuit_cost]

/-- The complete scatter-evaluate-gather-decode circuit on an already
computed schedule and its request suffixes.  Both sorter-capacity inclusions
are derived from the exact padding equations, so callers do not supply
redundant proof arguments. -/
noncomputable def assembledPipelineCircuit
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
        networkRecords gatherDepth) :=
  let scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth := by
    rw [← scatterRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  let gatherDestinationFits :
      totalRequests * nonzeroScalarCount width <=
        networkRecords gatherDepth := by
    rw [← gatherRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  (GatherDecoder.circuit
    (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
    (metadataWidth := orderWidth + 1)
    gatherDestinationFits
    (fun request => (placement (requestSource request)).2)).comp
      (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount
        scatterDestinationFits gateCounts resourceCircuits gatherRecordCount)

theorem assembledPipelineCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
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
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool) :
    (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity placement requestSource
      scatterRecordCount gateCounts resourceCircuits gatherRecordCount).eval
        DeMorgan.interpretation input =
      let scatterDestinationFits :
          2 ^ (groupBitWidth + dimension * width) <=
            networkRecords scatterDepth := by
        rw [← scatterRecordCount]
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      let gatherDestinationFits :
          totalRequests * nonzeroScalarCount width <=
            networkRecords gatherDepth := by
        rw [← gatherRecordCount]
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      let schedule := scatterScheduleInput input
      let scatterOutput := canonicalFullScatterBits widthPositive
        groupBitWidth capacity schedule (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) scatterRecordCount
      let bankOutput :=
        (resourceBankCircuit scatterDestinationFits gateCounts
          resourceCircuits).eval DeMorgan.interpretation scatterOutput
      let gatherOutput := canonicalGatherBits widthPositive groupBitWidth
        orderWidth incidenceFits capacity schedule
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          bankOutput)
        (fun _destination _bit => false)
        (fun _padding _bit => false) gatherRecordCount
      (GatherDecoder.circuit
        (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
        (metadataWidth := orderWidth + 1)
        gatherDestinationFits
        (fun request => (placement (requestSource request)).2)).eval
          DeMorgan.interpretation gatherOutput := by
  rw [assembledPipelineCircuit, Circuit.eval_comp,
    scatterResourceGatherCircuit_eval groupsPositive widthPositive]

set_option maxHeartbeats 1500000 in
/-- End-to-end correctness of the single assembled finite circuit.  Given
the geometric scheduler invariants and correct shorter-resource circuits, it
returns every requested Boolean value in its original request position. -/
theorem assembledPipelineCircuit_recovers
    (widthPositive : 0 < width)
    (dimensionPositive : 0 < dimension)
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool)
    (directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : forall request scalar,
      requestScheduledLinePoint widthPositive capacity
          (scatterScheduleInput input) request scalar =
        packedTargetPoint widthPositive placement (requestSource request) +
          enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector (directions request).rep)
    (setFormula : forall request,
      requestScheduledLineSet widthPositive capacity
          (scatterScheduleInput input) request =
        ForbiddenRanks.binaryExtensionPuncturedLine
          (packedTargetPoint widthPositive placement (requestSource request))
          (directions request))
    (withinGroupDisjoint : forall left right,
      (requestGroupSlot capacity left).1 =
          (requestGroupSlot capacity right).1 ->
      left ≠ right ->
        Disjoint
          (requestScheduledLineSet widthPositive capacity
            (scatterScheduleInput input) left)
          (requestScheduledLineSet widthPositive capacity
            (scatterScheduleInput input) right))
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).Computes
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction widthPositive placement function point bit)
          groups))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity placement requestSource
      scatterRecordCount gateCounts resourceCircuits gatherRecordCount).eval
        DeMorgan.interpretation input =
      fun request => function (requestSource request)
        (scatterSuffixInput input request) := by
  rw [assembledPipelineCircuit_eval groupsPositive widthPositive]
  let schedule := scatterScheduleInput input
  let requestSuffix := scatterSuffixInput input
  have recovered := scatter_evaluate_gather_decode_recovers widthPositive
    dimensionPositive groupsPositive groupFits incidenceFits capacity schedule
    placement function requestSource requestSuffix directions pointFormula
    setFormula withinGroupDisjoint
    (fun _destination _bit => false)
    (fun _padding _bit => false) scatterRecordCount gateCounts
    resourceCircuits computes
    (fun _destination _bit => false)
    (fun _padding _bit => false) gatherRecordCount
  simpa only [evaluatedResourceValues] using recovered

/-- Exact cost ledger for the assembled finite circuit.  Record assembly,
schedule preservation, and all fixed reindexings contribute zero gates. -/
@[simp] theorem assembledPipelineCircuit_cost
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
        networkRecords gatherDepth) :
    (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity placement requestSource
      scatterRecordCount gateCounts resourceCircuits gatherRecordCount).cost
        DeMorgan.standardCost =
      (((CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost) +
      totalRequests * (nonzeroScalarCount width * 4) := by
  unfold assembledPipelineCircuit
  rw [Circuit.cost_comp, scatterResourceGatherCircuit_cost,
    GatherDecoder.circuit_cost]

/-! ## Hardwired grouped scheduling -/

/-- Assemble a fixed rectangular target family for the grouped scheduler.
The suffix inputs are deliberately ignored by this zero-cost layer. -/
noncomputable def fixedGroupedTargetAssemblyCircuit
    (totalRequests : Nat)
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :=
  DeMorgan.Wiring.circuit (inputs := totalRequests * suffixWidth) fun output =>
    .constant (groupedTargetArrayBits widthPositive targets output)

@[simp] theorem fixedGroupedTargetAssemblyCircuit_cost
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive targets).cost DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

theorem fixedGroupedTargetAssemblyCircuit_eval
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive targets).eval DeMorgan.interpretation input =
      groupedTargetArrayBits widthPositive targets := by
  rw [fixedGroupedTargetAssemblyCircuit, DeMorgan.Wiring.circuit_eval]
  rfl

/-- Run the grouped greedy scheduler on hardwired packed target points while
passing every runtime suffix bit through unchanged. -/
noncomputable def fixedScheduleAndSuffixCircuit
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  let groupSize := requestGroupSize totalRequests groups
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  let targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width :=
    fun request => packedTargetPoint widthPositive placement
      (requestSource request)
  let paddedTargets : Fin groups -> Fin groupSize ->
      Fin dimension -> BinaryExtension width :=
    paddedGroupedTargets capacity targets dummyTarget
  ((groupedScheduleCircuit dimension widthPositive schedulerDepth groups
      groupSize allFit).comp
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive paddedTargets)).parallel
    (Circuit.id DeMorgan.signature (totalRequests * suffixWidth))

theorem fixedScheduleAndSuffixCircuit_eval
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (fixedScheduleAndSuffixCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth allFit placement requestSource dummyTarget).eval
        DeMorgan.interpretation input =
      let groupSize := requestGroupSize totalRequests groups
      let capacity := requestGroupCapacity
        (totalRequests := totalRequests) groupsPositive
      let targets : Fin totalRequests ->
          Fin dimension -> BinaryExtension width :=
        fun request => packedTargetPoint widthPositive placement
          (requestSource request)
      let paddedTargets : Fin groups -> Fin groupSize ->
          Fin dimension -> BinaryExtension width :=
        paddedGroupedTargets capacity targets dummyTarget
      Fin.append
        (groupedScheduleOutput dimension widthPositive schedulerDepth groups
          groupSize allFit paddedTargets)
        input := by
  unfold fixedScheduleAndSuffixCircuit
  rw [Circuit.eval_parallel, Circuit.eval_comp,
    fixedGroupedTargetAssemblyCircuit_eval, Circuit.eval_id]
  rfl

@[simp] theorem fixedScheduleAndSuffixCircuit_cost
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (fixedScheduleAndSuffixCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth allFit placement requestSource dummyTarget).cost
        DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost := by
  simp [fixedScheduleAndSuffixCircuit]

/-- The complete finite mass-production circuit.  Its only runtime inputs
are the row-major suffixes; selected function prefixes, packed target points,
and the dummy padding target are nonuniform construction data. -/
noncomputable def finiteMassProductionCircuit
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
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
  (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
    orderWidth incidenceFits capacity placement requestSource
    scatterRecordCount gateCounts resourceCircuits gatherRecordCount).comp
      (fixedScheduleAndSuffixCircuit widthPositive groupsPositive
        schedulerDepth suffixWidth allFit placement requestSource dummyTarget)

theorem finiteMassProductionCircuit_eval
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
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
        networkRecords gatherDepth)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (finiteMassProductionCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth groupBitWidth orderWidth allFit incidenceFits placement
      requestSource dummyTarget scatterRecordCount gateCounts resourceCircuits
      gatherRecordCount).eval DeMorgan.interpretation input =
      let groupSize := requestGroupSize totalRequests groups
      let capacity := requestGroupCapacity
        (totalRequests := totalRequests) groupsPositive
      let targets : Fin totalRequests ->
          Fin dimension -> BinaryExtension width :=
        fun request => packedTargetPoint widthPositive placement
          (requestSource request)
      let paddedTargets : Fin groups -> Fin groupSize ->
          Fin dimension -> BinaryExtension width :=
        paddedGroupedTargets capacity targets dummyTarget
      let schedule := groupedScheduleOutput dimension widthPositive
        schedulerDepth groups groupSize allFit paddedTargets
      (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity placement requestSource
        scatterRecordCount gateCounts resourceCircuits gatherRecordCount).eval
          DeMorgan.interpretation (Fin.append schedule input) := by
  rw [finiteMassProductionCircuit, Circuit.eval_comp,
    fixedScheduleAndSuffixCircuit_eval]

set_option maxHeartbeats 1800000 in
/-- The fully assembled circuit, including the verified deterministic grouped
scheduler, computes the requested functions on all row-major suffix inputs. -/
theorem finiteMassProductionCircuit_recovers
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (groupsPositive : 0 < groups)
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
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).Computes
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction widthPositive placement function point bit)
          groups))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (finiteMassProductionCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth groupBitWidth orderWidth allFit incidenceFits placement
      requestSource dummyTarget scatterRecordCount gateCounts resourceCircuits
      gatherRecordCount).eval DeMorgan.interpretation input =
      fun request => function (requestSource request)
        (fun bit => input (finProdFinEquiv (request, bit))) := by
  rw [finiteMassProductionCircuit_eval,
    assembledPipelineCircuit_eval groupsPositive widthPositive,
    scatterScheduleInput_append, scatterSuffixInput_append]
  let requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool :=
    fun request bit => input (finProdFinEquiv (request, bit))
  have recovered := grouped_scatter_evaluate_gather_decode_recovers
    (width := width) (dimension := dimension) (groups := groups)
    (totalRequests := totalRequests) (groupBitWidth := groupBitWidth)
    (orderWidth := orderWidth) (schedulerDepth := schedulerDepth)
    (suffixWidth := suffixWidth) (scatterDepth := scatterDepth)
    (scatterPaddingCount := scatterPaddingCount)
    (gatherDepth := gatherDepth) (gatherPaddingCount := gatherPaddingCount)
    widthPositive widthAtLeastTwo dimensionPositive groupsPositive groupFits
    incidenceFits allFit directionCapacity placement function requestSource
    requestSuffix dummyTarget
    (fun _destination _bit => false)
    (fun _padding _bit => false) scatterRecordCount gateCounts
    resourceCircuits computes
    (fun _destination _bit => false)
    (fun _padding _bit => false) gatherRecordCount
  simpa only [evaluatedResourceValues] using recovered

/-- Exact top-level finite cost ledger: scheduler, scatter routing, shorter
resource bank, gather routing, and decoder. -/
@[simp] theorem finiteMassProductionCircuit_cost
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
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
    (finiteMassProductionCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth groupBitWidth orderWidth allFit incidenceFits placement
      requestSource dummyTarget scatterRecordCount gateCounts resourceCircuits
      gatherRecordCount).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost +
      ((((CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost) +
      totalRequests * (nonzeroScalarCount width * 4)) := by
  unfold finiteMassProductionCircuit
  rw [Circuit.cost_comp, fixedScheduleAndSuffixCircuit_cost,
    assembledPipelineCircuit_cost]

end RoutingAssembly
end MassProduction
end Algebraic
