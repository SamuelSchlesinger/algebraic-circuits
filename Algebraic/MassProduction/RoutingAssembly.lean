import Algebraic.MassProduction.PackedPipeline

/-!
# Zero-cost record assembly wiring

The scheduler already emits every selected punctured-line point in packed
row-major form.  This module exposes the exact wire index, avoiding a second
field computation when scatter and gather records are assembled.
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

/-! ## Generic zero-cost wiring circuits -/

/-- One output bit of a pure wiring layer is either an original input wire or
a hardwired Boolean constant. -/
inductive WiringBit (inputs : Nat)
  | input (index : Fin inputs)
  | constant (value : Bool)

namespace WiringBit

/-- Interpret a wiring source against a concrete input assignment. -/
def eval (input : Fin inputs -> Bool) : WiringBit inputs -> Bool
  | .input index => input index
  | .constant value => value

@[simp] theorem eval_input
    (input : Fin inputs -> Bool)
    (index : Fin inputs) :
    eval input (.input index) = input index := rfl

@[simp] theorem eval_constant
    (input : Fin inputs -> Bool)
    (value : Bool) :
    eval input (.constant value) = value := rfl

/-- Compile a wiring source to its zero-cost De Morgan expression. -/
def expression : WiringBit inputs -> DeMorgan.Expression inputs
  | .input index => .input index
  | .constant value => .constant value

@[simp] theorem expression_eval
    (source : WiringBit inputs)
    (input : Fin inputs -> Bool) :
    source.expression.eval input = source.eval input := by
  cases source <;> rfl

@[simp] theorem expression_standardCost
    (source : WiringBit inputs) :
    source.expression.standardCost = 0 := by
  cases source <;> rfl

theorem eval_finAppend
    (left : Fin leftCount -> WiringBit inputs)
    (right : Fin rightCount -> WiringBit inputs)
    (input : Fin inputs -> Bool)
    (index : Fin (leftCount + rightCount)) :
    (Fin.append left right index).eval input =
      Fin.append (fun leftIndex => (left leftIndex).eval input)
        (fun rightIndex => (right rightIndex).eval input) index := by
  refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

theorem eval_finAppend_apply
    (left : Fin leftCount -> Fin width -> WiringBit inputs)
    (right : Fin rightCount -> Fin width -> WiringBit inputs)
    (input : Fin inputs -> Bool)
    (index : Fin (leftCount + rightCount))
    (bit : Fin width) :
    (Fin.append left right index bit).eval input =
      Fin.append
        (fun leftIndex bit => (left leftIndex bit).eval input)
        (fun rightIndex bit => (right rightIndex bit).eval input)
        index bit := by
  refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

end WiringBit

/-- Compile an arbitrary vector of input selections and constants. -/
def wiringCircuit
    (specification : Fin outputs -> WiringBit inputs) :
    Circuit DeMorgan.signature inputs
      (∑ output, (specification output).expression.gateCount) outputs :=
  Circuit.parallelFin outputs
    (fun output => (specification output).expression.gateCount)
    (fun output => (specification output).expression.circuit)

@[simp] theorem wiringCircuit_eval
    (specification : Fin outputs -> WiringBit inputs)
    (input : Fin inputs -> Bool) :
    (wiringCircuit specification).eval DeMorgan.interpretation input =
      fun output => (specification output).eval input := by
  funext output
  rw [wiringCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval, WiringBit.expression_eval]

@[simp] theorem wiringCircuit_cost
    (specification : Fin outputs -> WiringBit inputs) :
    (wiringCircuit specification).cost DeMorgan.standardCost = 0 := by
  rw [wiringCircuit, Circuit.cost_parallelFin]
  simp [DeMorgan.Expression.circuit_cost]

/-- Record packing lifted from Booleans to wiring-bit descriptions. -/
def wiringPackRecord
    (key : Fin keyWidth -> WiringBit inputs)
    (tag : WiringBit inputs)
    (payload : Fin payloadWidth -> WiringBit inputs) :
    Fin (Routing.recordWidth keyWidth payloadWidth) -> WiringBit inputs :=
  Fin.append (Fin.append key (fun _ : Fin 1 => tag)) payload

theorem wiringPackRecord_eval
    (key : Fin keyWidth -> WiringBit inputs)
    (tag : WiringBit inputs)
    (payload : Fin payloadWidth -> WiringBit inputs)
    (input : Fin inputs -> Bool) :
    (fun bit => (wiringPackRecord key tag payload bit).eval input) =
      Routing.packRecord
        (fun bit => (key bit).eval input)
        (tag.eval input)
        (fun bit => (payload bit).eval input) := by
  funext bit
  unfold wiringPackRecord Routing.packRecord
  refine Fin.addCases (motive := fun bit =>
      (Fin.append (Fin.append key (fun _ : Fin 1 => tag)) payload bit).eval
          input =
        Fin.append
          (Fin.append (fun bit => (key bit).eval input)
            (fun _ : Fin 1 => tag.eval input))
          (fun bit => (payload bit).eval input) bit)
    (fun headerBit => ?_) (fun payloadBit => ?_) bit
  · rw [Fin.append_left, Fin.append_left]
    refine Fin.addCases (fun keyBit => ?_) (fun tagBit => ?_) headerBit
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
  · rw [Fin.append_right, Fin.append_right]

theorem wiringPackRecord_eval_apply
    (key : Fin keyWidth -> WiringBit inputs)
    (tag : WiringBit inputs)
    (payload : Fin payloadWidth -> WiringBit inputs)
    (input : Fin inputs -> Bool)
    (bit : Fin (Routing.recordWidth keyWidth payloadWidth)) :
    (wiringPackRecord key tag payload bit).eval input =
      Routing.packRecord
        (fun keyBit => (key keyBit).eval input)
        (tag.eval input)
        (fun payloadBit => (payload payloadBit).eval input) bit := by
  exact congrFun (wiringPackRecord_eval key tag payload input) bit

/-- Routing records whose fields are all wiring-bit descriptions. -/
def wiringRoutingRecordSequence
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> WiringBit inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> WiringBit inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> WiringBit inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> WiringBit inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> WiringBit inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> WiringBit inputs) :
    Fin (sourceCount + destinationCount + paddingCount) ->
      Fin (Routing.recordWidth keyWidth payloadWidth) -> WiringBit inputs :=
  Fin.append
    (Fin.append
      (fun source => wiringPackRecord (sourceKeys source) (.constant false)
        (sourcePayloads source))
      (fun destination => wiringPackRecord (destinationKeys destination)
        (.constant true) (destinationPayloads destination)))
    (fun padding => wiringPackRecord (paddingKeys padding) (.constant true)
      (paddingPayloads padding))

theorem wiringRoutingRecordSequence_eval
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> WiringBit inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> WiringBit inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> WiringBit inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> WiringBit inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> WiringBit inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> WiringBit inputs)
    (input : Fin inputs -> Bool) :
    (fun record bit => (wiringRoutingRecordSequence sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      record bit).eval input) =
      Routing.routingRecordSequence
        (fun source bit => (sourceKeys source bit).eval input)
        (fun source bit => (sourcePayloads source bit).eval input)
        (fun destination bit =>
          (destinationKeys destination bit).eval input)
        (fun destination bit =>
          (destinationPayloads destination bit).eval input)
        (fun padding bit => (paddingKeys padding bit).eval input)
        (fun padding bit => (paddingPayloads padding bit).eval input) := by
  funext record bit
  unfold wiringRoutingRecordSequence Routing.routingRecordSequence
  rw [WiringBit.eval_finAppend_apply]
  refine Fin.addCases (motive := fun record =>
      Fin.append
          (fun leftIndex bit =>
            (Fin.append
              (fun source => wiringPackRecord (sourceKeys source)
                (.constant false) (sourcePayloads source))
              (fun destination => wiringPackRecord
                (destinationKeys destination) (.constant true)
                (destinationPayloads destination)) leftIndex bit).eval input)
          (fun padding bit =>
            (wiringPackRecord (paddingKeys padding) (.constant true)
              (paddingPayloads padding) bit).eval input)
          record bit =
        Fin.append
          (Fin.append
            (fun source => Routing.packRecord
              (fun bit => (sourceKeys source bit).eval input) false
              (fun bit => (sourcePayloads source bit).eval input))
            (fun destination => Routing.packRecord
              (fun bit => (destinationKeys destination bit).eval input) true
              (fun bit => (destinationPayloads destination bit).eval input)))
          (fun padding => Routing.packRecord
            (fun bit => (paddingKeys padding bit).eval input) true
            (fun bit => (paddingPayloads padding bit).eval input))
          record bit)
    (fun sourceOrDestination => ?_) (fun padding => ?_) record
  · rw [Fin.append_left, Fin.append_left,
      WiringBit.eval_finAppend_apply]
    refine Fin.addCases (fun source => ?_) (fun destination => ?_)
      sourceOrDestination
    · rw [Fin.append_left, Fin.append_left]
      exact wiringPackRecord_eval_apply _ _ _ input bit
    · rw [Fin.append_right, Fin.append_right]
      exact wiringPackRecord_eval_apply _ _ _ input bit
  · rw [Fin.append_right, Fin.append_right]
    exact wiringPackRecord_eval_apply _ _ _ input bit

/-- Exact-capacity routing records whose fields are all wiring-bit
descriptions, flattened in the sorter's row-major format. -/
def wiringRoutingInputBits
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> WiringBit inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> WiringBit inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> WiringBit inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> WiringBit inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> WiringBit inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> WiringBit inputs)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth) :
    Fin (networkBits depth (Routing.recordWidth keyWidth payloadWidth)) ->
      WiringBit inputs :=
  fun flat =>
    let recordAndBit :=
      (finProdFinEquiv
        (m := networkRecords depth)
        (n := Routing.recordWidth keyWidth payloadWidth)).symm flat
    wiringRoutingRecordSequence sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads
      (Fin.cast recordCount.symm recordAndBit.1) recordAndBit.2

/-- Evaluating a wiring-level routing layout gives the corresponding
Boolean routing layout exactly. -/
theorem wiringRoutingInputBits_eval
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> WiringBit inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> WiringBit inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> WiringBit inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> WiringBit inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> WiringBit inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> WiringBit inputs)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (input : Fin inputs -> Bool) :
    (fun bit => (wiringRoutingInputBits sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      recordCount bit).eval input) =
      Routing.routingInputBits
        (fun source bit => (sourceKeys source bit).eval input)
        (fun source bit => (sourcePayloads source bit).eval input)
        (fun destination bit =>
          (destinationKeys destination bit).eval input)
        (fun destination bit =>
          (destinationPayloads destination bit).eval input)
        (fun padding bit => (paddingKeys padding bit).eval input)
        (fun padding bit => (paddingPayloads padding bit).eval input)
        recordCount := by
  funext flat
  unfold wiringRoutingInputBits Routing.routingInputBits
    Routing.recordArrayBits Routing.networkRoutingRecords
  exact congrFun (congrFun
    (wiringRoutingRecordSequence_eval sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads input)
    (Fin.cast recordCount.symm (finProdFinEquiv.symm flat).1))
    (finProdFinEquiv.symm flat).2

/-- Scheduler-output wire containing one affine-point bit of a flattened
scheduled incidence. -/
noncomputable def scheduledIncidencePointBitIndex
    (capacity : totalRequests <= groups * requestsPerGroup)
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (pointBit : Fin (dimension * width)) :
    Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) :=
  let requestAndScalar := incidenceAt incidence
  let groupAndRequest := requestGroupSlot capacity requestAndScalar.1
  finProdFinEquiv
    (groupAndRequest.1,
      finProdFinEquiv
        (groupAndRequest.2,
          finProdFinEquiv (requestAndScalar.2, pointBit)))

/-- Decoding and re-encoding a scheduled point is exactly the corresponding
scheduler-output block. -/
theorem scheduledIncidencePointBit
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (pointBit : Fin (dimension * width)) :
    binaryExtensionVectorBits widthPositive
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          incidence).2 pointBit =
      scheduleOutput
        (scheduledIncidencePointBitIndex capacity incidence pointBit) := by
  unfold scheduledIncidenceSlotAt scheduledIncidenceSlot
  unfold requestScheduledLinePoint scheduledLinePoint
  rw [binaryExtensionVectorBits_vectorCoordinate]
  rfl

/-- Scheduled matching keys are a constant active marker and group prefix
followed by scheduler-output point wires. -/
theorem scheduledIncidenceKeyBits_eq_wiring
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        scheduleOutput incidence =
      activeRoutingKey (Fin.append
        (finiteIndexBits groupBitWidth
          (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
            incidence).1)
        (fun pointBit => scheduleOutput
          (scheduledIncidencePointBitIndex capacity incidence pointBit))) := by
  unfold scheduledIncidenceKeyBits
  apply congrArg activeRoutingKey
  unfold resourceSlotKeyBits
  funext baseBit
  refine Fin.addCases (fun groupBit => ?_) (fun pointBit => ?_) baseBit
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]
    exact scheduledIncidencePointBit widthPositive capacity scheduleOutput
      incidence pointBit

/-! ## Scatter-record assembly -/

/-- Scheduler-output wires consumed by scatter assembly. -/
@[reducible] noncomputable def scheduleBitCount
    (groups requestsPerGroup dimension width : Nat) : Nat :=
  groups * (requestsPerGroup * lineBitWidth dimension width)

/-- Scheduler output followed by one suffix for every actual request. -/
@[reducible] noncomputable def scatterAssemblyInputCount
    (groups requestsPerGroup dimension width totalRequests suffixWidth : Nat) :
    Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    totalRequests * suffixWidth

/-- Embed a scheduler-output wire into the scatter-assembly input. -/
noncomputable def scatterScheduleInputIndex
    (index : Fin (scheduleBitCount groups requestsPerGroup dimension width)) :
    Fin (scatterAssemblyInputCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.castAdd (totalRequests * suffixWidth) index

/-- Embed a row-major request-suffix wire into the scatter-assembly input. -/
noncomputable def scatterSuffixInputIndex
    (request : Fin totalRequests)
    (bit : Fin suffixWidth) :
    Fin (scatterAssemblyInputCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width)
    (finProdFinEquiv (request, bit))

/-- Scheduler-output view of the combined scatter-assembly input. -/
noncomputable def scatterScheduleInput
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool :=
  fun index => input (scatterScheduleInputIndex
    (totalRequests := totalRequests) (suffixWidth := suffixWidth) index)

/-- Request-suffix view of the combined scatter-assembly input. -/
noncomputable def scatterSuffixInput
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    Fin totalRequests -> Fin suffixWidth -> Bool :=
  fun request bit => input (scatterSuffixInputIndex
    (groups := groups) (requestsPerGroup := requestsPerGroup)
    (dimension := dimension) (width := width) request bit)

@[simp] theorem scatterScheduleInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool) :
    scatterScheduleInput (Fin.append schedule suffixes) = schedule := by
  funext index
  simp [scatterScheduleInput, scatterScheduleInputIndex]

@[simp] theorem scatterSuffixInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool) :
    scatterSuffixInput (Fin.append schedule suffixes) =
      fun request bit => suffixes (finProdFinEquiv (request, bit)) := by
  funext request bit
  simp [scatterSuffixInput, scatterSuffixInputIndex]

/-- A scheduled incidence key consists only of constants and direct scheduler
output wires. -/
noncomputable def scatterSourceKeyWiring
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) ->
      WiringBit (scatterAssemblyInputCount groups requestsPerGroup dimension
        width totalRequests suffixWidth) :=
  let requestAndScalar := incidenceAt incidence
  let group := (requestGroupSlot capacity requestAndScalar.1).1
  Fin.cons (.constant false)
    (Fin.append
      (fun groupBit => .constant (finiteIndexBits groupBitWidth group groupBit))
      (fun pointBit => .input (scatterScheduleInputIndex
        (totalRequests := totalRequests) (suffixWidth := suffixWidth)
        (scheduledIncidencePointBitIndex capacity incidence pointBit))))

theorem scatterSourceKeyWiring_eval
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    (fun bit => (scatterSourceKeyWiring
      (suffixWidth := suffixWidth) groupBitWidth capacity incidence bit).eval
        input) =
      scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        (scatterScheduleInput input) incidence := by
  rw [scheduledIncidenceKeyBits_eq_wiring]
  funext bit
  refine Fin.cases ?_ (fun tailBit => ?_) bit
  · simp [scatterSourceKeyWiring, activeRoutingKey]
  · refine Fin.addCases (fun groupBit => ?_) (fun pointBit => ?_) tailBit
    · simp [scatterSourceKeyWiring, activeRoutingKey,
        scheduledIncidenceSlotAt, scheduledIncidenceSlot]
    · simp [scatterSourceKeyWiring, activeRoutingKey,
        scatterScheduleInput, scatterScheduleInputIndex]

/-- One source payload is a direct copy of its request's suffix wires. -/
noncomputable def scatterSourcePayloadWiring
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin suffixWidth ->
      WiringBit (scatterAssemblyInputCount groups requestsPerGroup dimension
        width totalRequests suffixWidth) :=
  fun bit => .input (scatterSuffixInputIndex
    (groups := groups) (requestsPerGroup := requestsPerGroup)
    (dimension := dimension) (width := width)
    (incidenceAt incidence).1 bit)

theorem scatterSourcePayloadWiring_eval
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    (fun bit => (scatterSourcePayloadWiring
      (groups := groups) (requestsPerGroup := requestsPerGroup)
      (dimension := dimension) (width := width) incidence bit).eval input) =
      incidenceSourcePayload (scatterSuffixInput input) incidence := by
  rfl

/-- Zero-gate wiring description of the complete scatter sorter input.
Destination and padding payloads are initialized to zero because their prior
contents are semantically irrelevant. -/
noncomputable def scatterAssemblySpecification
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :
    Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      WiringBit (scatterAssemblyInputCount groups requestsPerGroup dimension
        width totalRequests suffixWidth) :=
  wiringRoutingInputBits
    (scatterSourceKeyWiring (suffixWidth := suffixWidth)
      groupBitWidth capacity)
    (scatterSourcePayloadWiring (groups := groups)
      (requestsPerGroup := requestsPerGroup) (dimension := dimension)
      (width := width))
    (fun destination bit => .constant
      (fullResourceDestinationKeyBits groupBitWidth dimension width
        destination bit))
    (fun _destination _bit => .constant false)
    (fun _padding bit => .constant
      (incidencePaddingKey groupBitWidth dimension width bit))
    (fun _padding _bit => .constant false)
    recordCount

/-- Scatter record assembly itself uses no Boolean gates. -/
noncomputable def scatterAssemblyCircuit
    (suffixWidth : Nat)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :=
  wiringCircuit (scatterAssemblySpecification
    (suffixWidth := suffixWidth) groupBitWidth capacity recordCount)

@[simp] theorem scatterAssemblyCircuit_cost
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :
    (scatterAssemblyCircuit (suffixWidth := suffixWidth) groupBitWidth
      capacity recordCount).cost DeMorgan.standardCost = 0 := by
  exact wiringCircuit_cost _

theorem scatterAssemblyCircuit_eval
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    (scatterAssemblyCircuit (suffixWidth := suffixWidth) groupBitWidth
      capacity recordCount).eval DeMorgan.interpretation input =
      fullScatterRoutingInputBits widthPositive groupBitWidth capacity
        (scatterScheduleInput input) (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) recordCount := by
  rw [scatterAssemblyCircuit, wiringCircuit_eval,
    scatterAssemblySpecification, wiringRoutingInputBits_eval]
  unfold fullScatterRoutingInputBits
  congr 1
  · funext incidence
    exact scatterSourceKeyWiring_eval widthPositive groupBitWidth capacity
      input incidence

/-- Complete scatter routing, including its zero-cost record assembly. -/
noncomputable def scatterRoutingCircuit
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :=
  (CanonicalRouting.matchedCanonicalRoutingCircuit routingDepth
    (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).comp
      (scatterAssemblyCircuit suffixWidth groupBitWidth capacity recordCount)

@[simp] theorem scatterRoutingCircuit_cost
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :
    (scatterRoutingCircuit suffixWidth groupBitWidth capacity recordCount).cost
        DeMorgan.standardCost =
      (CanonicalRouting.matchedCanonicalRoutingCircuit routingDepth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost := by
  rw [scatterRoutingCircuit, Circuit.cost_comp,
    scatterAssemblyCircuit_cost, Nat.zero_add]

theorem scatterRoutingCircuit_eval
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    (scatterRoutingCircuit suffixWidth groupBitWidth capacity recordCount).eval
        DeMorgan.interpretation input =
      canonicalFullScatterBits widthPositive groupBitWidth capacity
        (scatterScheduleInput input) (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) recordCount := by
  rw [scatterRoutingCircuit, Circuit.eval_comp,
    CanonicalRouting.matchedCanonicalRoutingCircuit_eval,
    scatterAssemblyCircuit_eval widthPositive]
  rfl

/-! ## Gather-record assembly -/

/-- Scheduler output followed by the complete resource-bank output. -/
@[reducible] noncomputable def gatherAssemblyInputCount
    (groups requestsPerGroup dimension width : Nat) : Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    resourceBitCount dimension width * groups

/-- Embed one scheduler bit in the gather-assembly input. -/
noncomputable def gatherScheduleInputIndex
    (index : Fin (scheduleBitCount groups requestsPerGroup dimension width)) :
    Fin (gatherAssemblyInputCount groups requestsPerGroup dimension width) :=
  Fin.castAdd (resourceBitCount dimension width * groups) index

/-- Embed one resource-bank output bit in the gather-assembly input. -/
noncomputable def gatherBankInputIndex
    (index : Fin (resourceBitCount dimension width * groups)) :
    Fin (gatherAssemblyInputCount groups requestsPerGroup dimension width) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width) index

/-- Scheduler view of a gather-assembly input. -/
noncomputable def gatherScheduleInput
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool :=
  fun index => input (gatherScheduleInputIndex index)

/-- Resource-bank view of a gather-assembly input. -/
noncomputable def gatherBankInput
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    Fin (resourceBitCount dimension width * groups) -> Bool :=
  fun index => input (gatherBankInputIndex
    (requestsPerGroup := requestsPerGroup) index)

@[simp] theorem gatherScheduleInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (bank : Fin (resourceBitCount dimension width * groups) -> Bool) :
    gatherScheduleInput (Fin.append schedule bank) = schedule := by
  funext index
  simp [gatherScheduleInput, gatherScheduleInputIndex]

@[simp] theorem gatherBankInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (bank : Fin (resourceBitCount dimension width * groups) -> Bool) :
    gatherBankInput (Fin.append schedule bank) = bank := by
  funext index
  simp [gatherBankInput, gatherBankInputIndex]

/-- Every full resource-source key is a construction-time constant. -/
noncomputable def gatherSourceKeyWiring
    (groupBitWidth dimension width : Nat)
    (source : Fin (2 ^ (groupBitWidth + dimension * width))) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) ->
      WiringBit inputs :=
  fun bit => .constant
    (fullResourceDestinationKeyBits groupBitWidth dimension width source bit)

/-- The resource value attached to a full-key source is selected directly
from the corresponding resource-bank output.  Invalid group encodings use
the same fixed group-zero convention as `resourceValuesFromBank`. -/
noncomputable def gatherSourcePayloadWiring
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (source : Fin (2 ^ (groupBitWidth + dimension * width))) :
    Fin ((orderWidth + 1) + width) ->
      WiringBit (gatherAssemblyInputCount groups requestsPerGroup dimension
        width) :=
  Fin.append
    (fun _metadataBit => .constant false)
    (fun valueBit => .input (gatherBankInputIndex
      (requestsPerGroup := requestsPerGroup)
      (finProdFinEquiv
        (resourceMemberIndex
          (fullDestinationPointIndex groupBitWidth dimension width source)
          valueBit,
        decodedGroupOrZero groupsPositive groupBitWidth
          (fullDestinationGroupBits groupBitWidth (dimension * width)
            source)))))

theorem gatherSourcePayloadWiring_eval
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool)
    (source : Fin (2 ^ (groupBitWidth + dimension * width))) :
    (fun bit => (gatherSourcePayloadWiring
      (requestsPerGroup := requestsPerGroup)
      groupsPositive groupBitWidth orderWidth source bit).eval input) =
      Fin.append (resourceSourceMetadata orderWidth source)
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          (gatherBankInput input) source) := by
  funext bit
  refine Fin.addCases (fun metadataBit => ?_) (fun valueBit => ?_) bit
  · simp [gatherSourcePayloadWiring, resourceSourceMetadata]
  · simp [gatherSourcePayloadWiring, resourceValuesFromBank,
      gatherBankInput, gatherBankInputIndex]

/-- A gather destination uses the same scheduled matching key as the
corresponding scatter source. -/
noncomputable def gatherDestinationKeyWiring
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) ->
      WiringBit (gatherAssemblyInputCount groups requestsPerGroup dimension
        width) :=
  let requestAndScalar := incidenceAt incidence
  let group := (requestGroupSlot capacity requestAndScalar.1).1
  Fin.cons (.constant false)
    (Fin.append
      (fun groupBit => .constant (finiteIndexBits groupBitWidth group groupBit))
      (fun pointBit => .input (gatherScheduleInputIndex
        (scheduledIncidencePointBitIndex capacity incidence pointBit))))

theorem gatherDestinationKeyWiring_eval
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    (fun bit => (gatherDestinationKeyWiring groupBitWidth capacity incidence
      bit).eval input) =
      scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        (gatherScheduleInput input) incidence := by
  rw [scheduledIncidenceKeyBits_eq_wiring]
  funext bit
  refine Fin.cases ?_ (fun tailBit => ?_) bit
  · simp [gatherDestinationKeyWiring, activeRoutingKey]
  · refine Fin.addCases (fun groupBit => ?_) (fun pointBit => ?_) tailBit
    · simp [gatherDestinationKeyWiring, activeRoutingKey,
        scheduledIncidenceSlotAt, scheduledIncidenceSlot]
    · simp [gatherDestinationKeyWiring, activeRoutingKey,
        gatherScheduleInput, gatherScheduleInputIndex]

/-- Destination ordering metadata is constant and its unused value field is
initialized to zero. -/
noncomputable def gatherDestinationPayloadWiring
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin ((orderWidth + 1) + width) -> WiringBit inputs :=
  Fin.append
    (fun metadataBit => .constant
      (destinationOrderMetadata incidenceFits incidence metadataBit))
    (fun _valueBit => .constant false)

/-- Gather padding uses a reserved metadata marker and a zero value. -/
noncomputable def gatherPaddingPayloadWiring
    (orderWidth width : Nat) :
    Fin ((orderWidth + 1) + width) -> WiringBit inputs :=
  Fin.append
    (fun metadataBit => .constant
      (paddingRoutingKey (fun _ : Fin orderWidth => false) metadataBit))
    (fun _valueBit => .constant false)

theorem gatherDestinationPayloadWiring_eval
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (input : Fin inputs -> Bool) :
    (fun bit => (gatherDestinationPayloadWiring incidenceFits incidence bit).eval
      input) =
      Fin.append (destinationOrderMetadata incidenceFits incidence)
        (fun _bit : Fin width => false) := by
  funext bit
  refine Fin.addCases (fun metadataBit => ?_) (fun valueBit => ?_) bit
  · simp [gatherDestinationPayloadWiring]
  · simp [gatherDestinationPayloadWiring]

theorem gatherPaddingPayloadWiring_eval
    (orderWidth width : Nat)
    (input : Fin inputs -> Bool) :
    (fun bit => (gatherPaddingPayloadWiring (inputs := inputs) orderWidth width
      bit).eval input) =
      Fin.append (paddingRoutingKey (fun _ : Fin orderWidth => false))
        (fun _bit : Fin width => false) := by
  funext bit
  refine Fin.addCases (fun metadataBit => ?_) (fun valueBit => ?_) bit
  · simp [gatherPaddingPayloadWiring]
  · simp [gatherPaddingPayloadWiring]

/-- Pure wiring specification for the gather-routing input array. -/
noncomputable def gatherAssemblySpecification
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :
    Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width)
        ((orderWidth + 1) + width))) ->
      WiringBit (gatherAssemblyInputCount groups requestsPerGroup dimension
        width) :=
  wiringRoutingInputBits
    (gatherSourceKeyWiring groupBitWidth dimension width)
    (gatherSourcePayloadWiring (requestsPerGroup := requestsPerGroup)
      groupsPositive groupBitWidth orderWidth)
    (gatherDestinationKeyWiring groupBitWidth capacity)
    (gatherDestinationPayloadWiring incidenceFits)
    (fun _padding bit => .constant
      (incidencePaddingKey groupBitWidth dimension width bit))
    (fun _padding => gatherPaddingPayloadWiring orderWidth width)
    recordCount

/-- Gather record assembly uses only wire selection and constants. -/
noncomputable def gatherAssemblyCircuit
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :=
  wiringCircuit (gatherAssemblySpecification groupsPositive
    groupBitWidth orderWidth incidenceFits capacity recordCount)

@[simp] theorem gatherAssemblyCircuit_cost
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :
    (gatherAssemblyCircuit groupsPositive groupBitWidth
      orderWidth incidenceFits capacity recordCount).cost
        DeMorgan.standardCost = 0 := by
  exact wiringCircuit_cost _

theorem gatherAssemblyCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    (gatherAssemblyCircuit groupsPositive groupBitWidth
      orderWidth incidenceFits capacity recordCount).eval
        DeMorgan.interpretation input =
      Routing.routingInputBits
        (fullResourceDestinationKeyBits groupBitWidth dimension width)
        (fun source => Fin.append (resourceSourceMetadata orderWidth source)
          (resourceValuesFromBank groupsPositive groupBitWidth dimension width
            (gatherBankInput input) source))
        (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
          (gatherScheduleInput input))
        (fun destination => Fin.append
          (destinationOrderMetadata incidenceFits destination)
          (fun _bit : Fin width => false))
        (fun _padding => incidencePaddingKey groupBitWidth dimension width)
        (fun _padding => Fin.append
          (paddingRoutingKey (fun _ : Fin orderWidth => false))
          (fun _bit : Fin width => false))
        recordCount := by
  rw [gatherAssemblyCircuit, wiringCircuit_eval,
    gatherAssemblySpecification, wiringRoutingInputBits_eval]
  congr 1
  · funext source
    exact gatherSourcePayloadWiring_eval groupsPositive groupBitWidth
      orderWidth input source
  · funext incidence
    exact gatherDestinationKeyWiring_eval widthPositive groupBitWidth
      capacity input incidence
  · funext destination
    exact gatherDestinationPayloadWiring_eval incidenceFits destination input
  · funext padding
    exact gatherPaddingPayloadWiring_eval orderWidth width input

/-- Complete metadata-preserving gather routing, including zero-cost record
assembly. -/
noncomputable def gatherRoutingCircuit
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :=
  (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit routingDepth
    (incidenceKeyWidth groupBitWidth dimension width)
    (orderWidth + 1) width).comp
      (gatherAssemblyCircuit groupsPositive groupBitWidth orderWidth
        incidenceFits capacity recordCount)

@[simp] theorem gatherRoutingCircuit_cost
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :
    (gatherRoutingCircuit groupsPositive groupBitWidth orderWidth
      incidenceFits capacity recordCount).cost DeMorgan.standardCost =
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit routingDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost := by
  rw [gatherRoutingCircuit, Circuit.cost_comp,
    gatherAssemblyCircuit_cost, Nat.zero_add]

theorem gatherRoutingCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    (gatherRoutingCircuit groupsPositive groupBitWidth orderWidth
      incidenceFits capacity recordCount).eval DeMorgan.interpretation input =
      canonicalGatherBits widthPositive groupBitWidth orderWidth incidenceFits
        capacity (gatherScheduleInput input)
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          (gatherBankInput input))
        (fun _destination _bit => false)
        (fun _padding _bit => false) recordCount := by
  rw [gatherRoutingCircuit, Circuit.eval_comp,
    CanonicalMetadataRouting.matchedCanonicalRoutingCircuit_eval,
    gatherAssemblyCircuit_eval groupsPositive widthPositive]
  rfl

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
  wiringCircuit (inputs := totalRequests * suffixWidth) fun output =>
    .constant (groupedTargetArrayBits widthPositive targets output)

@[simp] theorem fixedGroupedTargetAssemblyCircuit_cost
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive targets).cost DeMorgan.standardCost = 0 := by
  exact wiringCircuit_cost _

theorem fixedGroupedTargetAssemblyCircuit_eval
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive targets).eval DeMorgan.interpretation input =
      groupedTargetArrayBits widthPositive targets := by
  rw [fixedGroupedTargetAssemblyCircuit, wiringCircuit_eval]
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
