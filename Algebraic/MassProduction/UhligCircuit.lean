import Algebraic.Basis.DeMorgan.Arithmetic
import Algebraic.MassProduction.InputSplit
import Algebraic.MassProduction.ShannonSynthesis
import Algebraic.MassProduction.Uhlig

/-!
# Uhlig's finite mass-production layer

This module lifts Uhlig's two-request recovery invariant from a static vector
of values to arbitrary Boolean functions on independent row-major inputs.  It
is the semantic layer used by the quantitative Uhlig recursion: each pair of
requests chooses two disjoint recovery sets, and every resource function is
therefore evaluated on at most one suffix in that pair.

No asymptotic claim is hidden here.  The result below is an exact equality at
finite widths and for an arbitrary number of request pairs.
-/

namespace Algebraic
namespace MassProduction
namespace UhligCircuit

open scoped BigOperators

/-- The final source index among the `2 ^ prefixWidth` prefix assignments. -/
def prefixLast (prefixWidth : Nat) : Nat :=
  2 ^ prefixWidth - 1

theorem prefixCount_eq (prefixWidth : Nat) :
    prefixLast prefixWidth + 1 = 2 ^ prefixWidth := by
  unfold prefixLast
  have positive : 0 < 2 ^ prefixWidth := Nat.two_pow_pos prefixWidth
  omega

/-- Restrict the first `prefixWidth` variables of a Boolean function to one
canonical source value. -/
def restriction
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (source : Fin (prefixLast prefixWidth + 1)) :
    ScalarFunction Bool suffixWidth :=
  fun suffix => function (InputSplit.joinedInput
    (Fin.cast (prefixCount_eq prefixWidth) source) suffix)

/-- Uhlig's resource functions, now viewed as functions of the unspecialized
suffix variables. -/
def resourceFunction
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (resource : Fin (prefixLast prefixWidth + 2)) :
    ScalarFunction Bool suffixWidth :=
  uhligResource (fun source => restriction function source) resource

/-- Pair-major enumeration of the `2 * pairs` requests. -/
def pairRequest
    (pair : Fin pairs) (side : Fin 2) : Fin (2 * pairs) :=
  Fin.cast (Nat.mul_comm pairs 2) (finProdFinEquiv (pair, side))

/-- The full input block belonging to one side of one request pair. -/
def requestBlock
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    Fin (prefixWidth + suffixWidth) -> Bool :=
  directProductInput input (pairRequest pair side)

/-- The prefix bits of one request. -/
def requestPrefix
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Fin prefixWidth -> Bool :=
  fun bit => requestBlock input pair side (Fin.castAdd suffixWidth bit)

/-- The suffix bits of one request. -/
def requestSuffix
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Fin suffixWidth -> Bool :=
  fun bit => requestBlock input pair side (Fin.natAdd prefixWidth bit)

/-- Canonical numeric source selected by the request prefix. -/
def requestSource
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    Fin (prefixLast prefixWidth + 1) :=
  Fin.cast (prefixCount_eq prefixWidth).symm
    (RuntimePacking.source (requestPrefix input pair side))

/-- The two disjoint resource sets assigned to one request pair. -/
def recoveryPair
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) :
    Prod (Finset (Fin (prefixLast prefixWidth + 2)))
      (Finset (Fin (prefixLast prefixWidth + 2))) :=
  uhligRecoveryPair (requestSource input pair 0)
    (requestSource input pair 1)

/-- Runtime suffix sent to one resource.  Disjointness makes the first two
branches mutually exclusive; an unused resource receives an arbitrary zero
suffix. -/
def routedSuffix
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2)) :
    Fin suffixWidth -> Bool :=
  if resource ∈ (recoveryPair input pair).1 then
    requestSuffix input pair 0
  else if resource ∈ (recoveryPair input pair).2 then
    requestSuffix input pair 1
  else
    fun _ => false

/-- Value produced by one resource for one request pair. -/
def resourceValue
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2)) : Bool :=
  resourceFunction function resource (routedSuffix input pair resource)

/-- Decode one requested output by XORing its assigned resource values. -/
def decodedValue
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Bool :=
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases (recoveryPair input pair).1
    (fun _ => (recoveryPair input pair).2) side
  resources.sum fun resource => resourceValue function input pair resource

/-- The runtime prefix and suffix really reassemble the selected input
block. -/
theorem joined_request_eq_requestBlock
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    InputSplit.joinedInput
        (Fin.cast (prefixCount_eq prefixWidth)
          (requestSource input pair side))
        (requestSuffix input pair side) =
      requestBlock input pair side := by
  funext index
  refine Fin.addCases (motive := fun index =>
      InputSplit.joinedInput
          (Fin.cast (prefixCount_eq prefixWidth)
            (requestSource input pair side))
          (requestSuffix input pair side) index =
        requestBlock input pair side index)
    (fun prefixBit => ?_) (fun suffixBit => ?_) index
  · simp [InputSplit.joinedInput, requestSource, requestPrefix]
  · simp [InputSplit.joinedInput, requestSuffix]

theorem restriction_requestSource_requestSuffix
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    restriction function (requestSource input pair side)
        (requestSuffix input pair side) =
      function (requestBlock input pair side) := by
  unfold restriction
  rw [joined_request_eq_requestBlock]

theorem routedSuffix_eq_left
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2))
    (member : resource ∈ (recoveryPair input pair).1) :
    routedSuffix input pair resource = requestSuffix input pair 0 := by
  simp [routedSuffix, member]

theorem routedSuffix_eq_right
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2))
    (member : resource ∈ (recoveryPair input pair).2) :
    routedSuffix input pair resource = requestSuffix input pair 1 := by
  have disjoint :
      Disjoint (recoveryPair input pair).1 (recoveryPair input pair).2 := by
    exact uhligRecoveryPair_disjoint
      (requestSource input pair 0) (requestSource input pair 1)
  have notLeft : resource ∉ (recoveryPair input pair).1 := by
    intro leftMember
    exact Finset.disjoint_left.mp disjoint leftMember member
  simp [routedSuffix, member, notLeft]

/-- Exact correctness for one side of one pair. -/
theorem decodedValue_eq
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    decodedValue function input pair side =
      function (requestBlock input pair side) := by
  let values : Fin (prefixLast prefixWidth + 1) ->
      (Fin suffixWidth -> Bool) -> Bool :=
    fun source => restriction function source
  have recovery := uhligBoolean_two_copy_disjoint_recovery
    (Z := Fin suffixWidth -> Bool) values
    (requestSource input pair 0) (requestSource input pair 1)
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · change
      (recoveryPair input pair).1.sum
          (fun resource => resourceValue function input pair resource) =
        function (requestBlock input pair 0)
    have pointwise := congrFun recovery.2.1 (requestSuffix input pair 0)
    dsimp [values] at pointwise
    rw [restriction_requestSource_requestSuffix] at pointwise
    rw [recoveryPair]
    rw [Finset.sum_apply] at pointwise
    rw [← pointwise]
    apply Finset.sum_congr rfl
    intro resource member
    rw [resourceValue, routedSuffix_eq_left input pair resource member]
    rfl
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    change
      (recoveryPair input pair).2.sum
          (fun resource => resourceValue function input pair resource) =
        function (requestBlock input pair 1)
    have pointwise := congrFun recovery.2.2 (requestSuffix input pair 1)
    dsimp [values] at pointwise
    rw [restriction_requestSource_requestSuffix] at pointwise
    rw [recoveryPair]
    rw [Finset.sum_apply] at pointwise
    rw [← pointwise]
    apply Finset.sum_congr rfl
    intro resource member
    rw [resourceValue, routedSuffix_eq_right input pair resource member]
    rfl

/-- Exact row-major finite Uhlig layer: decoding all pairs is the ordinary
direct product of the original function. -/
theorem decodedValue_eq_directProduct
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool) :
    (fun output =>
        let pairSide := finProdFinEquiv.symm
          (Fin.cast (Nat.mul_comm 2 pairs) output)
        decodedValue function input pairSide.1 pairSide.2) =
      directProduct function (2 * pairs) input := by
  funext output
  let pairSide := finProdFinEquiv.symm
    (Fin.cast (Nat.mul_comm 2 pairs) output)
  have outputEq : pairRequest pairSide.1 pairSide.2 = output := by
    unfold pairRequest pairSide
    rw [Equiv.apply_symm_apply]
    simp
  rw [decodedValue_eq]
  unfold requestBlock
  rw [outputEq]
  rfl

/-! ## Explicit routing expressions -/

/-- Input coordinate in one two-request block. -/
def localInputIndex
    (side : Fin 2) (coordinate : Fin (prefixWidth + suffixWidth)) :
    Fin (2 * (prefixWidth + suffixWidth)) :=
  finProdFinEquiv (side, coordinate)

/-- Prefix bits in one two-request block. -/
def localPrefix
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (side : Fin 2) : Fin prefixWidth -> Bool :=
  fun bit => input (localInputIndex side (Fin.castAdd suffixWidth bit))

/-- Suffix bits in one two-request block. -/
def localSuffix
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (side : Fin 2) : Fin suffixWidth -> Bool :=
  fun bit => input (localInputIndex side (Fin.natAdd prefixWidth bit))

/-- Numeric source represented by a local request prefix. -/
def localSource
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (side : Fin 2) : Fin (prefixLast prefixWidth + 1) :=
  Fin.cast (prefixCount_eq prefixWidth).symm
    (RuntimePacking.source (localPrefix input side))

/-- Indicator that one local request prefix equals a fixed source. -/
def sourceIndicatorExpression
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    DeMorgan.Expression (2 * (prefixWidth + suffixWidth)) :=
  DeMorgan.Expression.finAnd prefixWidth fun bit =>
    ShannonSynthesis.matchingLiteral
      (localInputIndex side (Fin.castAdd suffixWidth bit))
      (InputSplit.sourceBits
        (Fin.cast (prefixCount_eq prefixWidth) source) bit)

theorem sourceIndicatorExpression_eval_eq_true_iff
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1))
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool) :
    (sourceIndicatorExpression side source).eval input = true <->
      localSource input side = source := by
  rw [sourceIndicatorExpression, DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · intro everyBit
    have bitsEqual : localPrefix input side = InputSplit.sourceBits
        (Fin.cast (prefixCount_eq prefixWidth) source) := by
      funext bit
      have bitMatch := everyBit bit
      rw [ShannonSynthesis.matchingLiteral_eval] at bitMatch
      exact of_decide_eq_true bitMatch
    simp [localSource, bitsEqual]
  · intro sourceEqual bit
    rw [ShannonSynthesis.matchingLiteral_eval]
    apply decide_eq_true
    have encodedEqual : RuntimePacking.source (localPrefix input side) =
        Fin.cast (prefixCount_eq prefixWidth) source := by
      have castEqual := congrArg
        (Fin.cast (prefixCount_eq prefixWidth)) sourceEqual
      simpa [localSource] using castEqual
    calc
      localPrefix input side bit =
          InputSplit.sourceBits
            (RuntimePacking.source (localPrefix input side)) bit :=
        (congrFun (InputSplit.sourceBits_runtimeSource
          (localPrefix input side)) bit).symm
      _ = InputSplit.sourceBits
          (Fin.cast (prefixCount_eq prefixWidth) source) bit :=
        congrFun (congrArg InputSplit.sourceBits encodedEqual) bit

/-- The fixed suffix input chosen for a resource after the two prefixes have
been hardwired. -/
def fixedRoutedSuffixExpression
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    DeMorgan.Expression (2 * (prefixWidth + suffixWidth)) :=
  if resource ∈ (uhligRecoveryPair first second).1 then
    .input (localInputIndex 0 (Fin.natAdd prefixWidth bit))
  else if resource ∈ (uhligRecoveryPair first second).2 then
    .input (localInputIndex 1 (Fin.natAdd prefixWidth bit))
  else
    .constant false

/-- Runtime routing for one suffix bit, written as a one-hot selection over
the two request prefixes. -/
def routedSuffixExpression
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    DeMorgan.Expression (2 * (prefixWidth + suffixWidth)) :=
  DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun first =>
    .and (sourceIndicatorExpression 0 first)
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun second =>
        .and (sourceIndicatorExpression 1 second)
          (fixedRoutedSuffixExpression first second resource bit))

theorem fixedRoutedSuffixExpression_eval
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth)
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool) :
    (fixedRoutedSuffixExpression first second resource bit).eval input =
      (if resource ∈ (uhligRecoveryPair first second).1 then
        localSuffix input 0 bit
      else if resource ∈ (uhligRecoveryPair first second).2 then
        localSuffix input 1 bit
      else false) := by
  by_cases leftMember : resource ∈ (uhligRecoveryPair first second).1
  · simp only [fixedRoutedSuffixExpression, if_pos leftMember]
    rfl
  · by_cases rightMember : resource ∈ (uhligRecoveryPair first second).2
    · simp only [fixedRoutedSuffixExpression, if_neg leftMember,
        if_pos rightMember]
      rfl
    · simp only [fixedRoutedSuffixExpression, if_neg leftMember,
        if_neg rightMember]
      rfl

theorem routedSuffixExpression_eval
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth)
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool) :
    (routedSuffixExpression resource bit).eval input =
      (if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).1 then
        localSuffix input 0 bit
      else if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).2 then
        localSuffix input 1 bit
      else false) := by
  rw [routedSuffixExpression, DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  let first := localSource input 0
  let second := localSource input 1
  have firstTrue :
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 0 first).eval
          input = true :=
    (sourceIndicatorExpression_eval_eq_true_iff 0 first input).2 rfl
  have firstUnique : forall candidate,
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 0 candidate).eval
          input = true -> candidate = first := by
    intro candidate candidateTrue
    exact ((sourceIndicatorExpression_eval_eq_true_iff
      0 candidate input).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) first
    (fun candidate =>
      (sourceIndicatorExpression (suffixWidth := suffixWidth)
        0 candidate).eval input)
    (fun candidate =>
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun other =>
        .and (sourceIndicatorExpression 1 other)
          (fixedRoutedSuffixExpression candidate other resource bit)).eval
        input)
    firstTrue firstUnique]
  rw [DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  have secondTrue :
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 1 second).eval
          input = true :=
    (sourceIndicatorExpression_eval_eq_true_iff 1 second input).2 rfl
  have secondUnique : forall candidate,
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 1 candidate).eval
          input = true -> candidate = second := by
    intro candidate candidateTrue
    exact ((sourceIndicatorExpression_eval_eq_true_iff
      1 candidate input).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) second
    (fun candidate =>
      (sourceIndicatorExpression (suffixWidth := suffixWidth)
        1 candidate).eval input)
    (fun candidate =>
      (fixedRoutedSuffixExpression first candidate resource bit).eval input)
    secondTrue secondUnique]
  exact fixedRoutedSuffixExpression_eval first second resource bit input

/-- Explicit circuit routing one pair's suffix to one Uhlig resource. -/
noncomputable def resourceRouterCircuit
    (resource : Fin (prefixLast prefixWidth + 2)) :
    Circuit DeMorgan.signature (2 * (prefixWidth + suffixWidth))
      (Finset.univ.sum fun bit : Fin suffixWidth =>
        (routedSuffixExpression resource bit).gateCount)
      suffixWidth :=
  Circuit.parallelFin suffixWidth
    (fun bit => (routedSuffixExpression resource bit).gateCount)
    (fun bit => (routedSuffixExpression resource bit).circuit)

@[simp] theorem resourceRouterCircuit_eval
    (resource : Fin (prefixLast prefixWidth + 2))
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (bit : Fin suffixWidth) :
    (resourceRouterCircuit resource).eval DeMorgan.interpretation input bit =
      (if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).1 then
        localSuffix input 0 bit
      else if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).2 then
        localSuffix input 1 bit
      else false) := by
  rw [resourceRouterCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval, routedSuffixExpression_eval]

/-! ## Batched routing and supplied resource circuits -/

/-- Embed one local two-request input into the corresponding global pair. -/
def pairInputMap
    (pair : Fin pairs)
    (input : Fin (2 * (prefixWidth + suffixWidth))) :
    Fin ((2 * pairs) * (prefixWidth + suffixWidth)) :=
  let sideCoordinate := finProdFinEquiv.symm input
  finProdFinEquiv
    (pairRequest pair sideCoordinate.1, sideCoordinate.2)

@[simp] theorem pairInputMap_localInputIndex
    (pair : Fin pairs)
    (side : Fin 2)
    (coordinate : Fin (prefixWidth + suffixWidth)) :
    pairInputMap pair (localInputIndex side coordinate) =
      finProdFinEquiv (pairRequest pair side, coordinate) := by
  simp [pairInputMap, localInputIndex]

theorem localPrefix_pairInputMap
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    localPrefix (input ∘ pairInputMap pair) side =
      requestPrefix input pair side := by
  funext bit
  simp [localPrefix, requestPrefix, requestBlock, directProductInput,
    Function.comp_apply]

theorem localSuffix_pairInputMap
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    localSuffix (input ∘ pairInputMap pair) side =
      requestSuffix input pair side := by
  funext bit
  simp [localSuffix, requestSuffix, requestBlock, directProductInput,
    Function.comp_apply]

theorem localSource_pairInputMap
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    localSource (input ∘ pairInputMap pair) side =
      requestSource input pair side := by
  simp [localSource, requestSource, localPrefix_pairInputMap]

/-- Charged/gate count of one resource router. -/
@[reducible] noncomputable def resourceRouterGateCount
    (prefixWidth suffixWidth : Nat)
    (resource : Fin (prefixLast prefixWidth + 2)) : Nat :=
  Finset.univ.sum fun bit : Fin suffixWidth =>
    (routedSuffixExpression resource bit).gateCount

/-- Route all request pairs to one shared resource circuit. -/
noncomputable def resourceRouterArrayCircuit
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2)) :
    Circuit DeMorgan.signature
      ((2 * pairs) * (prefixWidth + suffixWidth))
      (Finset.univ.sum fun _pair : Fin pairs =>
        resourceRouterGateCount prefixWidth suffixWidth resource)
      (pairs * suffixWidth) :=
  Circuit.parallelFinVector pairs suffixWidth
    (fun _pair => resourceRouterGateCount prefixWidth suffixWidth resource)
    (fun pair => (resourceRouterCircuit resource).mapInputs
      (pairInputMap pair))

@[simp] theorem resourceRouterArrayCircuit_eval
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (bit : Fin suffixWidth) :
    (resourceRouterArrayCircuit pairs resource).eval
        DeMorgan.interpretation input (finProdFinEquiv (pair, bit)) =
      routedSuffix input pair resource bit := by
  rw [resourceRouterArrayCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs, resourceRouterCircuit_eval]
  rw [localSource_pairInputMap, localSource_pairInputMap,
    localSuffix_pairInputMap, localSuffix_pairInputMap]
  unfold routedSuffix recoveryPair
  by_cases leftMember : resource ∈
      (uhligRecoveryPair (requestSource input pair 0)
        (requestSource input pair 1)).1
  · simp [leftMember]
  · by_cases rightMember : resource ∈
        (uhligRecoveryPair (requestSource input pair 0)
          (requestSource input pair 1)).2
    · simp [leftMember, rightMember]
    · simp [leftMember, rightMember]

/-- Compose one supplied `pairs`-copy resource circuit after its explicit
Uhlig router. -/
noncomputable def routedResourceCircuit
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2))
    (resourceCircuit : Circuit DeMorgan.signature
      (pairs * suffixWidth) gates pairs) :
    Circuit DeMorgan.signature
      ((2 * pairs) * (prefixWidth + suffixWidth))
      ((Finset.univ.sum fun _pair : Fin pairs =>
          resourceRouterGateCount prefixWidth suffixWidth resource) +
        gates)
      pairs :=
  resourceCircuit.comp (resourceRouterArrayCircuit pairs resource)

theorem routedResourceCircuit_eval
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2))
    (resourceCircuit : Circuit DeMorgan.signature
      (pairs * suffixWidth) gates pairs)
    (computes : resourceCircuit.Computes DeMorgan.interpretation
      (directProduct (resourceFunction function resource) pairs))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) :
    (routedResourceCircuit pairs resource resourceCircuit).eval
        DeMorgan.interpretation input pair =
      resourceValue function input pair resource := by
  rw [routedResourceCircuit, Circuit.eval_comp, computes]
  unfold directProduct resourceValue
  apply congrArg (resourceFunction function resource)
  funext bit
  exact resourceRouterArrayCircuit_eval pairs resource input pair bit

/-- Gate count of one routed supplied resource circuit. -/
@[reducible] noncomputable def routedResourceGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resource : Fin (prefixLast prefixWidth + 2)) : Nat :=
  (Finset.univ.sum fun _pair : Fin pairs =>
      resourceRouterGateCount prefixWidth suffixWidth resource) +
    resourceGateCounts resource

/-- All Uhlig resources evaluated in parallel, in `(resource, pair)` order. -/
noncomputable def resourceBankCircuit
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    Circuit DeMorgan.signature
      ((2 * pairs) * (prefixWidth + suffixWidth))
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        routedResourceGateCount prefixWidth suffixWidth pairs
          resourceGateCounts resource)
      ((prefixLast prefixWidth + 2) * pairs) :=
  Circuit.parallelFinVector (prefixLast prefixWidth + 2) pairs
    (routedResourceGateCount prefixWidth suffixWidth pairs
      resourceGateCounts)
    (fun resource => routedResourceCircuit pairs resource
      (resourceCircuits resource))

theorem resourceBankCircuit_eval
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).Computes DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    (resourceBankCircuit pairs resourceGateCounts resourceCircuits).eval
        DeMorgan.interpretation input (finProdFinEquiv (resource, pair)) =
      resourceValue function input pair resource := by
  rw [resourceBankCircuit, Circuit.eval_parallelFinVector]
  exact routedResourceCircuit_eval function pairs resource
    (resourceCircuits resource) (computes resource) input pair

@[simp] theorem resourceBankCircuit_cost
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (resourceBankCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost) := by
  simp [resourceBankCircuit, routedResourceCircuit,
    resourceRouterArrayCircuit]

/-! ## Explicit XOR decoder -/

/-- Reindex the inputs of a De Morgan expression. -/
def reindexExpression
    (inputMap : Fin sourceInputs -> Fin targetInputs) :
    DeMorgan.Expression sourceInputs -> DeMorgan.Expression targetInputs
  | .input index => .input (inputMap index)
  | .constant value => .constant value
  | .not child => .not (reindexExpression inputMap child)
  | .and left right =>
      .and (reindexExpression inputMap left)
        (reindexExpression inputMap right)
  | .or left right =>
      .or (reindexExpression inputMap left)
        (reindexExpression inputMap right)

@[simp] theorem reindexExpression_eval
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : DeMorgan.Expression sourceInputs)
    (input : Fin targetInputs -> Bool) :
    (reindexExpression inputMap expression).eval input =
      expression.eval (input ∘ inputMap) := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | not child inductionHypothesis =>
      simp [reindexExpression, DeMorgan.Expression.eval,
        inductionHypothesis]
  | and left right leftIH rightIH =>
      simp [reindexExpression, DeMorgan.Expression.eval, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [reindexExpression, DeMorgan.Expression.eval, leftIH, rightIH]

@[simp] theorem reindexExpression_gateCount
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : DeMorgan.Expression sourceInputs) :
    (reindexExpression inputMap expression).gateCount =
      expression.gateCount := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | not child inductionHypothesis =>
      simp [reindexExpression, DeMorgan.Expression.gateCount,
        inductionHypothesis]
  | and left right leftIH rightIH =>
      simp [reindexExpression, DeMorgan.Expression.gateCount,
        leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [reindexExpression, DeMorgan.Expression.gateCount,
        leftIH, rightIH]

@[simp] theorem reindexExpression_standardCost
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : DeMorgan.Expression sourceInputs) :
    (reindexExpression inputMap expression).standardCost =
      expression.standardCost := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | not child inductionHypothesis =>
      simp [reindexExpression, DeMorgan.Expression.standardCost,
        inductionHypothesis]
  | and left right leftIH rightIH =>
      simp [reindexExpression, DeMorgan.Expression.standardCost,
        leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [reindexExpression, DeMorgan.Expression.standardCost,
        leftIH, rightIH]

/-- De Morgan implementation of Boolean XOR. -/
def xorExpression
    (left right : DeMorgan.Expression inputs) :
    DeMorgan.Expression inputs :=
  .and (.or left right) (.not (.and left right))

@[simp] theorem xorExpression_eval
    (left right : DeMorgan.Expression inputs)
    (input : Fin inputs -> Bool) :
    (xorExpression left right).eval input =
      left.eval input + right.eval input := by
  rw [Bool.add_eq_xor]
  cases leftValue : left.eval input <;>
    cases rightValue : right.eval input <;>
      simp [xorExpression, DeMorgan.Expression.eval,
        leftValue, rightValue]

/-- XOR a finite expression family, with false for the empty family. -/
def finXor :
    (count : Nat) -> (Fin count -> DeMorgan.Expression inputs) ->
      DeMorgan.Expression inputs
  | 0, _ => .constant false
  | count + 1, terms =>
      xorExpression (finXor count (fun index => terms index.castSucc))
        (terms (Fin.last count))

@[simp] theorem finXor_eval
    (count : Nat)
    (terms : Fin count -> DeMorgan.Expression inputs)
    (input : Fin inputs -> Bool) :
    (finXor count terms).eval input =
      Finset.univ.sum fun index => (terms index).eval input := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finXor, xorExpression_eval, inductionHypothesis,
        Fin.sum_univ_castSucc]

/-- Number of original input wires in one batched Uhlig layer. -/
@[reducible] def layerInputCount
    (prefixWidth suffixWidth pairs : Nat) : Nat :=
  (2 * pairs) * (prefixWidth + suffixWidth)

/-- Number of resource-result wires in one batched Uhlig layer. -/
@[reducible] def layerResourceOutputCount (prefixWidth pairs : Nat) : Nat :=
  (prefixLast prefixWidth + 2) * pairs

/-- Original inputs followed by every `(resource, pair)` result. -/
@[reducible] def layerStateCount
    (prefixWidth suffixWidth pairs : Nat) : Nat :=
  layerInputCount prefixWidth suffixWidth pairs +
    layerResourceOutputCount prefixWidth pairs

/-- Read the original-input prefix of a layer state. -/
def originalInputFromState
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool :=
  fun input => state
    (Fin.castAdd (layerResourceOutputCount prefixWidth pairs) input)

/-- State wire carrying one resource result. -/
def resourceStateIndex
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    Fin (layerStateCount prefixWidth suffixWidth pairs) :=
  Fin.natAdd (layerInputCount prefixWidth suffixWidth pairs)
    (finProdFinEquiv (resource, pair))

/-- Embed one local pair input into the original-input prefix of a layer
state. -/
def stateLocalInputMap
    (pair : Fin pairs)
    (input : Fin (2 * (prefixWidth + suffixWidth))) :
    Fin (layerStateCount prefixWidth suffixWidth pairs) :=
  Fin.castAdd (layerResourceOutputCount prefixWidth pairs)
    (pairInputMap pair input)

/-- Prefix equality test for one request inside a layer state. -/
def stateSourceIndicatorExpression
    (pair : Fin pairs)
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  reindexExpression (stateLocalInputMap pair)
    (sourceIndicatorExpression (suffixWidth := suffixWidth) side source)

theorem stateSourceIndicatorExpression_eval_eq_true_iff
    (pair : Fin pairs)
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (stateSourceIndicatorExpression pair side source).eval state = true <->
      requestSource (originalInputFromState state) pair side = source := by
  rw [stateSourceIndicatorExpression, reindexExpression_eval,
    sourceIndicatorExpression_eval_eq_true_iff]
  have composition : state ∘ stateLocalInputMap pair =
      originalInputFromState state ∘ pairInputMap pair := by
    rfl
  rw [composition, localSource_pairInputMap]

/-- Resource-result input expression for the decoder. -/
def resourceValueExpression
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  .input (resourceStateIndex resource pair)

/-- One fixed decoder term: either the selected resource-result wire or the
free false constant. -/
def fixedResourceTermExpression
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases (uhligRecoveryPair first second).1
      (fun _ => (uhligRecoveryPair first second).2) side
  if resource ∈ resources then resourceValueExpression resource pair
  else .constant false

/-- XOR decoder for fixed prefix values. -/
def fixedDecodedExpression
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  finXor (prefixLast prefixWidth + 2) fun resource =>
    fixedResourceTermExpression pair side first second resource

theorem fixedDecodedExpression_eval
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (fixedDecodedExpression pair side first second).eval state =
      let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
        Fin.cases (uhligRecoveryPair first second).1
          (fun _ => (uhligRecoveryPair first second).2) side
      resources.sum fun resource => state (resourceStateIndex resource pair) := by
  classical
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases (uhligRecoveryPair first second).1
      (fun _ => (uhligRecoveryPair first second).2) side
  rw [fixedDecodedExpression, finXor_eval]
  simp only [fixedResourceTermExpression]
  simp_rw [apply_ite (DeMorgan.Expression.eval state)]
  simp only [DeMorgan.Expression.eval, resourceValueExpression]
  change
    (Finset.univ.sum fun resource =>
      if resource ∈ resources then
        state (resourceStateIndex resource pair)
      else false) =
      resources.sum fun resource => state (resourceStateIndex resource pair)
  calc
    (Finset.univ.sum fun resource =>
        if resource ∈ resources then
          state (resourceStateIndex resource pair)
        else false) =
        resources.sum (fun resource =>
          if resource ∈ resources then
            state (resourceStateIndex resource pair)
          else false) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ resources)
      intro resource _inUniv notSelected
      simp [notSelected]
      rfl
    _ = resources.sum
        (fun resource => state (resourceStateIndex resource pair)) := by
      apply Finset.sum_congr rfl
      intro resource selected
      simp [selected]

/-- Runtime decoder selected by the two actual request prefixes. -/
def decodedExpression
    (pair : Fin pairs) (side : Fin 2) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun first =>
    .and (stateSourceIndicatorExpression pair 0 first)
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun second =>
        .and (stateSourceIndicatorExpression pair 1 second)
          (fixedDecodedExpression pair side first second))

/-- Semantic decoder on a completed layer state. -/
def decodedStateValue
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Bool :=
  let original := originalInputFromState state
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases
      (uhligRecoveryPair (requestSource original pair 0)
        (requestSource original pair 1)).1
      (fun _ =>
        (uhligRecoveryPair (requestSource original pair 0)
          (requestSource original pair 1)).2)
      side
  resources.sum fun resource => state (resourceStateIndex resource pair)

theorem decodedExpression_eval
    (pair : Fin pairs) (side : Fin 2)
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (decodedExpression pair side).eval state =
      decodedStateValue state pair side := by
  rw [decodedExpression, DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  let first := requestSource (originalInputFromState state) pair 0
  let second := requestSource (originalInputFromState state) pair 1
  have firstTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 first state).2 rfl
  have firstUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state = true -> candidate = first := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 candidate state).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) first
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state)
    (fun candidate =>
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun other =>
        .and (stateSourceIndicatorExpression pair 1 other)
          (fixedDecodedExpression pair side candidate other)).eval state)
    firstTrue firstUnique]
  rw [DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  have secondTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 second state).2 rfl
  have secondUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state = true -> candidate = second := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 candidate state).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) second
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state)
    (fun candidate =>
      (fixedDecodedExpression pair side first candidate).eval state)
    secondTrue secondUnique]
  rw [fixedDecodedExpression_eval]
  rfl

/-! ## Decoder circuit -/

/-- Recover the pair and side represented by a row-major direct-product
output. -/
def decoderPairSide (output : Fin (2 * pairs)) : Fin pairs × Fin 2 :=
  finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 pairs) output)

/-- Decoder expression attached to one row-major output. -/
def decoderOutputExpression
    (output : Fin (2 * pairs)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  let pairSide := decoderPairSide output
  decodedExpression pairSide.1 pairSide.2

/-- Gate count of one compiled decoder output. -/
@[reducible] noncomputable def decoderGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (output : Fin (2 * pairs)) : Nat :=
  (decoderOutputExpression (prefixWidth := prefixWidth)
    (suffixWidth := suffixWidth) output).gateCount

/-- All requested outputs decoded in ordinary row-major order. -/
noncomputable def decoderCircuit
    (prefixWidth suffixWidth pairs : Nat) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        decoderGateCount prefixWidth suffixWidth pairs output)
      (2 * pairs) :=
  Circuit.parallelFin (2 * pairs)
    (decoderGateCount prefixWidth suffixWidth pairs)
    (fun output =>
      (decoderOutputExpression (prefixWidth := prefixWidth)
        (suffixWidth := suffixWidth) output).circuit)

@[simp] theorem decoderCircuit_eval
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (output : Fin (2 * pairs)) :
    (decoderCircuit prefixWidth suffixWidth pairs).eval
        DeMorgan.interpretation state output =
      let pairSide := decoderPairSide output
      decodedStateValue state pairSide.1 pairSide.2 := by
  rw [decoderCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval, decoderOutputExpression,
    decodedExpression_eval]

@[simp] theorem decoderCircuit_cost
    (prefixWidth suffixWidth pairs : Nat) :
    (decoderCircuit prefixWidth suffixWidth pairs).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun output : Fin (2 * pairs) =>
        (decoderOutputExpression (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) output).standardCost := by
  simp [decoderCircuit]

/-! ## Shared linear-size Boolean folds -/

/-- Arithmetic XOR of all input wires.  Compiling the arithmetic addition
gate preserves sharing, so this avoids the duplication inherent in a
De Morgan formula for XOR. -/
def xorInputExpression (count : Nat) :
    Arithmetic.Expression Bool count :=
  DeMorgan.ArithmeticExpression.finSum count fun input => .input input

/-- Program-gate count of the shared XOR fold. -/
@[reducible] noncomputable def xorInputGateCount (count : Nat) : Nat :=
  DeMorgan.arithmeticTranslation.compiledGateCount
    (xorInputExpression count).circuit

/-- De Morgan circuit obtained by compiling the shared arithmetic XOR fold. -/
noncomputable def xorInputCircuit (count : Nat) :
    Circuit DeMorgan.signature count (xorInputGateCount count) 1 :=
  DeMorgan.ArithmeticExpression.circuit (xorInputExpression count)

@[simp] theorem xorInputCircuit_eval
    (count : Nat) (input : Fin count -> Bool) :
    (xorInputCircuit count).eval DeMorgan.interpretation input 0 =
      Finset.univ.sum input := by
  rw [xorInputCircuit, DeMorgan.ArithmeticExpression.circuit_eval,
    xorInputExpression, DeMorgan.ArithmeticExpression.finSum_eval]
  rfl

@[simp] theorem xorInputCircuit_cost (count : Nat) :
    (xorInputCircuit count).cost DeMorgan.standardCost = count * 4 := by
  rw [xorInputCircuit, DeMorgan.ArithmeticExpression.circuit_cost,
    xorInputExpression,
    DeMorgan.ArithmeticExpression.finSum_weightedCost]
  simp [Arithmetic.Expression.weightedCost]

/-- OR of all input wires. -/
def orInputExpression (count : Nat) : DeMorgan.Expression count :=
  DeMorgan.Expression.finOr count fun input => .input input

/-- Program-gate count of the shared OR fold. -/
@[reducible] def orInputGateCount (count : Nat) : Nat :=
  (orInputExpression count).gateCount

/-- De Morgan circuit implementing the shared OR fold. -/
def orInputCircuit (count : Nat) :
    Circuit DeMorgan.signature count (orInputGateCount count) 1 :=
  (orInputExpression count).circuit

@[simp] theorem orInputCircuit_eval
    (count : Nat) (input : Fin count -> Bool) :
    (orInputCircuit count).eval DeMorgan.interpretation input 0 =
      DeMorgan.Expression.finOrValue count input := by
  rw [orInputCircuit, DeMorgan.Expression.circuit_eval,
    orInputExpression, DeMorgan.Expression.finOr_eval]
  rfl

@[simp] theorem orInputCircuit_cost (count : Nat) :
    (orInputCircuit count).cost DeMorgan.standardCost = count := by
  rw [orInputCircuit, DeMorgan.Expression.circuit_cost,
    orInputExpression, DeMorgan.Expression.finOr_standardCost]
  simp [DeMorgan.Expression.standardCost]

/-- Produce all fixed-prefix resource terms before their shared XOR fold. -/
noncomputable def fixedResourceVectorCircuit
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        (fixedResourceTermExpression (suffixWidth := suffixWidth)
          pair side first second resource).gateCount)
      (prefixLast prefixWidth + 2) :=
  Circuit.parallelFin (prefixLast prefixWidth + 2)
    (fun resource =>
      (fixedResourceTermExpression (suffixWidth := suffixWidth)
        pair side first second resource).gateCount)
    (fun resource =>
      (fixedResourceTermExpression (suffixWidth := suffixWidth)
        pair side first second resource).circuit)

@[simp] theorem fixedResourceVectorCircuit_eval
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (fixedResourceVectorCircuit (suffixWidth := suffixWidth)
      pair side first second).eval
        DeMorgan.interpretation state resource =
      (fixedResourceTermExpression (suffixWidth := suffixWidth)
        pair side first second resource).eval
        state := by
  rw [fixedResourceVectorCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]

@[simp] theorem fixedResourceVectorCircuit_cost
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    (fixedResourceVectorCircuit (suffixWidth := suffixWidth)
      pair side first second).cost
        DeMorgan.standardCost = 0 := by
  rw [fixedResourceVectorCircuit, Circuit.cost_parallelFin]
  apply Finset.sum_eq_zero
  intro resource _member
  rw [DeMorgan.Expression.circuit_cost]
  unfold fixedResourceTermExpression
  dsimp only
  split <;> rfl

/-- Fixed-prefix decoder with a circuit-level shared XOR fold. -/
noncomputable def sharedFixedDecodedCircuit
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          (fixedResourceTermExpression (suffixWidth := suffixWidth)
            pair side first second resource).gateCount) +
        xorInputGateCount (prefixLast prefixWidth + 2))
      1 :=
  (xorInputCircuit (prefixLast prefixWidth + 2)).comp
    (fixedResourceVectorCircuit (suffixWidth := suffixWidth)
      pair side first second)

@[simp] theorem sharedFixedDecodedCircuit_eval
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).eval
        DeMorgan.interpretation state 0 =
      let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
        Fin.cases (uhligRecoveryPair first second).1
          (fun _ => (uhligRecoveryPair first second).2) side
      resources.sum fun resource =>
        state (resourceStateIndex resource pair) := by
  calc
    (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).eval
        DeMorgan.interpretation state 0 =
        Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          (fixedResourceTermExpression (suffixWidth := suffixWidth)
            pair side first second resource).eval
            state := by
      rw [sharedFixedDecodedCircuit, Circuit.eval_comp,
        xorInputCircuit_eval]
      apply Finset.sum_congr rfl
      intro resource _member
      exact fixedResourceVectorCircuit_eval pair side first second state
        resource
    _ = (fixedDecodedExpression pair side first second).eval state := by
      rw [fixedDecodedExpression, finXor_eval]
    _ = _ := fixedDecodedExpression_eval pair side first second state

@[simp] theorem sharedFixedDecodedCircuit_cost
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).cost
        DeMorgan.standardCost = 4 * (prefixLast prefixWidth + 2) := by
  rw [sharedFixedDecodedCircuit, Circuit.cost_comp,
    fixedResourceVectorCircuit_cost, xorInputCircuit_cost]
  omega

/-- Three-input postprocessor for one candidate prefix pair.  The second
source indicator is outermost so the row decoder has one-hot form. -/
def candidatePostprocessExpression : DeMorgan.Expression 3 :=
  .and (.input 1) (.and (.input 0) (.input 2))

@[simp] theorem candidatePostprocessExpression_eval
    (input : Fin 3 -> Bool) :
    candidatePostprocessExpression.eval input =
      (input 1 && (input 0 && input 2)) := rfl

/-- Program-gate count of one fully specified decoder candidate. -/
@[reducible] noncomputable def candidateDecodedGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) : Nat :=
  (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
      pair 0 first).gateCount +
    ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).gateCount +
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          (fixedResourceTermExpression (suffixWidth := suffixWidth)
            pair side first second resource).gateCount) +
        xorInputGateCount (prefixLast prefixWidth + 2))) +
    candidatePostprocessExpression.gateCount

/-- Circuit for one hardwired pair of possible request prefixes. -/
noncomputable def candidateDecodedCircuit
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (candidateDecodedGateCount prefixWidth suffixWidth pairs
        pair side first second)
      1 :=
  candidatePostprocessExpression.circuit.comp
    ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
      pair 0 first).circuit.parallel
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).circuit.parallel
        (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
          pair side first second)))

@[simp] theorem candidateDecodedCircuit_eval
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (candidateDecodedCircuit pair side first second).eval
        DeMorgan.interpretation state 0 =
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 1 second).eval state &&
        ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
            pair 0 first).eval state &&
          (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
            pair side first second).eval DeMorgan.interpretation state 0)) := by
  change
    (candidatePostprocessExpression.circuit.comp
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).circuit.parallel
        ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 1 second).circuit.parallel
          (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
            pair side first second)))).eval
        DeMorgan.interpretation state 0 = _
  rw [Circuit.eval_comp, DeMorgan.Expression.circuit_eval,
    candidatePostprocessExpression_eval, Circuit.eval_parallel,
    Circuit.eval_parallel]
  rw [show (1 : Fin 3) =
      Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1)) by rfl,
    Fin.append_right, Fin.append_left]
  rw [show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) by rfl,
    Fin.append_left]
  rw [show (2 : Fin 3) =
      Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1)) by rfl,
    Fin.append_right, Fin.append_right]
  rw [DeMorgan.Expression.circuit_eval,
    DeMorgan.Expression.circuit_eval]

/-- Program-gate count of one row of decoder candidates. -/
@[reducible] noncomputable def candidateRowGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1)) : Nat :=
  (Finset.univ.sum fun second : Fin (prefixLast prefixWidth + 1) =>
      candidateDecodedGateCount prefixWidth suffixWidth pairs
        pair side first second) +
    orInputGateCount (prefixLast prefixWidth + 1)

/-- OR all candidates for the second request prefix while retaining one
fixed candidate for the first prefix. -/
noncomputable def candidateRowCircuit
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (candidateRowGateCount prefixWidth suffixWidth pairs pair side first)
      1 :=
  (orInputCircuit (prefixLast prefixWidth + 1)).comp
    (Circuit.parallelFin (prefixLast prefixWidth + 1)
      (fun second => candidateDecodedGateCount
        prefixWidth suffixWidth pairs pair side first second)
      (fun second => candidateDecodedCircuit pair side first second))

@[simp] theorem candidateRowCircuit_eval
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (candidateRowCircuit pair side first).eval
        DeMorgan.interpretation state 0 =
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 0 first).eval state &&
        (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
          pair side first
          (requestSource (originalInputFromState state) pair 1)).eval
            DeMorgan.interpretation state 0) := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun second => candidateDecodedGateCount
          prefixWidth suffixWidth pairs pair side first second)
        (fun second =>
          candidateDecodedCircuit pair side first second))).eval
        DeMorgan.interpretation state 0 = _
  rw [Circuit.eval_comp, orInputCircuit_eval]
  have bankEval :
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun second => candidateDecodedGateCount
          prefixWidth suffixWidth pairs pair side first second)
        (fun second => candidateDecodedCircuit pair side first second)).eval
          DeMorgan.interpretation state =
        fun second =>
          (candidateDecodedCircuit pair side first second).eval
            DeMorgan.interpretation state 0 := by
    funext second
    exact Circuit.eval_parallelFin _ _ _ _ _ second
  rw [bankEval]
  simp only [candidateDecodedCircuit_eval]
  let second := requestSource (originalInputFromState state) pair 1
  have secondTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 second state).2 rfl
  have secondUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state = true -> candidate = second := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 candidate state).1 candidateTrue).symm
  exact DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) second
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state)
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 0 first).eval state &&
        (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
          pair side first candidate).eval DeMorgan.interpretation state 0)
    secondTrue secondUnique

/-- Program-gate count of one complete shared output decoder. -/
@[reducible] noncomputable def sharedDecodedGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (pair : Fin pairs) (side : Fin 2) : Nat :=
  (Finset.univ.sum fun first : Fin (prefixLast prefixWidth + 1) =>
      candidateRowGateCount prefixWidth suffixWidth pairs pair side first) +
    orInputGateCount (prefixLast prefixWidth + 1)

/-- Shared decoder for one requested output. -/
noncomputable def sharedDecodedCircuit
    (pair : Fin pairs) (side : Fin 2) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (sharedDecodedGateCount prefixWidth suffixWidth pairs pair side)
      1 :=
  (orInputCircuit (prefixLast prefixWidth + 1)).comp
    (Circuit.parallelFin (prefixLast prefixWidth + 1)
      (fun first => candidateRowGateCount
        prefixWidth suffixWidth pairs pair side first)
      (fun first => candidateRowCircuit pair side first))

@[simp] theorem sharedDecodedCircuit_eval
    (pair : Fin pairs) (side : Fin 2)
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (sharedDecodedCircuit pair side).eval
        DeMorgan.interpretation state 0 =
      decodedStateValue state pair side := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun first => candidateRowGateCount
          prefixWidth suffixWidth pairs pair side first)
        (fun first => candidateRowCircuit pair side first))).eval
        DeMorgan.interpretation state 0 = _
  rw [Circuit.eval_comp, orInputCircuit_eval]
  have bankEval :
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun first => candidateRowGateCount
          prefixWidth suffixWidth pairs pair side first)
        (fun first => candidateRowCircuit pair side first)).eval
          DeMorgan.interpretation state =
        fun first =>
          (candidateRowCircuit pair side first).eval
            DeMorgan.interpretation state 0 := by
    funext first
    exact Circuit.eval_parallelFin _ _ _ _ _ first
  rw [bankEval]
  simp only [candidateRowCircuit_eval]
  let first := requestSource (originalInputFromState state) pair 0
  have firstTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 first state).2 rfl
  have firstUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state = true -> candidate = first := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 candidate state).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) first
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state)
    (fun candidate =>
      (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
        pair side candidate
          (requestSource (originalInputFromState state) pair 1)).eval
            DeMorgan.interpretation state 0)
    firstTrue firstUnique]
  rw [sharedFixedDecodedCircuit_eval]
  rfl

/-- Gate count of the shared decoder attached to one row-major output. -/
@[reducible] noncomputable def sharedDecoderOutputGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (output : Fin (2 * pairs)) : Nat :=
  let pairSide := decoderPairSide output
  sharedDecodedGateCount prefixWidth suffixWidth pairs
    pairSide.1 pairSide.2

/-- Shared decoders for all row-major outputs. -/
noncomputable def sharedDecoderCircuit
    (prefixWidth suffixWidth pairs : Nat) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        sharedDecoderOutputGateCount prefixWidth suffixWidth pairs output)
      (2 * pairs) :=
  Circuit.parallelFin (2 * pairs)
    (sharedDecoderOutputGateCount prefixWidth suffixWidth pairs)
    (fun output =>
      let pairSide := decoderPairSide output
      sharedDecodedCircuit pairSide.1 pairSide.2)

@[simp] theorem sharedDecoderCircuit_eval
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (output : Fin (2 * pairs)) :
    (sharedDecoderCircuit prefixWidth suffixWidth pairs).eval
        DeMorgan.interpretation state output =
      let pairSide := decoderPairSide output
      decodedStateValue state pairSide.1 pairSide.2 := by
  rw [sharedDecoderCircuit, Circuit.eval_parallelFin]
  dsimp only
  exact sharedDecodedCircuit_eval
    (prefixWidth := prefixWidth) (suffixWidth := suffixWidth)
    (decoderPairSide output).1 (decoderPairSide output).2 state

@[simp] theorem sharedDecoderCircuit_cost
    (prefixWidth suffixWidth pairs : Nat) :
    (sharedDecoderCircuit prefixWidth suffixWidth pairs).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun output : Fin (2 * pairs) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
            DeMorgan.standardCost := by
  rw [sharedDecoderCircuit, Circuit.cost_parallelFin]

/-! ## Complete finite Uhlig layer -/

/-- Preserve the original inputs and append every routed resource value. -/
noncomputable def layerStateCircuit
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    Circuit DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        routedResourceGateCount prefixWidth suffixWidth pairs
          resourceGateCounts resource)
      (layerStateCount prefixWidth suffixWidth pairs) :=
  (Circuit.id DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)).parallel
    (resourceBankCircuit pairs resourceGateCounts resourceCircuits)
  |>.castCounts rfl (Nat.zero_add _) rfl

@[simp] theorem layerStateCircuit_eval_original
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (input : Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool) :
    originalInputFromState
        ((layerStateCircuit pairs resourceGateCounts resourceCircuits).eval
          DeMorgan.interpretation input) = input := by
  funext originalInput
  simp [originalInputFromState, layerStateCircuit]

theorem layerStateCircuit_eval_resource
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).Computes DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs))
    (input : Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool)
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    (layerStateCircuit pairs resourceGateCounts resourceCircuits).eval
        DeMorgan.interpretation input (resourceStateIndex resource pair) =
      resourceValue function input pair resource := by
  rw [layerStateCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, id_eq]
  rw [Circuit.eval_parallel]
  unfold resourceStateIndex
  rw [Fin.append_right]
  exact resourceBankCircuit_eval function pairs resourceGateCounts
    resourceCircuits computes input resource pair

/-- Decoding the completed layer state agrees with the semantic Uhlig
decoder. -/
theorem decodedStateValue_layerStateCircuit_eval
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).Computes DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs))
    (input : Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    decodedStateValue
        ((layerStateCircuit pairs resourceGateCounts resourceCircuits).eval
          DeMorgan.interpretation input)
        pair side =
      decodedValue function input pair side := by
  unfold decodedStateValue decodedValue
  rw [layerStateCircuit_eval_original pairs resourceGateCounts
    resourceCircuits input]
  unfold recoveryPair
  apply Finset.sum_congr rfl
  intro resource _member
  exact layerStateCircuit_eval_resource function pairs resourceGateCounts
    resourceCircuits computes input resource pair

/-- Quantitatively useful finite Uhlig layer, using circuit sharing inside
each XOR decoder. -/
noncomputable def sharedUhligLayerCircuit
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    Circuit DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          routedResourceGateCount prefixWidth suffixWidth pairs
            resourceGateCounts resource) +
        (Finset.univ.sum fun output : Fin (2 * pairs) =>
          sharedDecoderOutputGateCount
            prefixWidth suffixWidth pairs output))
      (2 * pairs) :=
  (sharedDecoderCircuit prefixWidth suffixWidth pairs).comp
    (layerStateCircuit pairs resourceGateCounts resourceCircuits)

/-- Exact correctness of the shared finite layer. -/
theorem sharedUhligLayerCircuit_computes
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).Computes DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs)) :
    (sharedUhligLayerCircuit pairs resourceGateCounts
      resourceCircuits).Computes DeMorgan.interpretation
        (directProduct function (2 * pairs)) := by
  intro input
  funext output
  rw [sharedUhligLayerCircuit, Circuit.eval_comp,
    sharedDecoderCircuit_eval]
  let pairSide := decoderPairSide output
  rw [decodedStateValue_layerStateCircuit_eval function pairs
    resourceGateCounts resourceCircuits computes input pairSide.1 pairSide.2]
  exact congrFun (decodedValue_eq_directProduct function input) output

/-- Exact cost ledger for the shared finite layer. -/
@[simp] theorem sharedUhligLayerCircuit_cost
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (sharedUhligLayerCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost)) +
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
            DeMorgan.standardCost) := by
  simp [sharedUhligLayerCircuit]
  simp [layerStateCircuit]

/-- Compose routing, supplied resource evaluation, and exact decoding. -/
noncomputable def uhligLayerCircuit
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    Circuit DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          routedResourceGateCount prefixWidth suffixWidth pairs
            resourceGateCounts resource) +
        (Finset.univ.sum fun output : Fin (2 * pairs) =>
          decoderGateCount prefixWidth suffixWidth pairs output))
      (2 * pairs) :=
  (decoderCircuit prefixWidth suffixWidth pairs).comp
    (layerStateCircuit pairs resourceGateCounts resourceCircuits)

/-- Exact finite Uhlig circuit theorem. If each resource function is
available on `pairs` independent suffixes, one explicit De Morgan circuit
computes `2 * pairs` independent copies of the original function. -/
theorem uhligLayerCircuit_computes
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).Computes DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs)) :
    (uhligLayerCircuit pairs resourceGateCounts resourceCircuits).Computes
      DeMorgan.interpretation (directProduct function (2 * pairs)) := by
  intro input
  funext output
  rw [uhligLayerCircuit, Circuit.eval_comp, decoderCircuit_eval]
  let pairSide := decoderPairSide output
  rw [decodedStateValue_layerStateCircuit_eval function pairs
    resourceGateCounts resourceCircuits computes input pairSide.1 pairSide.2]
  exact congrFun (decodedValue_eq_directProduct function input) output

@[simp] theorem layerStateCircuit_cost
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (layerStateCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost) := by
  simp [layerStateCircuit]

/-- Exact cost ledger for the complete finite layer. -/
@[simp] theorem uhligLayerCircuit_cost
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (uhligLayerCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost)) +
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        (decoderOutputExpression (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) output).standardCost) := by
  simp [uhligLayerCircuit]

/-! ## Polynomial overhead bounds for the shared layer -/

/-- Prefix-equality testing costs at most two gates per tested bit. -/
theorem sourceIndicatorExpression_standardCost_le
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    (sourceIndicatorExpression (suffixWidth := suffixWidth)
      side source).standardCost <= 2 * prefixWidth := by
  rw [sourceIndicatorExpression,
    DeMorgan.Expression.finAnd_standardCost]
  calc
    (Finset.univ.sum fun bit : Fin prefixWidth =>
        (ShannonSynthesis.matchingLiteral
          (localInputIndex side (Fin.castAdd suffixWidth bit))
          (InputSplit.sourceBits
            (Fin.cast (prefixCount_eq prefixWidth) source) bit)).standardCost) +
        prefixWidth <=
      (Finset.univ.sum fun _bit : Fin prefixWidth => 1) +
        prefixWidth := by
          gcongr with bit
          exact ShannonSynthesis.matchingLiteral_standardCost_le _ _
    _ = 2 * prefixWidth := by
      simp
      omega

theorem stateSourceIndicatorExpression_standardCost_le
    (pair : Fin pairs)
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
      pair side source).standardCost <= 2 * prefixWidth := by
  rw [stateSourceIndicatorExpression, reindexExpression_standardCost]
  exact sourceIndicatorExpression_standardCost_le
    (suffixWidth := suffixWidth) side source

@[simp] theorem fixedRoutedSuffixExpression_standardCost
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    (fixedRoutedSuffixExpression first second resource bit).standardCost =
      0 := by
  unfold fixedRoutedSuffixExpression
  split
  · rfl
  · split <;> rfl

@[simp] theorem resourceRouterCircuit_cost
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun bit : Fin suffixWidth =>
        (routedSuffixExpression resource bit).standardCost := by
  simp [resourceRouterCircuit]

/-- A direct polynomial bound for one routed suffix bit. -/
def routedSuffixCostBound (prefixWidth : Nat) : Nat :=
  let sources := prefixLast prefixWidth + 1
  sources *
      (2 * prefixWidth +
        (sources * (2 * prefixWidth + 1) + sources) + 1) +
    sources

theorem routedSuffixExpression_standardCost_le
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    (routedSuffixExpression resource bit).standardCost <=
      routedSuffixCostBound prefixWidth := by
  let sources := prefixLast prefixWidth + 1
  have innerBound (first : Fin (prefixLast prefixWidth + 1)) :
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun second =>
        .and (sourceIndicatorExpression
            (suffixWidth := suffixWidth) 1 second)
          (fixedRoutedSuffixExpression first second resource bit)).standardCost <=
        sources * (2 * prefixWidth + 1) + sources := by
    rw [DeMorgan.Expression.finOr_standardCost]
    calc
      (Finset.univ.sum fun second : Fin (prefixLast prefixWidth + 1) =>
          (DeMorgan.Expression.and
            (sourceIndicatorExpression
              (suffixWidth := suffixWidth) 1 second)
            (fixedRoutedSuffixExpression first second resource bit)).standardCost) +
          (prefixLast prefixWidth + 1) <=
        (Finset.univ.sum fun _second :
            Fin (prefixLast prefixWidth + 1) =>
          2 * prefixWidth + 1) +
          (prefixLast prefixWidth + 1) := by
            gcongr with second
            simp only [DeMorgan.Expression.standardCost,
              fixedRoutedSuffixExpression_standardCost]
            have indicatorBound :=
              sourceIndicatorExpression_standardCost_le
                (suffixWidth := suffixWidth) 1 second
            omega
      _ = sources * (2 * prefixWidth + 1) + sources := by
        simp [sources]
  rw [routedSuffixExpression,
    DeMorgan.Expression.finOr_standardCost]
  calc
    (Finset.univ.sum fun first : Fin (prefixLast prefixWidth + 1) =>
        (DeMorgan.Expression.and
          (sourceIndicatorExpression (suffixWidth := suffixWidth) 0 first)
          (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1)
            fun second =>
              .and (sourceIndicatorExpression
                  (suffixWidth := suffixWidth) 1 second)
                (fixedRoutedSuffixExpression first second resource bit))).standardCost) +
        (prefixLast prefixWidth + 1) <=
      (Finset.univ.sum fun _first : Fin (prefixLast prefixWidth + 1) =>
        2 * prefixWidth +
          (sources * (2 * prefixWidth + 1) + sources) + 1) +
        (prefixLast prefixWidth + 1) := by
          gcongr with first
          simp only [DeMorgan.Expression.standardCost]
          have indicatorBound :=
            sourceIndicatorExpression_standardCost_le
              (suffixWidth := suffixWidth) 0 first
          have nestedBound := innerBound first
          omega
    _ = routedSuffixCostBound prefixWidth := by
      simp [routedSuffixCostBound, sources]

theorem resourceRouterCircuit_cost_le
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
        DeMorgan.standardCost <=
      suffixWidth * routedSuffixCostBound prefixWidth := by
  rw [resourceRouterCircuit_cost]
  calc
    (Finset.univ.sum fun bit : Fin suffixWidth =>
      (routedSuffixExpression resource bit).standardCost) <=
        Finset.univ.sum fun _bit : Fin suffixWidth =>
          routedSuffixCostBound prefixWidth := by
            gcongr with bit
            exact routedSuffixExpression_standardCost_le
              (suffixWidth := suffixWidth) resource bit
    _ = suffixWidth * routedSuffixCostBound prefixWidth := by simp

theorem candidatePostprocessExpression_cost :
    candidatePostprocessExpression.circuit.cost DeMorgan.standardCost = 2 := by
  rfl

/-- Uniform charged cost bound for one hardwired source-pair candidate. -/
def candidateDecodedCostBound (prefixWidth : Nat) : Nat :=
  4 * prefixWidth + 4 * (prefixLast prefixWidth + 2) + 2

theorem candidateDecodedCircuit_cost_le
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    (candidateDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).cost DeMorgan.standardCost <=
      candidateDecodedCostBound prefixWidth := by
  change
    (candidatePostprocessExpression.circuit.comp
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).circuit.parallel
        ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 1 second).circuit.parallel
          (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
            pair side first second)))).cost DeMorgan.standardCost <= _
  rw [Circuit.cost_comp, Circuit.cost_parallel, Circuit.cost_parallel,
    DeMorgan.Expression.circuit_cost,
    DeMorgan.Expression.circuit_cost,
    sharedFixedDecodedCircuit_cost,
    candidatePostprocessExpression_cost]
  have firstBound := stateSourceIndicatorExpression_standardCost_le
    (suffixWidth := suffixWidth) pair 0 first
  have secondBound := stateSourceIndicatorExpression_standardCost_le
    (suffixWidth := suffixWidth) pair 1 second
  unfold candidateDecodedCostBound
  omega

/-- Uniform row cost after OR-ing over the second source. -/
def candidateRowCostBound (prefixWidth : Nat) : Nat :=
  (prefixLast prefixWidth + 1) *
      candidateDecodedCostBound prefixWidth +
    (prefixLast prefixWidth + 1)

theorem candidateRowCircuit_cost_le
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1)) :
    (candidateRowCircuit (suffixWidth := suffixWidth)
      pair side first).cost DeMorgan.standardCost <=
      candidateRowCostBound prefixWidth := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun second => candidateDecodedGateCount
          prefixWidth suffixWidth pairs pair side first second)
        (fun second =>
          candidateDecodedCircuit pair side first second))).cost
        DeMorgan.standardCost <= _
  rw [Circuit.cost_comp, Circuit.cost_parallelFin, orInputCircuit_cost]
  calc
    (Finset.univ.sum fun second : Fin (prefixLast prefixWidth + 1) =>
        (candidateDecodedCircuit (suffixWidth := suffixWidth)
          pair side first second).cost DeMorgan.standardCost) +
        (prefixLast prefixWidth + 1) <=
      (Finset.univ.sum fun _second : Fin (prefixLast prefixWidth + 1) =>
        candidateDecodedCostBound prefixWidth) +
        (prefixLast prefixWidth + 1) := by
          gcongr with second
          exact candidateDecodedCircuit_cost_le
            (suffixWidth := suffixWidth) pair side first second
    _ = candidateRowCostBound prefixWidth := by
      simp [candidateRowCostBound]

/-- Uniform charged cost bound for one requested-output decoder. -/
def sharedDecodedCostBound (prefixWidth : Nat) : Nat :=
  (prefixLast prefixWidth + 1) * candidateRowCostBound prefixWidth +
    (prefixLast prefixWidth + 1)

theorem sharedDecodedCircuit_cost_le
    (pair : Fin pairs) (side : Fin 2) :
    (sharedDecodedCircuit (prefixWidth := prefixWidth)
      (suffixWidth := suffixWidth) pair side).cost DeMorgan.standardCost <=
      sharedDecodedCostBound prefixWidth := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun first => candidateRowGateCount
          prefixWidth suffixWidth pairs pair side first)
        (fun first => candidateRowCircuit pair side first))).cost
        DeMorgan.standardCost <= _
  rw [Circuit.cost_comp, Circuit.cost_parallelFin, orInputCircuit_cost]
  calc
    (Finset.univ.sum fun first : Fin (prefixLast prefixWidth + 1) =>
        (candidateRowCircuit (suffixWidth := suffixWidth)
          pair side first).cost DeMorgan.standardCost) +
        (prefixLast prefixWidth + 1) <=
      (Finset.univ.sum fun _first : Fin (prefixLast prefixWidth + 1) =>
        candidateRowCostBound prefixWidth) +
        (prefixLast prefixWidth + 1) := by
          gcongr with first
          exact candidateRowCircuit_cost_le
            (suffixWidth := suffixWidth) pair side first
    _ = sharedDecodedCostBound prefixWidth := by
      simp [sharedDecodedCostBound]

theorem sharedDecoderCircuit_cost_le
    (prefixWidth suffixWidth pairs : Nat) :
    (sharedDecoderCircuit prefixWidth suffixWidth pairs).cost
        DeMorgan.standardCost <=
      (2 * pairs) * sharedDecodedCostBound prefixWidth := by
  rw [sharedDecoderCircuit_cost]
  calc
    (Finset.univ.sum fun output : Fin (2 * pairs) =>
      let pairSide := decoderPairSide output
      (sharedDecodedCircuit (prefixWidth := prefixWidth)
        (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
          DeMorgan.standardCost) <=
        Finset.univ.sum fun _output : Fin (2 * pairs) =>
          sharedDecodedCostBound prefixWidth := by
            gcongr with output
            exact sharedDecodedCircuit_cost_le
              (suffixWidth := suffixWidth)
              (decoderPairSide output).1 (decoderPairSide output).2
    _ = (2 * pairs) * sharedDecodedCostBound prefixWidth := by simp

/-- Uniform routing cost across all resources and request pairs. -/
theorem resourceRoutingBankCost_le
    (prefixWidth suffixWidth pairs : Nat) :
    (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
      Finset.univ.sum fun _pair : Fin pairs =>
        (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
          DeMorgan.standardCost) <=
      (prefixLast prefixWidth + 2) *
        (pairs * (suffixWidth * routedSuffixCostBound prefixWidth)) := by
  calc
    (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
      Finset.univ.sum fun _pair : Fin pairs =>
        (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
          DeMorgan.standardCost) <=
      Finset.univ.sum fun _resource : Fin (prefixLast prefixWidth + 2) =>
        pairs * (suffixWidth * routedSuffixCostBound prefixWidth) := by
          gcongr with resource
          calc
            (Finset.univ.sum fun _pair : Fin pairs =>
              (resourceRouterCircuit (suffixWidth := suffixWidth)
                resource).cost DeMorgan.standardCost) =
                pairs *
                  (resourceRouterCircuit (suffixWidth := suffixWidth)
                    resource).cost DeMorgan.standardCost := by simp
            _ <= pairs *
                (suffixWidth * routedSuffixCostBound prefixWidth) := by
              gcongr
              exact resourceRouterCircuit_cost_le
                (suffixWidth := suffixWidth) resource
    _ = (prefixLast prefixWidth + 2) *
        (pairs * (suffixWidth * routedSuffixCostBound prefixWidth)) := by simp

/-- Polynomial overhead added by one shared Uhlig layer. -/
def sharedLayerOverheadBound
    (prefixWidth suffixWidth pairs : Nat) : Nat :=
  (prefixLast prefixWidth + 2) *
      (pairs * (suffixWidth * routedSuffixCostBound prefixWidth)) +
    (2 * pairs) * sharedDecodedCostBound prefixWidth

/-- The shared finite layer costs the sum of its recursive resource circuits
plus an explicit polynomial overhead. -/
theorem sharedUhligLayerCircuit_cost_le_resource_sum_add_overhead
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (sharedUhligLayerCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost <=
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        (resourceCircuits resource).cost DeMorgan.standardCost) +
      sharedLayerOverheadBound prefixWidth suffixWidth pairs := by
  rw [sharedUhligLayerCircuit_cost]
  rw [Finset.sum_add_distrib]
  have routingBound := resourceRoutingBankCost_le
    prefixWidth suffixWidth pairs
  have decoderBound :
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
            DeMorgan.standardCost) <=
        (2 * pairs) * sharedDecodedCostBound prefixWidth := by
    rw [← sharedDecoderCircuit_cost]
    exact sharedDecoderCircuit_cost_le prefixWidth suffixWidth pairs
  unfold sharedLayerOverheadBound
  omega

end UhligCircuit
end MassProduction
end Algebraic
