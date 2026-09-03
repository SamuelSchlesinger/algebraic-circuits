import Algebraic.Basis.DeMorgan.Expression
import Algebraic.MassProduction.Statement
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Log

/-!
# Native Shannon synthesis

This module gives an Algebraic-native version of the finite synthesis
construction used as the base case of the mass-production induction.  It
uses a shared circuit for all minterms, followed by a shared library of all
Boolean functions on a short address block.  No external circuit model and
no new type-class instances are used.
-/

namespace Algebraic
namespace MassProduction
namespace ShannonSynthesis

open scoped BigOperators

/-- Canonical finite index of a Boolean vector. -/
noncomputable def bitVectorEquiv (width : Nat) :
    (Fin width -> Bool) ≃ Fin (2 ^ width) :=
  (Equiv.piCongrRight
      (fun _ : Fin width => finTwoEquiv.symm)).trans
    finFunctionFinEquiv

/-- Decode a canonical finite index back to its Boolean vector. -/
noncomputable def assignmentBits
    (width : Nat) (assignment : Fin (2 ^ width)) : Fin width -> Bool :=
  (bitVectorEquiv width).symm assignment

@[simp] theorem bitVectorEquiv_assignmentBits
    (assignment : Fin (2 ^ width)) :
    bitVectorEquiv width (assignmentBits width assignment) = assignment := by
  exact (bitVectorEquiv width).apply_symm_apply assignment

@[simp] theorem assignmentBits_bitVectorEquiv
    (input : Fin width -> Bool) :
    assignmentBits width (bitVectorEquiv width input) = input := by
  exact (bitVectorEquiv width).symm_apply_apply input

/-- A positive or negative occurrence of one input, according to the
expected Boolean value. -/
def matchingLiteral
    (index : Fin inputs) (expected : Bool) : DeMorgan.Expression inputs :=
  if expected then .input index else .not (.input index)

@[simp] theorem matchingLiteral_eval
    (index : Fin inputs)
    (expected : Bool)
    (input : Fin inputs -> Bool) :
    (matchingLiteral index expected).eval input =
      decide (input index = expected) := by
  cases actualEquation : input index <;> cases expected <;>
    simp [matchingLiteral, DeMorgan.Expression.eval, actualEquation]

theorem matchingLiteral_standardCost_le
    (index : Fin inputs) (expected : Bool) :
    (matchingLiteral index expected).standardCost <= 1 := by
  cases expected <;> simp [matchingLiteral,
    DeMorgan.Expression.standardCost]

/-- Index in the retained-state vector of a minterm from the previous
dimension. -/
def previousMintermInput
    (assignment : Fin (2 ^ width)) : Fin (2 ^ width + 1) :=
  Fin.castAdd 1 assignment

/-- Index in the retained-state vector of the newly prepended input bit. -/
def newHeadInput (width : Nat) : Fin (2 ^ width + 1) :=
  Fin.last (2 ^ width)

/-- The previous-dimension assignment required by a full assignment. -/
noncomputable def assignmentTailIndex
    (width : Nat) (assignment : Fin (2 ^ (width + 1))) : Fin (2 ^ width) :=
  bitVectorEquiv width (Fin.tail (assignmentBits (width + 1) assignment))

/-- One output of the layer which extends all `width`-bit minterms by one
new head bit. -/
noncomputable def extensionExpression
    (width : Nat) (assignment : Fin (2 ^ (width + 1))) :
    DeMorgan.Expression (2 ^ width + 1) :=
  .and (.input (previousMintermInput (assignmentTailIndex width assignment)))
    (matchingLiteral (newHeadInput width)
      (assignmentBits (width + 1) assignment 0))

/-- Program-gate count of one full minterm-extension layer. -/
@[reducible] noncomputable def extensionGateCount (width : Nat) : Nat :=
  ∑ assignment : Fin (2 ^ (width + 1)),
    (extensionExpression width assignment).gateCount

/-- Compute all extended minterms in parallel. -/
noncomputable def extensionCircuit (width : Nat) :
    Circuit DeMorgan.signature (2 ^ width + 1)
      (extensionGateCount width) (2 ^ (width + 1)) :=
  Circuit.parallelFin (2 ^ (width + 1))
    (fun assignment => (extensionExpression width assignment).gateCount)
    (fun assignment => (extensionExpression width assignment).circuit)

@[simp] theorem extensionCircuit_eval
    (state : Fin (2 ^ width + 1) -> Bool)
    (assignment : Fin (2 ^ (width + 1))) :
    (extensionCircuit width).eval DeMorgan.interpretation state assignment =
      (state (previousMintermInput (assignmentTailIndex width assignment)) &&
        decide (state (newHeadInput width) =
          assignmentBits (width + 1) assignment 0)) := by
  unfold extensionCircuit extensionGateCount
  rw [Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  simp [extensionExpression, DeMorgan.Expression.eval]

theorem extensionCircuit_cost_le (width : Nat) :
    (extensionCircuit width).cost DeMorgan.standardCost <=
      2 * 2 ^ (width + 1) := by
  unfold extensionCircuit extensionGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ assignment : Fin (2 ^ (width + 1)),
        (extensionExpression width assignment).circuit.cost
          DeMorgan.standardCost) =
        ∑ assignment : Fin (2 ^ (width + 1)),
          (extensionExpression width assignment).standardCost := by
            apply Finset.sum_congr rfl
            intro assignment _membership
            rw [DeMorgan.Expression.circuit_cost]
    _ <= ∑ _assignment : Fin (2 ^ (width + 1)), 2 := by
      apply Finset.sum_le_sum
      intro assignment _membership
      simp only [extensionExpression, DeMorgan.Expression.standardCost]
      simpa [Nat.zero_add] using
        Nat.add_le_add_right (matchingLiteral_standardCost_le
          (newHeadInput width)
          (assignmentBits (width + 1) assignment 0)) 1
    _ = 2 * 2 ^ (width + 1) := by simp [Nat.mul_comm]

/-- Program-gate count of the shared all-minterms circuit. -/
@[reducible] noncomputable def mintermGateCount : Nat -> Nat
  | 0 => 1
  | width + 1 => mintermGateCount width + extensionGateCount width

/-- A shared circuit computing the indicator of every Boolean assignment.
The recursive layer prepends the new input bit, matching `Fin.cons`. -/
noncomputable def mintermCircuit : (width : Nat) ->
    Circuit DeMorgan.signature width (mintermGateCount width) (2 ^ width)
  | 0 => (DeMorgan.Expression.constant true).circuit
  | width + 1 =>
      let previous :=
        (mintermCircuit width).mapInputs (fun index => index.succ)
      let head :=
        (Circuit.id DeMorgan.signature (width + 1)).mapOutputs
          (fun _ : Fin 1 => (0 : Fin (width + 1)))
      let state := (previous.parallel head).castCounts rfl
        (Nat.add_zero _) rfl
      (extensionCircuit width).comp state

/-- Equality with a decoded assignment is exactly equality of the head bit
and equality of the encoded tail. -/
theorem assignment_eq_iff_head_tail
    (input : Fin (width + 1) -> Bool)
    (assignment : Fin (2 ^ (width + 1))) :
    bitVectorEquiv (width + 1) input = assignment ↔
      bitVectorEquiv width (Fin.tail input) =
          assignmentTailIndex width assignment ∧
        input 0 = assignmentBits (width + 1) assignment 0 := by
  rw [← (bitVectorEquiv (width + 1)).eq_symm_apply]
  constructor
  · intro inputEquality
    subst input
    exact ⟨rfl, rfl⟩
  · rintro ⟨tailEquality, headEquality⟩
    let decoded := assignmentBits (width + 1) assignment
    have tails : Fin.tail input = Fin.tail decoded := by
      apply (bitVectorEquiv width).injective
      simpa only [assignmentTailIndex, decoded]
        using tailEquality
    calc
      input = Fin.cons (input 0) (Fin.tail input) :=
        (Fin.cons_self_tail input).symm
      _ = Fin.cons (decoded 0) (Fin.tail decoded) := by
        rw [headEquality, tails]
      _ = decoded := Fin.cons_self_tail decoded

/-- The Boolean conjunction used by an extension layer is the indicator of
the represented full assignment. -/
theorem assignmentIndicator_extension
    (input : Fin (width + 1) -> Bool)
    (assignment : Fin (2 ^ (width + 1))) :
    (decide (bitVectorEquiv width (Fin.tail input) =
          assignmentTailIndex width assignment) &&
        decide (input 0 = assignmentBits (width + 1) assignment 0)) =
      decide (bitVectorEquiv (width + 1) input = assignment) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact (assignment_eq_iff_head_tail input assignment).symm

/-- Every output of the shared minterm circuit is the exact indicator of its
canonical Boolean assignment. -/
@[simp] theorem mintermCircuit_eval
    (width : Nat)
    (input : Fin width -> Bool)
    (assignment : Fin (2 ^ width)) :
    (mintermCircuit width).eval DeMorgan.interpretation input assignment =
      decide (bitVectorEquiv width input = assignment) := by
  induction width with
  | zero =>
      have inputUnique : input = fun index => Fin.elim0 index := by
        funext index
        exact Fin.elim0 index
      have assignmentUnique : assignment = 0 := by
        apply Fin.ext
        omega
      subst input
      subst assignment
      simp only [mintermCircuit]
      rw [DeMorgan.Expression.circuit_eval]
      change true = decide (bitVectorEquiv 0 (fun index => Fin.elim0 index) = 0)
      rw [show bitVectorEquiv 0 (fun index => Fin.elim0 index) = 0 by
        apply Fin.ext
        omega]
      rfl
  | succ width inductionHypothesis =>
      rw [mintermCircuit, Circuit.eval_comp, extensionCircuit_eval]
      simp only [Circuit.eval_castCounts, Fin.cast_refl, Function.comp_id,
        Circuit.eval_parallel, id_eq]
      rw [show previousMintermInput
            (assignmentTailIndex width assignment) =
          Fin.castAdd 1 (assignmentTailIndex width assignment) by rfl,
        Fin.append_left, Circuit.eval_mapInputs, inductionHypothesis]
      rw [show newHeadInput width = Fin.natAdd (2 ^ width) (0 : Fin 1) by
        apply Fin.ext
        simp [newHeadInput], Fin.append_right,
        Circuit.eval_mapOutputs, Function.comp_apply, Circuit.eval_id]
      exact assignmentIndicator_extension input assignment

/-- The complete shared minterm table costs at most four gates per Boolean
assignment. -/
theorem mintermCircuit_cost_le (width : Nat) :
    (mintermCircuit width).cost DeMorgan.standardCost <= 4 * 2 ^ width := by
  induction width with
  | zero =>
      simp only [mintermCircuit]
      rw [DeMorgan.Expression.circuit_cost]
      exact Nat.zero_le _
  | succ width inductionHypothesis =>
      rw [mintermCircuit, Circuit.cost_comp, Circuit.cost_castCounts,
        Circuit.cost_parallel, Circuit.cost_mapInputs,
        Circuit.cost_mapOutputs, Circuit.cost_id]
      have layerBound := extensionCircuit_cost_le width
      simp only [Nat.add_zero]
      have powerSucc : 2 ^ (width + 1) = 2 ^ width * 2 := by
        rw [Nat.pow_succ]
      omega

/-! ## The shared library of short-address Boolean functions -/

/-- One hardwired term in the truth-table disjunction for a short-address
function. -/
noncomputable def columnTerm
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth)))
    (assignment : Fin (2 ^ addressWidth)) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  if assignmentBits (2 ^ addressWidth) pattern assignment then
    .input assignment
  else
    .constant false

/-- The truth-table formula for one Boolean function of the address block,
evaluated on a one-hot vector of address minterms. -/
noncomputable def columnExpression
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  DeMorgan.Expression.finOr (2 ^ addressWidth)
    (columnTerm addressWidth pattern)

@[simp] theorem columnTerm_standardCost
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth)))
    (assignment : Fin (2 ^ addressWidth)) :
    (columnTerm addressWidth pattern assignment).standardCost = 0 := by
  unfold columnTerm
  split <;> rfl

theorem columnExpression_standardCost
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    (columnExpression addressWidth pattern).standardCost =
      2 ^ addressWidth := by
  rw [columnExpression, DeMorgan.Expression.finOr_standardCost]
  simp

/-- A hardwired column formula reads the truth-table bit selected by a
one-hot minterm vector. -/
theorem columnExpression_eval_oneHot
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth)))
    (flags : Fin (2 ^ addressWidth) -> Bool)
    (selected : Fin (2 ^ addressWidth))
    (selectedTrue : flags selected = true)
    (unique : forall assignment, flags assignment = true ->
      assignment = selected) :
    (columnExpression addressWidth pattern).eval flags =
      assignmentBits (2 ^ addressWidth) pattern selected := by
  rw [columnExpression, DeMorgan.Expression.finOr_eval]
  have termsEqual :
      (fun assignment =>
          (columnTerm addressWidth pattern assignment).eval flags) =
        (fun assignment => flags assignment &&
          assignmentBits (2 ^ addressWidth) pattern assignment) := by
    funext assignment
    unfold columnTerm
    cases bitEquation : assignmentBits (2 ^ addressWidth) pattern assignment <;>
      simp [DeMorgan.Expression.eval]
  rw [termsEqual]
  exact DeMorgan.Expression.finOrValue_oneHot
    (2 ^ addressWidth) selected flags
    (assignmentBits (2 ^ addressWidth) pattern)
    selectedTrue unique

/-- Program-gate count of the complete short-address function library. -/
@[reducible] noncomputable def libraryGateCount (addressWidth : Nat) : Nat :=
  ∑ pattern : Fin (2 ^ (2 ^ addressWidth)),
    (columnExpression addressWidth pattern).gateCount

/-- All Boolean functions of `addressWidth` inputs, sharing the same address
minterm vector. -/
noncomputable def libraryCircuit (addressWidth : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth)
      (libraryGateCount addressWidth) (2 ^ (2 ^ addressWidth)) :=
  Circuit.parallelFin (2 ^ (2 ^ addressWidth))
    (fun pattern => (columnExpression addressWidth pattern).gateCount)
    (fun pattern => (columnExpression addressWidth pattern).circuit)

@[simp] theorem libraryCircuit_eval
    (addressWidth : Nat)
    (flags : Fin (2 ^ addressWidth) -> Bool)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    (libraryCircuit addressWidth).eval DeMorgan.interpretation flags pattern =
      (columnExpression addressWidth pattern).eval flags := by
  unfold libraryCircuit libraryGateCount
  rw [Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]

theorem libraryCircuit_cost
    (addressWidth : Nat) :
    (libraryCircuit addressWidth).cost DeMorgan.standardCost =
      2 ^ (2 ^ addressWidth) * 2 ^ addressWidth := by
  unfold libraryCircuit libraryGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ pattern : Fin (2 ^ (2 ^ addressWidth)),
        (columnExpression addressWidth pattern).circuit.cost
          DeMorgan.standardCost) =
        ∑ pattern : Fin (2 ^ (2 ^ addressWidth)),
          (columnExpression addressWidth pattern).standardCost := by
            apply Finset.sum_congr rfl
            intro pattern _membership
            rw [DeMorgan.Expression.circuit_cost]
    _ = 2 ^ (2 ^ addressWidth) * 2 ^ addressWidth := by
      simp [columnExpression_standardCost]

/-- Composing the library after the shared minterm circuit evaluates the
canonical truth-table bit of the input address. -/
theorem library_after_minterms_eval
    (addressWidth : Nat)
    (input : Fin addressWidth -> Bool)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    (libraryCircuit addressWidth).eval DeMorgan.interpretation
        ((mintermCircuit addressWidth).eval DeMorgan.interpretation input)
        pattern =
      assignmentBits (2 ^ addressWidth) pattern
        (bitVectorEquiv addressWidth input) := by
  rw [libraryCircuit_eval]
  apply columnExpression_eval_oneHot addressWidth pattern
  · rw [mintermCircuit_eval]
    simp
  · intro assignment assignmentTrue
    rw [mintermCircuit_eval] at assignmentTrue
    simpa using (of_decide_eq_true assignmentTrue).symm

/-! ## Synthesis of an arbitrary split-input Boolean function -/

/-- The initial address block of a split input. -/
def addressInput
    (dataWidth : Nat)
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin addressWidth -> Bool :=
  input ∘ Fin.castAdd dataWidth

/-- The final data block of a split input. -/
def dataInput
    (addressWidth : Nat)
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin dataWidth -> Bool :=
  input ∘ Fin.natAdd addressWidth

theorem append_addressInput_dataInput
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin.append (addressInput dataWidth input)
        (dataInput addressWidth input) = input := by
  funext index
  refine Fin.addCases (fun address => ?_) (fun data => ?_) index
  · simp [addressInput]
  · simp [dataInput]

/-- Gate count of the two shared minterm tables. -/
@[reducible] noncomputable def splitMintermGateCount
    (addressWidth dataWidth : Nat) : Nat :=
  mintermGateCount addressWidth + mintermGateCount dataWidth

/-- Compute all address and all data minterms in parallel. -/
noncomputable def splitMintermCircuit
    (addressWidth dataWidth : Nat) :
    Circuit DeMorgan.signature (addressWidth + dataWidth)
      (splitMintermGateCount addressWidth dataWidth)
      (2 ^ addressWidth + 2 ^ dataWidth) :=
  ((mintermCircuit addressWidth).mapInputs (Fin.castAdd dataWidth)).parallel
    ((mintermCircuit dataWidth).mapInputs (Fin.natAdd addressWidth))

@[simp] theorem splitMintermCircuit_eval
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    (splitMintermCircuit addressWidth dataWidth).eval
        DeMorgan.interpretation input =
      Fin.append
        ((mintermCircuit addressWidth).eval DeMorgan.interpretation
          (addressInput dataWidth input))
        ((mintermCircuit dataWidth).eval DeMorgan.interpretation
          (dataInput addressWidth input)) := by
  rw [splitMintermCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_mapInputs]
  rfl

/-- Gate count of the library stage, whose retained data minterms are free
wires. -/
@[reducible] noncomputable def libraryAndDataGateCount
    (addressWidth : Nat) : Nat :=
  libraryGateCount addressWidth

/-- Evaluate the complete address library while retaining every data
minterm. -/
noncomputable def libraryAndDataCircuit
    (addressWidth dataWidth : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (libraryAndDataGateCount addressWidth)
      (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  (((libraryCircuit addressWidth).mapInputs
      (Fin.castAdd (2 ^ dataWidth))).parallel
    ((Circuit.id DeMorgan.signature
        (2 ^ addressWidth + 2 ^ dataWidth)).mapOutputs
      (Fin.natAdd (2 ^ addressWidth)))).castCounts rfl
        (Nat.add_zero _) rfl

@[simp] theorem libraryAndDataCircuit_eval
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool) :
    (libraryAndDataCircuit addressWidth dataWidth).eval
        DeMorgan.interpretation state =
      Fin.append
        ((libraryCircuit addressWidth).eval DeMorgan.interpretation
          (fun assignment => state (Fin.castAdd (2 ^ dataWidth) assignment)))
        (fun assignment =>
          state (Fin.natAdd (2 ^ addressWidth) assignment)) := by
  rw [libraryAndDataCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_mapOutputs, Circuit.eval_id,
    id_eq]
  rfl

/-- The address truth-table column required when the data block has one
fixed assignment. -/
noncomputable def columnPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (dataAssignment : Fin (2 ^ dataWidth)) :
    Fin (2 ^ (2 ^ addressWidth)) :=
  bitVectorEquiv (2 ^ addressWidth) fun addressAssignment =>
    function (Fin.append
      (assignmentBits addressWidth addressAssignment)
      (assignmentBits dataWidth dataAssignment))

@[simp] theorem assignmentBits_columnPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (dataAssignment : Fin (2 ^ dataWidth))
    (addressAssignment : Fin (2 ^ addressWidth)) :
    assignmentBits (2 ^ addressWidth)
        (columnPattern function dataAssignment) addressAssignment =
      function (Fin.append
        (assignmentBits addressWidth addressAssignment)
        (assignmentBits dataWidth dataAssignment)) := by
  unfold columnPattern
  rw [assignmentBits_bitVectorEquiv]

/-- Input coordinate of a precomputed address-column value. -/
def columnInput
    (dataWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    Fin (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  Fin.castAdd (2 ^ dataWidth) pattern

/-- Input coordinate of a retained data minterm. -/
def dataMintermInput
    (addressWidth : Nat)
    (assignment : Fin (2 ^ dataWidth)) :
    Fin (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  Fin.natAdd (2 ^ (2 ^ addressWidth)) assignment

/-- Combine one retained data minterm with the corresponding hardwired
address-function column. -/
noncomputable def rowExpression
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (dataAssignment : Fin (2 ^ dataWidth)) :
    DeMorgan.Expression (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  .and (.input (dataMintermInput addressWidth dataAssignment))
    (.input (columnInput dataWidth (columnPattern function dataAssignment)))

/-- OR the row terms to obtain the synthesized function. -/
noncomputable def synthesisExpression
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    DeMorgan.Expression (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  DeMorgan.Expression.finOr (2 ^ dataWidth) (rowExpression function)

theorem synthesisExpression_standardCost
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    (synthesisExpression function).standardCost = 2 * 2 ^ dataWidth := by
  rw [synthesisExpression, DeMorgan.Expression.finOr_standardCost]
  simp [rowExpression, DeMorgan.Expression.standardCost]
  omega

/-- Program-gate count of the complete native Shannon circuit. -/
@[reducible] noncomputable def synthesisGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth)) : Nat :=
  splitMintermGateCount addressWidth dataWidth +
    libraryAndDataGateCount addressWidth +
      (synthesisExpression function).gateCount

/-- Algebraic-native Shannon synthesis with a caller-selected address/data
split. -/
noncomputable def circuit
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    Circuit DeMorgan.signature (addressWidth + dataWidth)
      (synthesisGateCount function) 1 :=
  (synthesisExpression function).circuit.comp
    ((libraryAndDataCircuit addressWidth dataWidth).comp
      (splitMintermCircuit addressWidth dataWidth))

/-- Intermediate values after both minterm tables and the address-function
library have been evaluated. -/
noncomputable def libraryState
    (addressWidth dataWidth : Nat)
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) -> Bool :=
  (libraryAndDataCircuit addressWidth dataWidth).eval
    DeMorgan.interpretation
    ((splitMintermCircuit addressWidth dataWidth).eval
      DeMorgan.interpretation input)

@[simp] theorem libraryState_column
    (input : Fin (addressWidth + dataWidth) -> Bool)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    libraryState addressWidth dataWidth input
        (columnInput dataWidth pattern) =
      assignmentBits (2 ^ addressWidth) pattern
        (bitVectorEquiv addressWidth (addressInput dataWidth input)) := by
  rw [libraryState, libraryAndDataCircuit_eval]
  unfold columnInput
  rw [Fin.append_left, splitMintermCircuit_eval]
  simp only [Fin.append_left]
  exact library_after_minterms_eval addressWidth
    (addressInput dataWidth input) pattern

@[simp] theorem libraryState_dataMinterm
    (input : Fin (addressWidth + dataWidth) -> Bool)
    (assignment : Fin (2 ^ dataWidth)) :
    libraryState addressWidth dataWidth input
        (dataMintermInput addressWidth assignment) =
      decide (bitVectorEquiv dataWidth (dataInput addressWidth input) =
        assignment) := by
  rw [libraryState, libraryAndDataCircuit_eval]
  unfold dataMintermInput
  rw [Fin.append_right, splitMintermCircuit_eval]
  simp only [Fin.append_right]
  exact mintermCircuit_eval dataWidth (dataInput addressWidth input)
    assignment

@[simp] theorem rowExpression_eval_libraryState
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (input : Fin (addressWidth + dataWidth) -> Bool)
    (dataAssignment : Fin (2 ^ dataWidth)) :
    (rowExpression function dataAssignment).eval
        (libraryState addressWidth dataWidth input) =
      (decide (bitVectorEquiv dataWidth (dataInput addressWidth input) =
          dataAssignment) &&
        function (Fin.append (addressInput dataWidth input)
          (assignmentBits dataWidth dataAssignment))) := by
  unfold rowExpression
  simp only [DeMorgan.Expression.eval, libraryState_dataMinterm,
    libraryState_column, assignmentBits_columnPattern,
    assignmentBits_bitVectorEquiv]

/-- The native Shannon circuit computes the supplied Boolean function. -/
theorem circuit_eval
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    (circuit function).eval DeMorgan.interpretation input 0 =
      function input := by
  rw [circuit, Circuit.eval_comp, Circuit.eval_comp,
    DeMorgan.Expression.circuit_eval]
  change (synthesisExpression function).eval
      (libraryState addressWidth dataWidth input) = function input
  rw [synthesisExpression, DeMorgan.Expression.finOr_eval]
  have rowValues :
      (fun dataAssignment =>
          (rowExpression function dataAssignment).eval
            (libraryState addressWidth dataWidth input)) =
        (fun dataAssignment =>
          decide (bitVectorEquiv dataWidth (dataInput addressWidth input) =
              dataAssignment) &&
            function (Fin.append (addressInput dataWidth input)
              (assignmentBits dataWidth dataAssignment))) := by
    funext dataAssignment
    exact rowExpression_eval_libraryState function input dataAssignment
  rw [rowValues]
  let selected := bitVectorEquiv dataWidth (dataInput addressWidth input)
  rw [DeMorgan.Expression.finOrValue_oneHot (2 ^ dataWidth) selected
    (fun dataAssignment => decide (selected = dataAssignment))
    (fun dataAssignment =>
      function (Fin.append (addressInput dataWidth input)
        (assignmentBits dataWidth dataAssignment)))]
  · rw [show assignmentBits dataWidth selected =
        dataInput addressWidth input by
      exact assignmentBits_bitVectorEquiv (dataInput addressWidth input)]
    rw [append_addressInput_dataInput]
  · simp
  · intro dataAssignment assignmentTrue
    exact (of_decide_eq_true assignmentTrue).symm

/-- Explicit cost ledger for the split synthesis construction. -/
@[reducible] def costBound (addressWidth dataWidth : Nat) : Nat :=
  4 * 2 ^ addressWidth + 4 * 2 ^ dataWidth +
    2 ^ (2 ^ addressWidth) * 2 ^ addressWidth +
      2 * 2 ^ dataWidth

theorem circuit_cost_le
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    (circuit function).cost DeMorgan.standardCost <=
      costBound addressWidth dataWidth := by
  rw [circuit, Circuit.cost_comp, Circuit.cost_comp,
    splitMintermCircuit, Circuit.cost_parallel,
    Circuit.cost_mapInputs, Circuit.cost_mapInputs,
    libraryAndDataCircuit, Circuit.cost_castCounts,
    Circuit.cost_parallel, Circuit.cost_mapInputs,
    Circuit.cost_mapOutputs, Circuit.cost_id,
    libraryCircuit_cost, DeMorgan.Expression.circuit_cost,
    synthesisExpression_standardCost]
  unfold costBound
  have addressBound := mintermCircuit_cost_le addressWidth
  have dataBound := mintermCircuit_cost_le dataWidth
  omega

/-! ## A uniform `O(2^N / N)` specialization

The parameter choice and arithmetic below follow the full-column-library
proof in
`projects/formalization/complexitylib/Complexitylib/Circuits/Internal/ShannonUpper.lean`.
The circuit construction above is new to Algebraic; only the elementary
choice `k = floor(log_2 N) - 1` and its inequalities are reused.
-/

/-- Number of short address variables in the uniform specialization. -/
def shannonAddressWidth (inputs : Nat) : Nat :=
  Nat.log 2 inputs - 1

/-- Number of remaining data variables. -/
def shannonDataWidth (inputs : Nat) : Nat :=
  inputs - shannonAddressWidth inputs

private theorem log_ge_one
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    1 <= Nat.log 2 inputs :=
  Nat.le_log_of_pow_le (by omega) (by omega)

private theorem log_lt_inputs
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    Nat.log 2 inputs < inputs :=
  Nat.log_lt_of_lt_pow (by omega)
    (@Nat.lt_pow_self inputs 2 (by omega))

theorem shannonAddressWidth_ge_three
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    3 <= shannonAddressWidth inputs := by
  unfold shannonAddressWidth
  have := Nat.le_log_of_pow_le (by omega : 1 < 2)
    (show 2 ^ 4 <= inputs by omega)
  omega

theorem shannonDataWidth_pos
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    0 < shannonDataWidth inputs := by
  unfold shannonDataWidth shannonAddressWidth
  have := log_lt_inputs inputs inputsLarge
  omega

private theorem shannonAddressWidth_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    shannonAddressWidth inputs <= inputs := by
  unfold shannonAddressWidth
  have := log_lt_inputs inputs inputsLarge
  omega

/-- The selected address/data split has exactly the original input width. -/
theorem shannonAddressDataSum
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    shannonAddressWidth inputs + shannonDataWidth inputs = inputs := by
  unfold shannonDataWidth
  have := shannonAddressWidth_le inputs inputsLarge
  omega

private theorem shannonPowSplit
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    2 ^ shannonDataWidth inputs * 2 ^ shannonAddressWidth inputs =
      2 ^ inputs := by
  rw [← Nat.pow_add]
  congr 1
  rw [Nat.add_comm]
  exact shannonAddressDataSum inputs inputsLarge

private theorem two_mul_pow_address_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    2 * 2 ^ shannonAddressWidth inputs <= inputs := by
  unfold shannonAddressWidth
  have logPositive := log_ge_one inputs inputsLarge
  have powerIdentity :
      2 * 2 ^ (Nat.log 2 inputs - 1) = 2 ^ Nat.log 2 inputs := by
    conv_rhs =>
      rw [show Nat.log 2 inputs = (Nat.log 2 inputs - 1) + 1 by omega]
    rw [Nat.pow_succ]
    ring
  rw [powerIdentity]
  exact Nat.pow_log_le_self 2 (by omega)

private theorem inputs_lt_four_mul_pow_address
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    inputs < 4 * 2 ^ shannonAddressWidth inputs := by
  unfold shannonAddressWidth
  have logPositive := log_ge_one inputs inputsLarge
  have powerIdentity :
      4 * 2 ^ (Nat.log 2 inputs - 1) =
        2 ^ (Nat.log 2 inputs + 1) := by
    conv_rhs =>
      rw [show Nat.log 2 inputs + 1 =
        (Nat.log 2 inputs - 1) + 2 by omega]
    rw [Nat.pow_add]
    omega
  rw [powerIdentity]
  exact Nat.lt_pow_succ_log_self (by omega) inputs

private theorem two_inputs_plus_one_le_pow
    (inputs : Nat) (inputsAtLeastFour : 4 <= inputs) :
    2 * inputs + 1 <= 2 ^ inputs := by
  induction inputs with
  | zero => omega
  | succ prior inductionHypothesis =>
      cases Nat.lt_or_ge prior 4 with
      | inl below =>
          have : prior = 3 := by omega
          subst prior
          norm_num
      | inr above =>
          have priorBound := inductionHypothesis (by omega)
          calc
            2 * (prior + 1) + 1 = 2 * prior + 1 + 2 := by ring
            _ <= 2 ^ prior + 2 := by omega
            _ <= 2 ^ prior + 2 ^ prior := by
              nlinarith [@Nat.lt_pow_self prior 2 (by omega)]
            _ = 2 ^ (prior + 1) := by ring

private theorem square_le_pow
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    inputs * inputs <= 2 ^ inputs := by
  induction inputs with
  | zero => omega
  | succ prior inductionHypothesis =>
      cases Nat.lt_or_ge prior 16 with
      | inl below =>
          have : prior = 15 := by omega
          subst prior
          norm_num
      | inr above =>
          have priorSquare := inductionHypothesis (by omega)
          have linearBound := two_inputs_plus_one_le_pow prior (by omega)
          calc
            (prior + 1) * (prior + 1) =
                prior * prior + 2 * prior + 1 := by ring
            _ <= 2 ^ prior + (2 * prior + 1) := by omega
            _ <= 2 ^ prior + 2 ^ prior := by omega
            _ = 2 ^ (prior + 1) := by ring

private theorem dataTerm
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    6 * 2 ^ shannonDataWidth inputs * inputs <= 24 * 2 ^ inputs := by
  have inputBound := inputs_lt_four_mul_pow_address inputs inputsLarge
  calc
    6 * 2 ^ shannonDataWidth inputs * inputs <=
        6 * 2 ^ shannonDataWidth inputs *
          (4 * 2 ^ shannonAddressWidth inputs) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 24 * (2 ^ shannonDataWidth inputs *
        2 ^ shannonAddressWidth inputs) := by ring
    _ = 24 * 2 ^ inputs := by rw [shannonPowSplit inputs inputsLarge]

private theorem addressTerm
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    4 * 2 ^ shannonAddressWidth inputs * inputs <= 2 * 2 ^ inputs := by
  have addressBound := two_mul_pow_address_le inputs inputsLarge
  have squareBound := square_le_pow inputs inputsLarge
  calc
    4 * 2 ^ shannonAddressWidth inputs * inputs =
        2 * ((2 * 2 ^ shannonAddressWidth inputs) * inputs) := by ring
    _ <= 2 * (inputs * inputs) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right inputs addressBound)
    _ <= 2 * 2 ^ inputs := Nat.mul_le_mul_left 2 squareBound

private theorem pow_ge_four_mul
    (exponent : Nat) (atLeastFour : 4 <= exponent) :
    4 * exponent <= 2 ^ exponent := by
  induction exponent with
  | zero => omega
  | succ prior inductionHypothesis =>
      cases Nat.lt_or_ge prior 4 with
      | inl below =>
          have : prior = 3 := by omega
          subst prior
          norm_num
      | inr above =>
          have priorBound := inductionHypothesis (by omega)
          calc
            4 * (prior + 1) = 4 * prior + 4 := by ring
            _ <= 2 ^ prior + 4 := by omega
            _ <= 2 ^ prior + 2 ^ prior := by
              nlinarith [@Nat.lt_pow_self prior 2 (by omega)]
            _ = 2 ^ (prior + 1) := by ring

private theorem log_le_quarter
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    4 * Nat.log 2 inputs <= inputs := by
  have logAtLeastFour : 4 <= Nat.log 2 inputs :=
    Nat.le_log_of_pow_le (by omega) (by omega)
  calc
    4 * Nat.log 2 inputs <= 2 ^ Nat.log 2 inputs :=
      pow_ge_four_mul (Nat.log 2 inputs) logAtLeastFour
    _ <= inputs := Nat.pow_log_le_self 2 (by omega)

private theorem addressPowerPlusAddress_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    2 ^ shannonAddressWidth inputs + shannonAddressWidth inputs +
        (Nat.log 2 inputs + 1) <= inputs := by
  unfold shannonAddressWidth
  have logPositive : 1 <= Nat.log 2 inputs :=
    Nat.le_log_of_pow_le (by omega) (by omega)
  have powerIdentity :
      2 * 2 ^ (Nat.log 2 inputs - 1) = 2 ^ Nat.log 2 inputs := by
    conv_rhs =>
      rw [show Nat.log 2 inputs = (Nat.log 2 inputs - 1) + 1 by omega]
    rw [Nat.pow_succ]
    ring
  have addressPowerBound :
      2 * 2 ^ (Nat.log 2 inputs - 1) <= inputs := by
    rw [powerIdentity]
    exact Nat.pow_log_le_self 2 (by omega)
  have logarithmBound := log_le_quarter inputs inputsLarge
  omega

private theorem libraryTerm
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    (2 ^ (2 ^ shannonAddressWidth inputs) *
        2 ^ shannonAddressWidth inputs) * inputs <= 2 ^ inputs := by
  have exponentBound := addressPowerPlusAddress_le inputs inputsLarge
  have remainingBound : Nat.log 2 inputs + 1 <=
      inputs - (2 ^ shannonAddressWidth inputs +
        shannonAddressWidth inputs) := by
    omega
  have inputPowerBound : inputs <
      2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
        shannonAddressWidth inputs)) :=
    calc
      inputs < 2 ^ (Nat.log 2 inputs + 1) :=
        Nat.lt_pow_succ_log_self (by omega) inputs
      _ <= 2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs)) :=
        Nat.pow_le_pow_right (by omega) remainingBound
  have powerSplit :
      2 ^ (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs) *
        2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs)) = 2 ^ inputs := by
    rw [← Nat.pow_add]
    congr 1
    omega
  calc
    (2 ^ (2 ^ shannonAddressWidth inputs) *
        2 ^ shannonAddressWidth inputs) * inputs =
      2 ^ (2 ^ shannonAddressWidth inputs +
        shannonAddressWidth inputs) * inputs := by
        rw [Nat.pow_add]
    _ <= 2 ^ (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs) *
        2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs)) :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt inputPowerBound)
    _ = 2 ^ inputs := powerSplit

/-- The full native Shannon cost ledger, multiplied by `N`, is bounded by
`27 * 2^N`. -/
theorem shannonArithmetic
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    costBound (shannonAddressWidth inputs) (shannonDataWidth inputs) *
        inputs <= 27 * 2 ^ inputs := by
  have dataBound := dataTerm inputs inputsLarge
  have addressBound := addressTerm inputs inputsLarge
  have libraryBound := libraryTerm inputs inputsLarge
  unfold costBound
  calc
    (4 * 2 ^ shannonAddressWidth inputs +
        4 * 2 ^ shannonDataWidth inputs +
        2 ^ 2 ^ shannonAddressWidth inputs *
          2 ^ shannonAddressWidth inputs +
        2 * 2 ^ shannonDataWidth inputs) * inputs =
      4 * 2 ^ shannonAddressWidth inputs * inputs +
        6 * 2 ^ shannonDataWidth inputs * inputs +
        (2 ^ 2 ^ shannonAddressWidth inputs *
          2 ^ shannonAddressWidth inputs) * inputs := by ring
    _ <= 2 * 2 ^ inputs + 24 * 2 ^ inputs + 2 ^ inputs := by
      omega
    _ = 27 * 2 ^ inputs := by ring

/-- The selected finite cost ledger is at most `27 * 2^N / N`. -/
theorem shannonCostBound_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    costBound (shannonAddressWidth inputs) (shannonDataWidth inputs) <=
      27 * 2 ^ inputs / inputs := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  exact shannonArithmetic inputs inputsLarge

/-- Reindex a function along an equality of finite input counts. -/
def reindexFunction
    (inputCount : splitInputs = inputs)
    (function : ScalarFunction Bool inputs) :
    ScalarFunction Bool splitInputs :=
  fun input => function (input ∘ Fin.cast inputCount.symm)

/-- Uniform native Shannon circuit for an arbitrary `N`-input Boolean
function. -/
noncomputable def shannonCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    Circuit DeMorgan.signature inputs
      (synthesisGateCount
        (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      1 :=
  (circuit (addressWidth := shannonAddressWidth inputs)
    (dataWidth := shannonDataWidth inputs)
    (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      |>.castCounts (shannonAddressDataSum inputs inputsLarge) rfl rfl

@[simp] theorem shannonCircuit_eval
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (input : Fin inputs -> Bool) :
    (shannonCircuit inputs inputsLarge function).eval
        DeMorgan.interpretation input 0 = function input := by
  rw [shannonCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, id_eq]
  rw [circuit_eval]
  unfold reindexFunction
  apply congrArg function
  funext index
  simp [Function.comp_apply]

theorem shannonCircuit_computes
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    (shannonCircuit inputs inputsLarge function).Computes
      DeMorgan.interpretation (scalarTarget function) := by
  intro input
  funext output
  have outputZero : output = 0 := Fin.eq_zero output
  subst output
  exact shannonCircuit_eval inputs inputsLarge function input

theorem shannonCircuit_cost_le
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    (shannonCircuit inputs inputsLarge function).cost
        DeMorgan.standardCost <= 27 * 2 ^ inputs / inputs := by
  rw [shannonCircuit, Circuit.cost_castCounts]
  exact (circuit_cost_le
    (reindexFunction (shannonAddressDataSum inputs inputsLarge) function)).trans
      (shannonCostBound_le inputs inputsLarge)

/-- The concrete independently replicated Shannon circuit. -/
noncomputable def replicatedShannonCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    Circuit DeMorgan.signature (copies * inputs)
      (copies * synthesisGateCount
        (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      copies :=
  (shannonCircuit inputs inputsLarge function).replicateScalar copies

theorem replicatedShannonCircuit_computes
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    (replicatedShannonCircuit inputs inputsLarge function copies).Computes
      DeMorgan.interpretation (directProduct function copies) := by
  intro input
  rw [replicatedShannonCircuit, Circuit.eval_replicateScalar]
  funext copy
  exact shannonCircuit_eval inputs inputsLarge function
    (directProductInput input copy)

/-- A minimum-cost realization of a finite Boolean direct product, selected
from the nonempty implementation family witnessed by Shannon replication. -/
noncomputable def minimumMassCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    Circuit.Minimum DeMorgan.standardCost DeMorgan.interpretation
      (directProduct function copies) :=
  Circuit.minimum DeMorgan.standardCost
    (replicatedShannonCircuit inputs inputsLarge function copies)
    DeMorgan.interpretation (directProduct function copies)
    (replicatedShannonCircuit_computes inputs inputsLarge function copies)

/-- The selected minimum circuit realizes `booleanMassComplexity` exactly. -/
theorem minimumMassCircuit_cost_eq_complexity
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    booleanMassComplexity function copies =
      ((minimumMassCircuit inputs inputsLarge function copies).circuit.cost
        DeMorgan.standardCost : ENat) := by
  unfold booleanMassComplexity
  exact Circuit.costComplexity_eq DeMorgan.standardCost
    (minimumMassCircuit inputs inputsLarge function copies).computes
    (minimumMassCircuit inputs inputsLarge function copies).minimal.cost

theorem minimumMassCircuit_cost_le
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies bound : Nat)
    (complexityBound : booleanMassComplexity function copies <=
      (bound : Nat)) :
    (minimumMassCircuit inputs inputsLarge function copies).circuit.cost
        DeMorgan.standardCost <= bound := by
  have castBound :
      ((minimumMassCircuit inputs inputsLarge function copies).circuit.cost
          DeMorgan.standardCost : ENat) <= (bound : Nat) := by
    rw [← minimumMassCircuit_cost_eq_complexity]
    exact complexityBound
  exact_mod_cast castBound

/-- Naive replication of native Shannon synthesis bounds any finite number
of independent copies.  This is the base finite upper bound used before the
mass-production composition improves the dependence on `copies`. -/
theorem booleanMassComplexity_le_replicatedShannon
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    booleanMassComplexity function copies <=
      (copies * (27 * 2 ^ inputs / inputs) : Nat) := by
  let base := shannonCircuit inputs inputsLarge function
  let replicated := base.replicateScalar copies
  have computes : replicated.Computes DeMorgan.interpretation
      (directProduct function copies) := by
    intro input
    rw [show replicated = base.replicateScalar copies by rfl,
      Circuit.eval_replicateScalar]
    funext copy
    exact shannonCircuit_eval inputs inputsLarge function
      (directProductInput input copy)
  have complexityBound := replicated.costComplexity_le
    DeMorgan.standardCost computes
  have finiteBound : replicated.cost DeMorgan.standardCost <=
      copies * (27 * 2 ^ inputs / inputs) := by
    rw [show replicated = base.replicateScalar copies by rfl,
      Circuit.cost_replicateScalar]
    apply Nat.mul_le_mul_left
    exact shannonCircuit_cost_le inputs inputsLarge function
  unfold booleanMassComplexity
  exact complexityBound.trans (by exact_mod_cast finiteBound)

end ShannonSynthesis
end MassProduction
end Algebraic
