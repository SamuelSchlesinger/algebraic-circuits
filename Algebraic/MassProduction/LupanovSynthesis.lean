import Algebraic.MassProduction.CodeParameters
import Algebraic.MassProduction.ShannonSynthesis
import Algebraic.MassProduction.UhligTheorem
import Mathlib.Data.Fintype.EquivFin

/-!
# Sharp Lupanov synthesis

This module formalizes the block-table construction behind the sharp
one-copy upper bound.  Address assignments are divided into short consecutive
blocks.  For each block and each Boolean pattern on that block, one circuit
recognizes the indicated address rows and one sparse circuit recognizes the
data columns having that pattern.  Their conjunctions reconstruct the target
truth table.

All synthesis data is passed explicitly.  In particular, this module adds no
type-class instances.
-/

namespace Algebraic
namespace MassProduction
namespace LupanovSynthesis

open scoped BigOperators
open ShannonSynthesis

/-- Number of consecutive address-table blocks of length `blockSize`. -/
def blockCount (addressWidth blockSize : Nat) : Nat :=
  (2 ^ addressWidth) ⌈/⌉ blockSize

/-- Number of Boolean patterns on one address block. -/
def patternCount (blockSize : Nat) : Nat :=
  2 ^ blockSize

/-- The block containing a given address assignment. -/
def selectedBlock
    (blockSizePositive : 0 < blockSize)
    (address : Fin (2 ^ addressWidth)) :
    Fin (blockCount addressWidth blockSize) := by
  refine ⟨address.val / blockSize, ?_⟩
  by_contra notBelow
  have countLe : blockCount addressWidth blockSize <=
      address.val / blockSize := Nat.le_of_not_gt notBelow
  have capacity : 2 ^ addressWidth <=
      blockCount addressWidth blockSize * blockSize := by
    unfold blockCount
    simpa only [Nat.mul_comm] using
      (ceilDiv_le_iff_le_mul blockSizePositive).mp
        (show (2 ^ addressWidth) ⌈/⌉ blockSize <=
          (2 ^ addressWidth) ⌈/⌉ blockSize from le_rfl)
  have quotientPart :
      (address.val / blockSize) * blockSize <= address.val :=
    Nat.div_mul_le_self address.val blockSize
  have : 2 ^ addressWidth <= address.val :=
    capacity.trans <| (Nat.mul_le_mul_right blockSize countLe).trans quotientPart
  exact (Nat.not_le_of_lt address.isLt) this

/-- Offset of an address assignment inside its selected block. -/
def selectedOffset
    (blockSizePositive : 0 < blockSize)
    (address : Fin (2 ^ addressWidth)) : Fin blockSize :=
  ⟨address.val % blockSize, Nat.mod_lt _ blockSizePositive⟩

/-- The padded truth-table column on one consecutive address block.  Rows
beyond the address table in the last block are fixed to false. -/
noncomputable def blockColumn
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (data : Fin (2 ^ dataWidth)) : Fin blockSize -> Bool :=
  fun offset =>
    if rowValid : block.val * blockSize + offset.val < 2 ^ addressWidth then
      function (Fin.append
        (assignmentBits addressWidth
          ⟨block.val * blockSize + offset.val, rowValid⟩)
        (assignmentBits dataWidth data))
    else
      false

/-- Canonical index of the padded pattern in one truth-table block. -/
noncomputable def blockPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (data : Fin (2 ^ dataWidth)) : Fin (patternCount blockSize) :=
  bitVectorEquiv blockSize (blockColumn function block data)

@[simp] theorem assignmentBits_blockPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (data : Fin (2 ^ dataWidth))
    (offset : Fin blockSize) :
    assignmentBits blockSize (blockPattern function block data) offset =
      blockColumn function block data offset := by
  unfold blockPattern
  rw [assignmentBits_bitVectorEquiv]

/-- Data assignments whose padded column has one fixed block pattern. -/
noncomputable def rightSupport
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    Finset (Fin (2 ^ dataWidth)) :=
  Finset.univ.filter fun data => blockPattern function block data = pattern

@[simp] theorem mem_rightSupport
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (data : Fin (2 ^ dataWidth)) :
    data ∈ rightSupport function block pattern ↔
      blockPattern function block data = pattern := by
  simp [rightSupport]

/-- OR exactly the input wires in a finite support.  Unlike a full-width OR,
its charged size is the cardinality of the support. -/
noncomputable def supportExpression
    (support : Finset (Fin inputs)) : DeMorgan.Expression inputs :=
  DeMorgan.Expression.finOr support.card fun index =>
    .input ((support.equivFin).symm index).1

theorem supportExpression_standardCost
    (support : Finset (Fin inputs)) :
    (supportExpression support).standardCost = support.card := by
  rw [supportExpression, DeMorgan.Expression.finOr_standardCost]
  simp [DeMorgan.Expression.standardCost]

/-- On a one-hot vector, a sparse OR is exactly support membership of the
selected coordinate. -/
theorem supportExpression_eval_oneHot
    (support : Finset (Fin inputs))
    (flags : Fin inputs -> Bool)
    (selected : Fin inputs)
    (selectedTrue : flags selected = true)
    (unique : forall index, flags index = true -> index = selected) :
    (supportExpression support).eval flags =
      decide (selected ∈ support) := by
  apply Bool.eq_iff_iff.mpr
  rw [supportExpression, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨index, indexTrue⟩
    simp only [DeMorgan.Expression.eval] at indexTrue
    have selectedIndex : ((support.equivFin).symm index).1 = selected :=
      unique _ indexTrue
    simp [← selectedIndex]
  · intro selectedMember
    let member : support := ⟨selected, selectedMember⟩
    refine ⟨support.equivFin member, ?_⟩
    simp only [DeMorgan.Expression.eval]
    simpa [member] using selectedTrue

/-- The sparse data-pattern expression for one block and pattern. -/
noncomputable def rightExpression
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    DeMorgan.Expression (2 ^ dataWidth) :=
  supportExpression (rightSupport function block pattern)

theorem rightExpression_standardCost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (rightExpression function block pattern).standardCost =
      (rightSupport function block pattern).card := by
  exact supportExpression_standardCost _

/-- The right supports for a fixed block partition all data assignments. -/
theorem sum_rightSupport_card
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize)) :
    (∑ pattern : Fin (patternCount blockSize),
        (rightSupport function block pattern).card) = 2 ^ dataWidth := by
  classical
  have partition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin (2 ^ dataWidth))))
    (t := (Finset.univ : Finset (Fin (patternCount blockSize))))
    (f := blockPattern function block)
    (by simp)
  simpa [rightSupport] using partition.symm

/-! ## The two pattern banks -/

/-- One possible row of a block pattern, gated by its address minterm. -/
noncomputable def leftTerm
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (offset : Fin blockSize) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  if rowValid : block.val * blockSize + offset.val < 2 ^ addressWidth then
    if assignmentBits blockSize pattern offset then
      .input ⟨block.val * blockSize + offset.val, rowValid⟩
    else
      .constant false
  else
    .constant false

@[simp] theorem leftTerm_standardCost
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (offset : Fin blockSize) :
    (leftTerm addressWidth blockSize block pattern offset).standardCost = 0 := by
  unfold leftTerm
  split
  · split <;> rfl
  · rfl

@[simp] theorem leftTerm_eval
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (offset : Fin blockSize)
    (flags : Fin (2 ^ addressWidth) -> Bool) :
    (leftTerm addressWidth blockSize block pattern offset).eval flags =
      if rowValid : block.val * blockSize + offset.val < 2 ^ addressWidth then
        flags ⟨block.val * blockSize + offset.val, rowValid⟩ &&
          assignmentBits blockSize pattern offset
      else
        false := by
  unfold leftTerm
  split <;> rename_i rowValid
  · cases patternBit : assignmentBits blockSize pattern offset <;>
      simp [DeMorgan.Expression.eval]
  · simp [DeMorgan.Expression.eval]

/-- Address-side recognizer of one pattern in one block. -/
noncomputable def leftExpression
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  DeMorgan.Expression.finOr blockSize fun offset =>
    leftTerm addressWidth blockSize block pattern offset

theorem leftExpression_standardCost
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (leftExpression addressWidth blockSize block pattern).standardCost =
      blockSize := by
  rw [leftExpression, DeMorgan.Expression.finOr_standardCost]
  simp

/-- Program-gate count of all left recognizers for one block. -/
@[reducible] noncomputable def leftBlockGateCount
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) : Nat :=
  ∑ pattern : Fin (patternCount blockSize),
    (leftExpression addressWidth blockSize block pattern).gateCount

/-- All address-side pattern recognizers for one block. -/
noncomputable def leftBlockCircuit
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    Circuit DeMorgan.signature (2 ^ addressWidth)
      (leftBlockGateCount addressWidth blockSize block)
      (patternCount blockSize) :=
  Circuit.parallelFin (patternCount blockSize)
    (fun pattern =>
      (leftExpression addressWidth blockSize block pattern).gateCount)
    (fun pattern =>
      (leftExpression addressWidth blockSize block pattern).circuit)

@[simp] theorem leftBlockCircuit_eval
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (flags : Fin (2 ^ addressWidth) -> Bool)
    (pattern : Fin (patternCount blockSize)) :
    (leftBlockCircuit addressWidth blockSize block).eval
        DeMorgan.interpretation flags pattern =
      (leftExpression addressWidth blockSize block pattern).eval flags := by
  unfold leftBlockCircuit leftBlockGateCount
  rw [Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]

theorem leftBlockCircuit_cost
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    (leftBlockCircuit addressWidth blockSize block).cost
        DeMorgan.standardCost =
      patternCount blockSize * blockSize := by
  unfold leftBlockCircuit leftBlockGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ pattern : Fin (patternCount blockSize),
        (leftExpression addressWidth blockSize block pattern).circuit.cost
          DeMorgan.standardCost) =
        ∑ _pattern : Fin (patternCount blockSize), blockSize := by
          apply Finset.sum_congr rfl
          intro pattern _membership
          rw [DeMorgan.Expression.circuit_cost,
            leftExpression_standardCost]
    _ = patternCount blockSize * blockSize := by simp

/-- Program-gate count of all sparse right recognizers for one block. -/
@[reducible] noncomputable def rightBlockGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) : Nat :=
  ∑ pattern : Fin (patternCount blockSize),
    (rightExpression function block pattern).gateCount

/-- All sparse data-side pattern recognizers for one block. -/
noncomputable def rightBlockCircuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    Circuit DeMorgan.signature (2 ^ dataWidth)
      (rightBlockGateCount function blockSize block)
      (patternCount blockSize) :=
  Circuit.parallelFin (patternCount blockSize)
    (fun pattern => (rightExpression function block pattern).gateCount)
    (fun pattern => (rightExpression function block pattern).circuit)

@[simp] theorem rightBlockCircuit_eval
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (flags : Fin (2 ^ dataWidth) -> Bool)
    (pattern : Fin (patternCount blockSize)) :
    (rightBlockCircuit function blockSize block).eval
        DeMorgan.interpretation flags pattern =
      (rightExpression function block pattern).eval flags := by
  unfold rightBlockCircuit rightBlockGateCount
  rw [Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]

theorem rightBlockCircuit_cost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    (rightBlockCircuit function blockSize block).cost
        DeMorgan.standardCost = 2 ^ dataWidth := by
  unfold rightBlockCircuit rightBlockGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ pattern : Fin (patternCount blockSize),
        (rightExpression function block pattern).circuit.cost
          DeMorgan.standardCost) =
        ∑ pattern : Fin (patternCount blockSize),
          (rightSupport function block pattern).card := by
            apply Finset.sum_congr rfl
            intro pattern _membership
            rw [DeMorgan.Expression.circuit_cost,
              rightExpression_standardCost]
    _ = 2 ^ dataWidth := sum_rightSupport_card function block

/-- Program-gate count of the complete address-side pattern bank. -/
@[reducible] noncomputable def leftBankGateCount
    (addressWidth blockSize : Nat) : Nat :=
  ∑ block : Fin (blockCount addressWidth blockSize),
    leftBlockGateCount addressWidth blockSize block

/-- The address-side pattern banks, flattened in `(block, pattern)` order. -/
noncomputable def leftBankCircuit
    (addressWidth dataWidth blockSize : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (leftBankGateCount addressWidth blockSize)
      (blockCount addressWidth blockSize * patternCount blockSize) :=
  Circuit.parallelFinVector
    (blockCount addressWidth blockSize) (patternCount blockSize)
    (fun block => leftBlockGateCount addressWidth blockSize block)
    (fun block =>
      (leftBlockCircuit addressWidth blockSize block).mapInputs
        (Fin.castAdd (2 ^ dataWidth)))

@[simp] theorem leftBankCircuit_eval
    (addressWidth dataWidth blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (leftBankCircuit addressWidth dataWidth blockSize).eval
        DeMorgan.interpretation state (finProdFinEquiv (block, pattern)) =
      (leftExpression addressWidth blockSize block pattern).eval
        (fun address => state (Fin.castAdd (2 ^ dataWidth) address)) := by
  rw [leftBankCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs, leftBlockCircuit_eval]
  rfl

theorem leftBankCircuit_cost
    (addressWidth dataWidth blockSize : Nat) :
    (leftBankCircuit addressWidth dataWidth blockSize).cost
        DeMorgan.standardCost =
      blockCount addressWidth blockSize *
        (patternCount blockSize * blockSize) := by
  unfold leftBankCircuit leftBankGateCount
  rw [Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_mapInputs, leftBlockCircuit_cost]
  simp

/-- Program-gate count of the complete data-side pattern bank. -/
@[reducible] noncomputable def rightBankGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) : Nat :=
  ∑ block : Fin (blockCount addressWidth blockSize),
    rightBlockGateCount function blockSize block

/-- The data-side sparse pattern banks, flattened in `(block, pattern)`
order. -/
noncomputable def rightBankCircuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (rightBankGateCount function blockSize)
      (blockCount addressWidth blockSize * patternCount blockSize) :=
  Circuit.parallelFinVector
    (blockCount addressWidth blockSize) (patternCount blockSize)
    (fun block => rightBlockGateCount function blockSize block)
    (fun block =>
      (rightBlockCircuit function blockSize block).mapInputs
        (Fin.natAdd (2 ^ addressWidth)))

@[simp] theorem rightBankCircuit_eval
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (rightBankCircuit function blockSize).eval
        DeMorgan.interpretation state (finProdFinEquiv (block, pattern)) =
      (rightExpression function block pattern).eval
        (fun data => state (Fin.natAdd (2 ^ addressWidth) data)) := by
  rw [rightBankCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs, rightBlockCircuit_eval]
  rfl

theorem rightBankCircuit_cost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    (rightBankCircuit function blockSize).cost DeMorgan.standardCost =
      blockCount addressWidth blockSize * 2 ^ dataWidth := by
  unfold rightBankCircuit rightBankGateCount
  rw [Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_mapInputs, rightBlockCircuit_cost]
  simp

/-! ## Recombination and the complete finite circuit -/

/-- Number of flattened `(block, pattern)` flags in either bank. -/
@[reducible] def bankWidth (addressWidth blockSize : Nat) : Nat :=
  blockCount addressWidth blockSize * patternCount blockSize

/-- Program-gate count of both flattened pattern banks. -/
@[reducible] noncomputable def patternBankGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) : Nat :=
  leftBankGateCount addressWidth blockSize +
    rightBankGateCount function blockSize

/-- Compute the left and right pattern banks side by side. -/
noncomputable def patternBankCircuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (patternBankGateCount function blockSize)
      (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  (leftBankCircuit addressWidth dataWidth blockSize).parallel
    (rightBankCircuit function blockSize)

/-- Coordinate of a left-bank flag in the combined pattern state. -/
def leftPatternInput
    (index : Fin (bankWidth addressWidth blockSize)) :
    Fin (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  Fin.castAdd _ index

/-- Coordinate of the corresponding right-bank flag. -/
def rightPatternInput
    (index : Fin (bankWidth addressWidth blockSize)) :
    Fin (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  Fin.natAdd _ index

@[simp] theorem patternBankCircuit_eval_left
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (patternBankCircuit function blockSize).eval DeMorgan.interpretation state
        (leftPatternInput (finProdFinEquiv (block, pattern))) =
      (leftExpression addressWidth blockSize block pattern).eval
        (fun address => state (Fin.castAdd (2 ^ dataWidth) address)) := by
  rw [patternBankCircuit, Circuit.eval_parallel]
  unfold leftPatternInput
  rw [Fin.append_left, leftBankCircuit_eval]

@[simp] theorem patternBankCircuit_eval_right
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (patternBankCircuit function blockSize).eval DeMorgan.interpretation state
        (rightPatternInput (finProdFinEquiv (block, pattern))) =
      (rightExpression function block pattern).eval
        (fun data => state (Fin.natAdd (2 ^ addressWidth) data)) := by
  rw [patternBankCircuit, Circuit.eval_parallel]
  unfold rightPatternInput
  rw [Fin.append_right, rightBankCircuit_eval]

theorem patternBankCircuit_cost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    (patternBankCircuit function blockSize).cost DeMorgan.standardCost =
      blockCount addressWidth blockSize *
          (patternCount blockSize * blockSize) +
        blockCount addressWidth blockSize * 2 ^ dataWidth := by
  rw [patternBankCircuit, Circuit.cost_parallel,
    leftBankCircuit_cost, rightBankCircuit_cost]

/-- Conjoin corresponding flags in the two pattern banks. -/
def matchingPatternTerm
    (addressWidth blockSize : Nat)
    (index : Fin (bankWidth addressWidth blockSize)) :
    DeMorgan.Expression
      (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  .and (.input (leftPatternInput index)) (.input (rightPatternInput index))

/-- OR all matching block-pattern conjunctions. -/
def synthesisExpression
    (addressWidth blockSize : Nat) :
    DeMorgan.Expression
      (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  DeMorgan.Expression.finOr (bankWidth addressWidth blockSize)
    (matchingPatternTerm addressWidth blockSize)

theorem synthesisExpression_standardCost
    (addressWidth blockSize : Nat) :
    (synthesisExpression addressWidth blockSize).standardCost =
      2 * bankWidth addressWidth blockSize := by
  rw [synthesisExpression, DeMorgan.Expression.finOr_standardCost]
  simp [matchingPatternTerm, DeMorgan.Expression.standardCost]
  omega

/-- Program-gate count of all three stages of finite Lupanov synthesis. -/
@[reducible] noncomputable def synthesisGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) : Nat :=
  splitMintermGateCount addressWidth dataWidth +
    patternBankGateCount function blockSize +
      (synthesisExpression addressWidth blockSize).gateCount

/-- The finite Lupanov block-table circuit. -/
noncomputable def circuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    Circuit DeMorgan.signature (addressWidth + dataWidth)
      (synthesisGateCount function blockSize) 1 :=
  (synthesisExpression addressWidth blockSize).circuit.comp
    ((patternBankCircuit function blockSize).comp
      (splitMintermCircuit addressWidth dataWidth))

/-- Explicit finite cost ledger. -/
def costBound
    (addressWidth dataWidth blockSize : Nat) : Nat :=
  4 * 2 ^ addressWidth + 4 * 2 ^ dataWidth +
    blockCount addressWidth blockSize *
        (patternCount blockSize * blockSize) +
      blockCount addressWidth blockSize * 2 ^ dataWidth +
        2 * bankWidth addressWidth blockSize

theorem circuit_cost_le
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    (circuit function blockSize).cost DeMorgan.standardCost <=
      costBound addressWidth dataWidth blockSize := by
  rw [circuit, Circuit.cost_comp, Circuit.cost_comp,
    DeMorgan.Expression.circuit_cost, synthesisExpression_standardCost,
    patternBankCircuit_cost, splitMintermCircuit,
    Circuit.cost_parallel, Circuit.cost_mapInputs, Circuit.cost_mapInputs]
  have addressBound := mintermCircuit_cost_le addressWidth
  have dataBound := mintermCircuit_cost_le dataWidth
  unfold costBound
  omega

/-! ## Exact semantics -/

/-- The address-side block expression, fed by the shared minterm table, is
true exactly when one of its literal rows is the selected address and the
corresponding pattern bit is true. -/
theorem leftExpression_eval_minterms_true_iff
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (addressInput : Fin addressWidth -> Bool) :
    (leftExpression addressWidth blockSize block pattern).eval
          ((mintermCircuit addressWidth).eval
            DeMorgan.interpretation addressInput) = true ↔
      exists offset : Fin blockSize,
        exists rowValid : block.val * blockSize + offset.val <
            2 ^ addressWidth,
          (⟨block.val * blockSize + offset.val, rowValid⟩ :
              Fin (2 ^ addressWidth)) =
              bitVectorEquiv addressWidth addressInput /\
            assignmentBits blockSize pattern offset = true := by
  rw [leftExpression, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff]
  constructor
  · rintro ⟨offset, offsetTrue⟩
    rw [leftTerm_eval] at offsetTrue
    split at offsetTrue
    · rename_i rowValid
      rw [Bool.and_eq_true] at offsetTrue
      refine ⟨offset, rowValid, ?_, offsetTrue.2⟩
      rw [mintermCircuit_eval] at offsetTrue
      exact (of_decide_eq_true offsetTrue.1).symm
    · contradiction
  · rintro ⟨offset, rowValid, rowSelected, patternTrue⟩
    refine ⟨offset, ?_⟩
    rw [leftTerm_eval]
    simp only [dif_pos rowValid, Bool.and_eq_true]
    constructor
    · rw [mintermCircuit_eval]
      exact decide_eq_true rowSelected.symm
    · exact patternTrue

/-- The data-side sparse expression, fed by the shared minterm table, is the
indicator of the selected data column having the requested block pattern. -/
theorem rightExpression_eval_minterms
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (dataInput : Fin dataWidth -> Bool) :
    (rightExpression function block pattern).eval
          ((mintermCircuit dataWidth).eval
            DeMorgan.interpretation dataInput) =
      decide (blockPattern function block
        (bitVectorEquiv dataWidth dataInput) = pattern) := by
  unfold rightExpression
  let selected := bitVectorEquiv dataWidth dataInput
  have sparse := supportExpression_eval_oneHot
    (rightSupport function block pattern)
    ((mintermCircuit dataWidth).eval DeMorgan.interpretation dataInput)
    selected
    (by
      rw [mintermCircuit_eval]
      simp [selected])
    (by
      intro assignment assignmentTrue
      rw [mintermCircuit_eval] at assignmentTrue
      simpa [selected] using (of_decide_eq_true assignmentTrue).symm)
  simpa [rightSupport, selected] using sparse

/-- The finite block-table circuit computes the supplied Boolean function
exactly. -/
theorem circuit_eval
    (blockSizePositive : 0 < blockSize)
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    (circuit function blockSize).eval DeMorgan.interpretation input 0 =
      function input := by
  rw [circuit, Circuit.eval_comp, Circuit.eval_comp,
    DeMorgan.Expression.circuit_eval]
  apply Bool.eq_iff_iff.mpr
  rw [synthesisExpression, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff]
  constructor
  · rintro ⟨flat, flatTrue⟩
    let pair := (finProdFinEquiv :
      Fin (blockCount addressWidth blockSize) ×
        Fin (patternCount blockSize) ≃
          Fin (bankWidth addressWidth blockSize)).symm flat
    let block := pair.1
    let pattern := pair.2
    have flatEquality : finProdFinEquiv (block, pattern) = flat := by
      exact (finProdFinEquiv :
        Fin (blockCount addressWidth blockSize) ×
          Fin (patternCount blockSize) ≃
            Fin (bankWidth addressWidth blockSize)).apply_symm_apply flat
    rw [matchingPatternTerm, DeMorgan.Expression.eval,
      Bool.and_eq_true, ← flatEquality] at flatTrue
    simp only [DeMorgan.Expression.eval] at flatTrue
    have leftTrue := flatTrue.1
    have rightTrue := flatTrue.2
    rw [patternBankCircuit_eval_left, splitMintermCircuit_eval] at leftTrue
    simp only [Fin.append_left] at leftTrue
    rw [patternBankCircuit_eval_right, splitMintermCircuit_eval] at rightTrue
    simp only [Fin.append_right] at rightTrue
    obtain ⟨offset, rowValid, rowSelected, patternTrue⟩ :=
      (leftExpression_eval_minterms_true_iff
        addressWidth blockSize block pattern
          (addressInput dataWidth input)).mp leftTrue
    rw [rightExpression_eval_minterms] at rightTrue
    have selectedPattern :
        blockPattern function block
            (bitVectorEquiv dataWidth (dataInput addressWidth input)) =
          pattern :=
      of_decide_eq_true rightTrue
    rw [← selectedPattern, assignmentBits_blockPattern] at patternTrue
    unfold blockColumn at patternTrue
    simp only [dif_pos rowValid] at patternTrue
    rw [rowSelected, assignmentBits_bitVectorEquiv,
      assignmentBits_bitVectorEquiv] at patternTrue
    rw [append_addressInput_dataInput] at patternTrue
    exact patternTrue
  · intro functionTrue
    let address := bitVectorEquiv addressWidth (addressInput dataWidth input)
    let data := bitVectorEquiv dataWidth (dataInput addressWidth input)
    let block := selectedBlock (addressWidth := addressWidth)
      blockSizePositive address
    let offset := selectedOffset blockSizePositive address
    let pattern := blockPattern function block data
    let flat : Fin (bankWidth addressWidth blockSize) :=
      finProdFinEquiv (block, pattern)
    have rowEquality :
        block.val * blockSize + offset.val = address.val := by
      simpa [block, offset, selectedBlock, selectedOffset] using
        Nat.div_add_mod' address.val blockSize
    have rowValid :
        block.val * blockSize + offset.val < 2 ^ addressWidth := by
      simpa only [rowEquality] using address.isLt
    have rowSelected :
        (⟨block.val * blockSize + offset.val, rowValid⟩ :
            Fin (2 ^ addressWidth)) = address := by
      apply Fin.ext
      exact rowEquality
    have patternTrue :
        assignmentBits blockSize pattern offset = true := by
      rw [show pattern = blockPattern function block data by rfl,
        assignmentBits_blockPattern]
      unfold blockColumn
      simp only [dif_pos rowValid]
      rw [rowSelected]
      have addressDecoded : assignmentBits addressWidth address =
          addressInput dataWidth input := by
        exact assignmentBits_bitVectorEquiv _
      have dataDecoded : assignmentBits dataWidth data =
          dataInput addressWidth input := by
        exact assignmentBits_bitVectorEquiv _
      rw [addressDecoded, dataDecoded, append_addressInput_dataInput]
      exact functionTrue
    refine ⟨flat, ?_⟩
    rw [matchingPatternTerm, DeMorgan.Expression.eval, Bool.and_eq_true]
    constructor
    · dsimp only [flat]
      simp only [DeMorgan.Expression.eval]
      rw [patternBankCircuit_eval_left, splitMintermCircuit_eval]
      simp only [Fin.append_left]
      apply (leftExpression_eval_minterms_true_iff
        addressWidth blockSize block pattern
          (addressInput dataWidth input)).mpr
      exact ⟨offset, rowValid, rowSelected, patternTrue⟩
    · dsimp only [flat]
      simp only [DeMorgan.Expression.eval]
      rw [patternBankCircuit_eval_right, splitMintermCircuit_eval]
      simp only [Fin.append_right]
      rw [rightExpression_eval_minterms]
      exact decide_eq_true rfl

theorem circuit_computes
    (blockSizePositive : 0 < blockSize)
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    (circuit function blockSize).Computes DeMorgan.interpretation
      (scalarTarget function) := by
  intro input
  funext output
  have outputZero : output = 0 := Fin.eq_zero output
  subst output
  exact circuit_eval blockSizePositive function input

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
    (inputs : Nat) : UhligRecursion.ScalarSynthesis inputs where
  gateCount function :=
    synthesisGateCount
      (reindexFunction (lupanovAddressDataSum inputs) function)
      (lupanovBlockSize inputs)
  circuit := lupanovCircuit inputs
  computes := lupanovCircuit_computes inputs

/-- The Lupanov family as explicit dependent data, not a typeclass. -/
noncomputable def lupanovFamily : UhligTheorem.ScalarSynthesisFamily :=
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
