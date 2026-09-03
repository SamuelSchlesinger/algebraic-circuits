import Algebraic.MassProduction.SortingNetwork
import Mathlib.Data.List.OfFn

/-!
# Semantic model of Batcher sorting networks

This is the record-level semantic layer used to prove that the explicit
Boolean circuit sorts complete records by a projected key.
-/

namespace Algebraic
namespace MassProduction
namespace Sorting
namespace Semantics

/-- Four-point lattice characterization of a bitonic sequence. -/
def SequenceBitonic {n : ℕ} [LinearOrder α] (sequence : Fin n → α) : Prop :=
  ∀ i j k l, i < j → j < k → k < l →
    min (sequence i) (sequence k) ≤ max (sequence j) (sequence l) ∧
      min (sequence j) (sequence l) ≤ max (sequence i) (sequence k)

/-- A sequence is increasing in its index order. -/
def SequenceIncreasing [LE α] {n : ℕ} (sequence : Fin n → α) : Prop :=
  ∀ i j, i < j → sequence i ≤ sequence j

/-- A sequence is decreasing in its index order. -/
def SequenceDecreasing [LE α] {n : ℕ} (sequence : Fin n → α) : Prop :=
  ∀ i j, i < j → sequence j ≤ sequence i

/-- Sortedness in the selected direction. -/
def SequenceSorted [LE α] {n : ℕ}
    (ascending : Bool) (sequence : Fin n → α) : Prop :=
  if ascending then SequenceIncreasing sequence
  else SequenceDecreasing sequence

/-- Every value of the first sequence is at most every value of the second. -/
def SequenceAllLE [LE α] {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α) : Prop :=
  ∀ i j, first i ≤ second j

/-- Every output value occurs somewhere in the input sequence. -/
def SequenceRangeContained {n m : ℕ}
    (output : Fin n → α) (input : Fin m → α) : Prop :=
  ∀ i, ∃ j, output i = input j

/-- The output sequence is a permutation of the input sequence. -/
def SequencePermutes {n : ℕ}
    (output input : Fin n → α) : Prop :=
  (List.ofFn output).Perm (List.ofFn input)

namespace SequenceRangeContained

/-- Range containment is transitive. -/
theorem trans {n m k : ℕ}
    {first : Fin n → α} {second : Fin m → α} {third : Fin k → α}
    (hfirst : SequenceRangeContained first second)
    (hsecond : SequenceRangeContained second third) :
    SequenceRangeContained first third := by
  intro i
  obtain ⟨j, hj⟩ := hfirst i
  obtain ⟨k, hk⟩ := hsecond j
  exact ⟨k, hj.trans hk⟩

end SequenceRangeContained

namespace SequencePermutes

/-- Every finite sequence is a permutation of itself. -/
theorem refl {n : ℕ} (input : Fin n → α) :
    SequencePermutes input input :=
  List.Perm.refl _

/-- Sequence permutation is transitive. -/
theorem trans {n : ℕ}
    {first second third : Fin n → α}
    (hfirst : SequencePermutes first second)
    (hsecond : SequencePermutes second third) :
    SequencePermutes first third :=
  List.Perm.trans hfirst hsecond

/-- Applying the same observation to two permuted finite sequences preserves
their permutation relation. -/
theorem map {n : ℕ} {output input : Fin n → α}
    (observe : α → β)
    (permuted : SequencePermutes output input) :
    SequencePermutes
      (fun index => observe (output index))
      (fun index => observe (input index)) := by
  unfold SequencePermutes at permuted ⊢
  rw [List.ofFn_comp' output observe, List.ofFn_comp' input observe]
  exact permuted.map observe

/-- Every output of a finite-sequence permutation is an input value. -/
theorem rangeContained {n : ℕ} {output input : Fin n -> α}
    (permuted : SequencePermutes output input) :
    SequenceRangeContained output input := by
  intro outputIndex
  have outputMember : output outputIndex ∈ List.ofFn output :=
    (List.mem_ofFn' output (output outputIndex)).mpr
      ⟨outputIndex, rfl⟩
  have inputMember : output outputIndex ∈ List.ofFn input :=
    permuted.mem_iff.mp outputMember
  obtain ⟨inputIndex, equality⟩ :=
    (List.mem_ofFn' input (output outputIndex)).mp inputMember
  exact ⟨inputIndex, equality.symm⟩

end SequencePermutes

/-- Concatenation of two finite sequences. -/
def appendSequence {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α) : Fin (n + m) → α :=
  Fin.append first second

namespace SequencePermutes

/-- Concatenating two pairs of permuted sequences preserves permutation. -/
theorem append {n m : ℕ}
    {first firstInput : Fin n → α} {second secondInput : Fin m → α}
    (hfirst : SequencePermutes first firstInput)
    (hsecond : SequencePermutes second secondInput) :
    SequencePermutes (appendSequence first second)
      (appendSequence firstInput secondInput) := by
  unfold SequencePermutes appendSequence at *
  simpa only [List.ofFn_fin_append] using hfirst.append hsecond

end SequencePermutes

/-- Pointwise minimum of equal-length sequences. -/
def pointwiseMin [LinearOrder α] {n : ℕ}
    (first second : Fin n → α) : Fin n → α :=
  fun i => min (first i) (second i)

/-- Pointwise maximum of equal-length sequences. -/
def pointwiseMax [LinearOrder α] {n : ℕ}
    (first second : Fin n → α) : Fin n → α :=
  fun i => max (first i) (second i)

/-- First half of a record-level network sequence. -/
def recordFirstHalf {depth : ℕ}
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords depth) → α :=
  fun index => input (Fin.castAdd (networkRecords depth) index)

/-- Second half of a record-level network sequence. -/
def recordSecondHalf {depth : ℕ}
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords depth) → α :=
  fun index => input (Fin.natAdd (networkRecords depth) index)

/-- Join two record-level half sequences. -/
def joinRecordHalves {depth : ℕ}
    (first second : Fin (networkRecords depth) → α) :
    Fin (networkRecords (depth + 1)) → α :=
  Fin.append first second

/-- The record-specific and general sequence append operations agree. -/
theorem appendSequence_eq_joinRecordHalves {depth : Nat}
    (first second : Fin (networkRecords depth) -> α) :
    appendSequence first second = joinRecordHalves first second :=
  rfl

/-- One record-level butterfly layer over a linear order. -/
def orderedCompareLayer [LinearOrder α] (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords (depth + 1)) → α :=
  let first := recordFirstHalf input
  let second := recordSecondHalf input
  if ascending then
    joinRecordHalves (pointwiseMin first second) (pointwiseMax first second)
  else
    joinRecordHalves (pointwiseMax first second) (pointwiseMin first second)

/-- Record-level bitonic merge over a linear order. -/
def orderedBitonicMerge [LinearOrder α] :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let compared := orderedCompareLayer depth ascending input
      joinRecordHalves
        (orderedBitonicMerge depth ascending (recordFirstHalf compared))
        (orderedBitonicMerge depth ascending (recordSecondHalf compared))

/-- Record-level Batcher sorter over a linear order. -/
def orderedBitonicSort [LinearOrder α] :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let prepared := joinRecordHalves
        (orderedBitonicSort depth true (recordFirstHalf input))
        (orderedBitonicSort depth false (recordSecondHalf input))
      orderedBitonicMerge (depth + 1) ascending prepared

/-- Source record selected for one output of a keyed compare layer. -/
noncomputable def keyedCompareSource [LinearOrder κ] (key : α → κ)
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α)
    (output : Fin (networkRecords (depth + 1))) :
    Fin (networkRecords (depth + 1)) :=
  let half := networkRecords depth
  if hleft : output.val < half then
    let pair : Fin half := ⟨output.val, hleft⟩
    let shouldSwap :=
      key (input (Fin.natAdd half pair)) <
        key (input (Fin.castAdd half pair))
    let sourceRight := if ascending then shouldSwap else ¬shouldSwap
    if sourceRight then Fin.natAdd half pair else Fin.castAdd half pair
  else
    let pair : Fin half := ⟨output.val - half, by
      have hbound : output.val < half + half := by
        simpa only [half, networkRecords_succ] using output.isLt
      omega⟩
    let shouldSwap :=
      key (input (Fin.natAdd half pair)) <
        key (input (Fin.castAdd half pair))
    let sourceRight := if ascending then shouldSwap else ¬shouldSwap
    if sourceRight then Fin.castAdd half pair else Fin.natAdd half pair

/-- One compare layer on records ordered only through a separate key. -/
noncomputable def keyedCompareLayer [LinearOrder κ] (key : α → κ)
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords (depth + 1)) → α :=
  fun output => input (keyedCompareSource key depth ascending input output)

/-- Keyed record-level bitonic merge. -/
noncomputable def keyedBitonicMerge [LinearOrder κ] (key : α → κ) :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let compared := keyedCompareLayer key depth ascending input
      joinRecordHalves
        (keyedBitonicMerge key depth ascending (recordFirstHalf compared))
        (keyedBitonicMerge key depth ascending (recordSecondHalf compared))

/-- Keyed record-level Batcher sorter. -/
noncomputable def keyedBitonicSort [LinearOrder κ] (key : α → κ) :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let prepared := joinRecordHalves
        (keyedBitonicSort key depth true (recordFirstHalf input))
        (keyedBitonicSort key depth false (recordSecondHalf input))
      keyedBitonicMerge key (depth + 1) ascending prepared

end Semantics
end Sorting
end MassProduction
end Algebraic
