import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Support
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Occurrence

/-!
# Support profiles at arithmetic multiplication occurrences

For every rectangular split and every actual multiplication occurrence, count
the rows and columns supporting the catalecticant of that gate's product.  The
smaller count is a valid local rank budget.  Feeding this split-by-gate matrix
to the generic occurrence-profile theorem gives weighted Fusion bounds.

The witness-oriented API accepts any certified row and column covers.  The
canonical API specializes it to the exact sets of nonzero rows and columns.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Profile
namespace Support

noncomputable section

variable {K : Type} {C : Type}

/-- Polynomial produced at one evaluated multiplication occurrence. -/
def occurrenceProduct
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (index : Fin
      (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length) : MvPolynomial (Fin degree) K :=
  Rectangular.Decomposition.multiplicationOutput constant degree circuit index

/-- A split-by-occurrence family of finite sets covering every nonzero row. -/
def RowsAtOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (rows : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1)) : Prop :=
  ∀ split index,
    Rectangular.Support.RowsSupportedOn degree split.1
      (occurrenceProduct constant degree circuit index) (rows split index)

/-- A split-by-occurrence family of finite sets covering every nonzero
column. -/
def ColumnsAtOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (columns : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1)) : Prop :=
  ∀ split index,
    Rectangular.Support.ColumnsSupportedOn degree split.1
      (occurrenceProduct constant degree circuit index) (columns split index)

/-- Local budget supplied by row covers. -/
def rowBudget
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (rows : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1))
    (split : Fin (degree + 1))
    (index : Fin
      (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length) : Nat :=
  (rows split index).card

/-- Local budget supplied by column covers. -/
def columnBudget
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (columns : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1))
    (split : Fin (degree + 1))
    (index : Fin
      (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length) : Nat :=
  (columns split index).card

/-- Local budget supplied by simultaneous row and column covers. -/
def coverBudget
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (rows columns : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1))
    (split : Fin (degree + 1))
    (index : Fin
      (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length) : Nat :=
  min (rows split index).card (columns split index).card

/-- Certified row covers induce a valid split-by-occurrence rank matrix. -/
theorem indexedBound_of_rows
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (rows : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1))
    (supported : RowsAtOccurrences constant degree circuit rows) :
    Occurrence.IndexedBound constant degree degreeAtLeastTwo circuit
      (rowBudget constant degree circuit rows) := by
  intro split index
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split.1
      (occurrenceProduct constant degree circuit index)) ≤
        (rows split index).card
  exact Rectangular.Support.feature_rank_le_card_rows degree split.1
    (occurrenceProduct constant degree circuit index) (rows split index)
    (supported split index)

/-- Certified column covers induce a valid split-by-occurrence rank matrix. -/
theorem indexedBound_of_columns
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (columns : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1))
    (supported : ColumnsAtOccurrences constant degree circuit columns) :
    Occurrence.IndexedBound constant degree degreeAtLeastTwo circuit
      (columnBudget constant degree circuit columns) := by
  intro split index
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split.1
      (occurrenceProduct constant degree circuit index)) ≤
        (columns split index).card
  exact Rectangular.Support.feature_rank_le_card_columns degree split.1
    (occurrenceProduct constant degree circuit index) (columns split index)
    (supported split index)

/-- Simultaneous row and column covers induce their pointwise minimum rank
matrix. -/
theorem indexedBound_of_covers
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (rows columns : (split : Fin (degree + 1)) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length →
      Finset (SumOfTerms.MatrixRank.Layer degree split.1))
    (rowsSupported : RowsAtOccurrences constant degree circuit rows)
    (columnsSupported : ColumnsAtOccurrences constant degree circuit columns) :
    Occurrence.IndexedBound constant degree degreeAtLeastTwo circuit
      (coverBudget constant degree circuit rows columns) := by
  intro split index
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split.1
      (occurrenceProduct constant degree circuit index)) ≤
        min (rows split index).card (columns split index).card
  exact Rectangular.Support.feature_rank_le_min_card degree split.1
    (occurrenceProduct constant degree circuit index) (rows split index)
    (columns split index) (rowsSupported split index)
    (columnsSupported split index)

/-- Exact nonzero-row support at each split and occurrence. -/
def canonicalRows
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (split : Fin (degree + 1))
    (index : Fin
      (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length) :
    Finset (SumOfTerms.MatrixRank.Layer degree split.1) :=
  Rectangular.Support.rowSupport degree split.1
    (occurrenceProduct constant degree circuit index)

/-- Exact nonzero-column support at each split and occurrence. -/
def canonicalColumns
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (split : Fin (degree + 1))
    (index : Fin
      (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length) :
    Finset (SumOfTerms.MatrixRank.Layer degree split.1) :=
  Rectangular.Support.columnSupport degree split.1
    (occurrenceProduct constant degree circuit index)

/-- Canonical pointwise support-size rank matrix. -/
def canonicalBudget
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (split : Fin (degree + 1))
    (index : Fin
      (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length) : Nat :=
  Rectangular.Support.rankBudget degree split.1
    (occurrenceProduct constant degree circuit index)

theorem canonicalRows_supported
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1) :
    RowsAtOccurrences constant degree circuit
      (canonicalRows constant degree circuit) := by
  intro split index
  exact Rectangular.Support.rowsSupportedOn_rowSupport degree split.1
    (occurrenceProduct constant degree circuit index)

theorem canonicalColumns_supported
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1) :
    ColumnsAtOccurrences constant degree circuit
      (canonicalColumns constant degree circuit) := by
  intro split index
  exact Rectangular.Support.columnsSupportedOn_columnSupport degree split.1
    (occurrenceProduct constant degree circuit index)

/-- The exact support counts form a valid split-by-occurrence rank matrix for
every arithmetic circuit. -/
theorem canonicalIndexedBound
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1) :
    Occurrence.IndexedBound constant degree degreeAtLeastTwo circuit
      (canonicalBudget constant degree circuit) := by
  intro split index
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split.1
      (occurrenceProduct constant degree circuit index)) ≤
        Rectangular.Support.rankBudget degree split.1
          (occurrenceProduct constant degree circuit index)
  exact Rectangular.Support.feature_rank_le_rankBudget degree split.1
    (occurrenceProduct constant degree circuit index)

/-- Weighted rectangular target rank is bounded by the sum of the exact
support budgets of the actual multiplication occurrences. -/
theorem weightedTargetRank_le_sum_canonicalGateBudget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (weight : Fin (degree + 1) → Nat) :
    Occurrence.weightedTargetRank degree weight ≤
      ∑ index, Occurrence.weightedGateBudget degree weight
        (canonicalBudget constant degree circuit) index :=
  Occurrence.weightedTargetRank_le_sum_gateBudget constant degree
    degreeAtLeastTwo circuit constructs weight
    (canonicalBudget constant degree circuit)
    (canonicalIndexedBound constant degree degreeAtLeastTwo circuit)

/-- If every gate has aggregate weighted support at most `gateBudget`, the
weighted target divided by that budget lower-bounds multiplication cost. -/
theorem weighted_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (weight : Fin (degree + 1) → Nat)
    (gateBudget : Nat)
    (gateBudgetPositive : 0 < gateBudget)
    (aggregateBound : ∀ index,
      Occurrence.weightedGateBudget degree weight
        (canonicalBudget constant degree circuit) index ≤ gateBudget) :
    Occurrence.weightedTargetRank degree weight ⌈/⌉ gateBudget ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Occurrence.weighted_ceilDiv_lowerBound constant degree degreeAtLeastTwo
    circuit constructs weight (canonicalBudget constant degree circuit)
    (canonicalIndexedBound constant degree degreeAtLeastTwo circuit)
    gateBudget gateBudgetPositive aggregateBound

/-- Some actual gate carries at least the ceiling-average weighted support
budget whenever the weighted target is positive. -/
theorem exists_gateBudget_ge_weightedTarget_ceilDiv
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (weight : Fin (degree + 1) → Nat)
    (targetPositive : 0 < Occurrence.weightedTargetRank degree weight) :
    ∃ index,
      Occurrence.weightedTargetRank degree weight ⌈/⌉
          circuit.cost
            (Algebraic.Arithmetic.multiplicationCost (K := C)) ≤
        Occurrence.weightedGateBudget degree weight
          (canonicalBudget constant degree circuit) index :=
  Occurrence.exists_gateBudget_ge_weightedTarget_ceilDiv constant degree
    degreeAtLeastTwo circuit constructs weight
    (canonicalBudget constant degree circuit)
    (canonicalIndexedBound constant degree degreeAtLeastTwo circuit)
    targetPositive

end
end Support
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
