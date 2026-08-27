import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular
import Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Support

/-!
# Row and column support of rectangular catalecticants

Support size is a split-sensitive structural upper bound on catalecticant
rank.  We expose both a witness-oriented interface, where clients provide
finite row and column covers, and a canonical interface that counts the
actual nonzero rows and columns.

The circuit-level Fusion adapter lives separately under `Profile.Support`.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Support

noncomputable section

variable {K : Type}

/-- The catalecticant has no nonzero row outside `rows`. -/
def RowsSupportedOn
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (rows : Finset (SumOfTerms.MatrixRank.Layer degree split)) : Prop :=
  Function.support
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial).row ⊆
    rows

/-- The catalecticant has no nonzero column outside `columns`. -/
def ColumnsSupportedOn
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (columns : Finset (SumOfTerms.MatrixRank.Layer degree split)) : Prop :=
  Function.support
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial).col ⊆
    columns

/-- A supplied row cover bounds the rank of the rectangular feature. -/
theorem feature_rank_le_card_rows
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (rows : Finset (SumOfTerms.MatrixRank.Layer degree split))
    (supported : RowsSupportedOn degree split polynomial rows) :
    LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
      rows.card := by
  change LinearMap.rank
    (Matrix.toLin'
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial)) ≤ rows.card
  exact
    SumOfTerms.MatrixRank.Support.rank_toLin'_le_card_of_rowSupport_subset
      _ rows supported

/-- A supplied column cover bounds the rank of the rectangular feature. -/
theorem feature_rank_le_card_columns
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (columns : Finset (SumOfTerms.MatrixRank.Layer degree split))
    (supported : ColumnsSupportedOn degree split polynomial columns) :
    LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
      columns.card := by
  change LinearMap.rank
    (Matrix.toLin'
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial)) ≤ columns.card
  exact
    SumOfTerms.MatrixRank.Support.rank_toLin'_le_card_of_columnSupport_subset
      _ columns supported

/-- Simultaneous row and column covers give their smaller cardinality as a
rank budget. -/
theorem feature_rank_le_min_card
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (rows columns : Finset (SumOfTerms.MatrixRank.Layer degree split))
    (rowsSupported : RowsSupportedOn degree split polynomial rows)
    (columnsSupported : ColumnsSupportedOn degree split polynomial columns) :
    LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
      min rows.card columns.card := by
  by_cases rowLe : rows.card ≤ columns.card
  · rw [min_eq_left rowLe]
    exact feature_rank_le_card_rows degree split polynomial rows rowsSupported
  · rw [min_eq_right (Nat.le_of_not_ge rowLe)]
    exact feature_rank_le_card_columns degree split polynomial columns
      columnsSupported

/-- Canonical finite set of nonzero catalecticant rows. -/
def rowSupport
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :
    Finset (SumOfTerms.MatrixRank.Layer degree split) :=
  SumOfTerms.MatrixRank.Support.rowSupport
    (SumOfTerms.Waring.Rectangular.catalecticant K degree split polynomial)

/-- Canonical finite set of nonzero catalecticant columns. -/
def columnSupport
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :
    Finset (SumOfTerms.MatrixRank.Layer degree split) :=
  SumOfTerms.MatrixRank.Support.columnSupport
    (SumOfTerms.Waring.Rectangular.catalecticant K degree split polynomial)

@[simp] theorem mem_rowSupport
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (row : SumOfTerms.MatrixRank.Layer degree split) :
    row ∈ rowSupport degree split polynomial ↔
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial).row row ≠ 0 := by
  exact SumOfTerms.MatrixRank.Support.mem_rowSupport _ _

@[simp] theorem mem_columnSupport
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (column : SumOfTerms.MatrixRank.Layer degree split) :
    column ∈ columnSupport degree split polynomial ↔
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial).col column ≠ 0 := by
  exact SumOfTerms.MatrixRank.Support.mem_columnSupport _ _

/-- The canonical support-size rank budget at one split. -/
def rankBudget
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) : Nat :=
  min (rowSupport degree split polynomial).card
    (columnSupport degree split polynomial).card

/-- The canonical support budget bounds the rectangular feature rank. -/
theorem feature_rank_le_rankBudget
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :
    LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
      rankBudget degree split polynomial := by
  change LinearMap.rank
    (Matrix.toLin'
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial)) ≤ _
  exact SumOfTerms.MatrixRank.Support.rank_toLin'_le_min_support _

end
end Support
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
