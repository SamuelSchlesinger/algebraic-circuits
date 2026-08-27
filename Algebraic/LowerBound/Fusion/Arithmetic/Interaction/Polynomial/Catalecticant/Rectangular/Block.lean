import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Support
import Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Block

/-!
# Block-decomposable rectangular catalecticants

A polynomial has block budget at most `r` when its rectangular catalecticant
is a finite sum of row/column-supported blocks whose smaller-side sizes sum to
at most `r`.  This strictly separates the structural witness from the generic
rank argument and from the circuit-level Fusion theorem.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Block

noncomputable section

variable {K : Type}

/-- A block decomposition of one polynomial's rectangular catalecticant. -/
abbrev Decomposition
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :=
  SumOfTerms.MatrixRank.Block.Decomposition
    (SumOfTerms.Waring.Rectangular.catalecticant K degree split polynomial)

/-- Existence of a supported-block decomposition with total budget at most
`budget`. -/
def RankAtMost
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (budget : Nat) : Prop :=
  ∃ decomposition : Decomposition degree split polynomial,
    decomposition.rankBudget ≤ budget

/-- A concrete block decomposition bounds the rectangular feature rank. -/
theorem feature_rank_le_decompositionBudget
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (decomposition : Decomposition degree split polynomial) :
    LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
      decomposition.rankBudget := by
  change LinearMap.rank
    (Matrix.toLin'
      (SumOfTerms.Waring.Rectangular.catalecticant K degree split
        polynomial)) ≤ decomposition.rankBudget
  exact decomposition.rank_toLin'_le_rankBudget

/-- The existential structural predicate compiles to a feature-rank bound. -/
theorem feature_rank_le
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (budget : Nat)
    (decomposes : RankAtMost degree split polynomial budget) :
    LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
      budget := by
  obtain ⟨decomposition, budgetBound⟩ := decomposes
  exact (feature_rank_le_decompositionBudget degree split polynomial
    decomposition).trans (by exact_mod_cast budgetBound)

/-- Exact row/column support is the canonical one-block decomposition. -/
theorem rankAtMost_supportBudget
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :
    RankAtMost degree split polynomial
      (Rectangular.Support.rankBudget degree split polynomial) := by
  refine ⟨SumOfTerms.MatrixRank.Block.Decomposition.single _, ?_⟩
  simp [Rectangular.Support.rankBudget, Rectangular.Support.rowSupport,
    Rectangular.Support.columnSupport]

/-- The zero polynomial has an empty block decomposition. -/
theorem zero_rankAtMost
    [Field K]
    (degree split budget : Nat) :
    RankAtMost degree split (0 : MvPolynomial (Fin degree) K) budget := by
  unfold RankAtMost Decomposition
  rw [map_zero]
  refine ⟨SumOfTerms.MatrixRank.Block.Decomposition.zero, ?_⟩
  rw [SumOfTerms.MatrixRank.Block.Decomposition.zero_rankBudget]
  exact Nat.zero_le budget

/-- Block budgets are additive under polynomial addition. -/
theorem add_rankAtMost
    [Field K]
    (degree split leftBudget rightBudget : Nat)
    (left right : MvPolynomial (Fin degree) K)
    (leftDecomposes : RankAtMost degree split left leftBudget)
    (rightDecomposes : RankAtMost degree split right rightBudget) :
    RankAtMost degree split (left + right) (leftBudget + rightBudget) := by
  obtain ⟨leftDecomposition, leftBound⟩ := leftDecomposes
  obtain ⟨rightDecomposition, rightBound⟩ := rightDecomposes
  have catalecticantAdd :
      SumOfTerms.Waring.Rectangular.catalecticant K degree split
          (left + right) =
        SumOfTerms.Waring.Rectangular.catalecticant K degree split left +
          SumOfTerms.Waring.Rectangular.catalecticant K degree split right := by
    exact map_add _ left right
  unfold RankAtMost Decomposition
  rw [catalecticantAdd]
  refine ⟨leftDecomposition.add rightDecomposition, ?_⟩
  rw [SumOfTerms.MatrixRank.Block.Decomposition.add_rankBudget]
  exact Nat.add_le_add leftBound rightBound

end
end Block
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
