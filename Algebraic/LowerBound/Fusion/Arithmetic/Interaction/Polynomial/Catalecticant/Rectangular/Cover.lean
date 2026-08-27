import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Block
import Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Cover

/-!
# Rectangle covers of rectangular catalecticants

This is the polynomial-facing interface to weighted two-dimensional support
covers.  A cover may overlap; its weight is the sum over rectangles of the
smaller side.  The generic owner assignment turns it into a block
decomposition, and hence into a catalecticant-rank bound.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Cover

noncomputable section

variable {K : Type}

/-- Rectangle-cover certificate for one polynomial's catalecticant. -/
abbrev Certificate
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :=
  SumOfTerms.MatrixRank.Cover.Certificate
    (SumOfTerms.Waring.Rectangular.catalecticant K degree split polynomial)

/-- Existence of a rectangle cover whose weighted size is at most `budget`. -/
def RankAtMost
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (budget : Nat) : Prop :=
  ∃ certificate : Certificate degree split polynomial,
    certificate.rankBudget ≤ budget

/-- A rectangle-cover bound canonically induces the corresponding supported
block-decomposition bound. -/
theorem blockRankAtMost_of_rankAtMost
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (budget : Nat)
    (covered : RankAtMost degree split polynomial budget) :
    Rectangular.Block.RankAtMost degree split polynomial budget := by
  obtain ⟨certificate, budgetBound⟩ := covered
  refine ⟨certificate.toDecomposition, ?_⟩
  rw [certificate.toDecomposition_rankBudget]
  exact budgetBound

/-- Weighted rectangle-cover size bounds rectangular feature rank. -/
theorem feature_rank_le
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (budget : Nat)
    (covered : RankAtMost degree split polynomial budget) :
    LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
      budget :=
  Rectangular.Block.feature_rank_le degree split polynomial budget
    (blockRankAtMost_of_rankAtMost degree split polynomial budget covered)

/-- The exact nonzero row and column supports give a one-rectangle cover. -/
theorem rankAtMost_supportBudget
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :
    RankAtMost degree split polynomial
      (Rectangular.Support.rankBudget degree split polynomial) := by
  refine ⟨SumOfTerms.MatrixRank.Cover.Certificate.single _, ?_⟩
  simp [Rectangular.Support.rankBudget, Rectangular.Support.rowSupport,
    Rectangular.Support.columnSupport]

/-- The zero polynomial has an empty rectangle cover. -/
theorem zero_rankAtMost
    [Field K]
    (degree split budget : Nat) :
    RankAtMost degree split (0 : MvPolynomial (Fin degree) K) budget := by
  unfold RankAtMost Certificate
  rw [map_zero]
  refine ⟨SumOfTerms.MatrixRank.Cover.Certificate.zero, ?_⟩
  rw [SumOfTerms.MatrixRank.Cover.Certificate.zero_rankBudget]
  exact Nat.zero_le budget

end
end Cover
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
