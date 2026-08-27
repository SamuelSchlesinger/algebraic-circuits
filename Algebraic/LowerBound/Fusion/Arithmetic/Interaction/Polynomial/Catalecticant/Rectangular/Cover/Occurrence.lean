import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Cover
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Decomposition
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Occurrence

/-!
# Rectangle-cover budgets at one catalecticant split

At a fixed split `k`, assign each actual multiplication occurrence a weighted
rectangle-cover budget.  The generic occurrence-indexed Fusion inequality then
gives

`choose d k ≤ ∑_g budget(g)`.

The uniform specialization yields the direct arithmetic-circuit lower bound
`ceil(choose d k / r) ≤ multiplication cost`.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Cover
namespace Occurrence

noncomputable section

variable {K : Type} {C : Type}

/-- A weighted rectangle-cover budget for every actual multiplication
occurrence at one rectangular split. -/
def AtOccurrences
    [Field K]
    (constant : C → K)
    (degree split : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (Rectangular.Decomposition.multiplicationOccurrences
      constant degree circuit).length → Nat) : Prop :=
  ∀ index,
    Rectangular.Cover.RankAtMost degree split
      (Rectangular.Decomposition.multiplicationOutput constant degree circuit
        index)
      (budget index)

/-- Fixed-split cover budgets induce an occurrence-indexed rank bound. -/
theorem indexedBound_of_atOccurrences
    [Field K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (Rectangular.Decomposition.multiplicationOccurrences
      constant degree circuit).length → Nat)
    (covered : AtOccurrences constant degree split circuit budget) :
    Rank.Occurrence.IndexedBound
      (certificate constant degree split degreeAtLeastTwo) circuit budget := by
  intro index
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split
      (Rectangular.Decomposition.multiplicationOutput constant degree circuit
        index)) ≤ budget index
  exact Rectangular.Cover.feature_rank_le degree split
    (Rectangular.Decomposition.multiplicationOutput constant degree circuit
      index)
    (budget index) (covered index)

/-- Target rank is at most the sum of the per-occurrence cover budgets. -/
theorem choose_le_sum_budget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (budget : Fin (Rectangular.Decomposition.multiplicationOccurrences
      constant degree circuit).length → Nat)
    (covered : AtOccurrences constant degree split circuit budget) :
    Nat.choose degree split ≤ ∑ index, budget index :=
  Rank.Occurrence.targetRank_le_sum_indexedBudget
    (certificate constant degree split degreeAtLeastTwo)
    (Nat.choose degree split)
    (SumOfTerms.Waring.Rectangular.target_rank_ge degree split)
    circuit constructs budget
    (indexedBound_of_atOccurrences constant degree split degreeAtLeastTwo
      circuit budget covered)

/-- Uniform weighted cover size at a fixed split gives a direct
multiplication-cost lower bound. -/
theorem choose_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (coverBudget : Nat)
    (coverBudgetPositive : 0 < coverBudget)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (covered : AtOccurrences constant degree split circuit
      (fun _ ↦ coverBudget)) :
    Nat.choose degree split ⌈/⌉ coverBudget ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply (ceilDiv_le_iff_le_mul coverBudgetPositive).2
  simpa [Rectangular.Decomposition.multiplicationOccurrences_length,
    Nat.mul_comm] using
    (choose_le_sum_budget constant degree split degreeAtLeastTwo circuit
      constructs (fun _ ↦ coverBudget) covered)

/-- If the chosen target layer is nonempty, some gate has at least the
ceiling-average rectangle-cover budget. -/
theorem exists_budget_ge_choose_ceilDiv
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (splitLe : split ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (budget : Fin (Rectangular.Decomposition.multiplicationOccurrences
      constant degree circuit).length → Nat)
    (covered : AtOccurrences constant degree split circuit budget) :
    ∃ index,
      Nat.choose degree split ⌈/⌉
          circuit.cost
            (Algebraic.Arithmetic.multiplicationCost (K := C)) ≤
        budget index := by
  simpa [Rectangular.Decomposition.multiplicationOccurrences_length] using
    Rank.Occurrence.exists_budget_ge_ceilDiv
      (Nat.choose degree split) (Nat.choose_pos splitLe) budget
      (choose_le_sum_budget constant degree split degreeAtLeastTwo circuit
        constructs budget covered)

end
end Occurrence
end Cover
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
