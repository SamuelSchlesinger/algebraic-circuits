import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Decomposition
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Occurrence

/-!
# Split-by-occurrence rectangular rank budgets

Keep the two useful nonuniformities simultaneously: catalecticant split `k`
and multiplication occurrence `g`.  A rank matrix `r k g` gives one Fusion
constraint per split.  Nonnegative integer weights then combine them into

`sum_k w_k choose(d,k) ≤ sum_g sum_k w_k r(k,g)`.

If every gate has aggregate weighted rank at most `B`, this yields the single
cost bound `ceil(weighted target / B) ≤ multiplication cost`.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Profile
namespace Occurrence

noncomputable section

variable {K : Type} {C : Type}

/-- A local rank budget indexed by both rectangular split and actual
multiplication occurrence. -/
def IndexedBound
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat) : Prop :=
  ∀ split,
    Rank.Occurrence.IndexedBound
      (certificate constant degree split.1 degreeAtLeastTwo) circuit
      (budget split)

/-- Each row of a split-by-occurrence budget satisfies its own rectangular
Fusion inequality. -/
theorem choose_le_sum_budget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (bound : IndexedBound constant degree degreeAtLeastTwo circuit budget)
    (split : Fin (degree + 1)) :
    Nat.choose degree split.1 ≤ ∑ index, budget split index :=
  Rank.Occurrence.targetRank_le_sum_indexedBudget
    (certificate constant degree split.1 degreeAtLeastTwo)
    (Nat.choose degree split.1)
    (SumOfTerms.Waring.Rectangular.target_rank_ge degree split.1)
    circuit constructs (budget split) (bound split)

/-- Weighted target rank across all rectangular splits. -/
def weightedTargetRank
    (degree : Nat)
    (weight : Fin (degree + 1) → Nat) : Nat :=
  ∑ split, weight split * Nat.choose degree split.1

/-- Aggregate weighted local rank charged to one multiplication occurrence. -/
def weightedGateBudget
    (degree : Nat)
    {occurrenceCount : Nat}
    (weight : Fin (degree + 1) → Nat)
    (budget : Fin (degree + 1) → Fin occurrenceCount → Nat)
    (index : Fin occurrenceCount) : Nat :=
  ∑ split, weight split * budget split index

/-- Weighted sum of all target-rank constraints is bounded by the sum of the
weighted budgets over actual gates. -/
theorem weightedTargetRank_le_sum_gateBudget
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
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (bound : IndexedBound constant degree degreeAtLeastTwo circuit budget) :
    weightedTargetRank degree weight ≤
      ∑ index, weightedGateBudget degree weight budget index := by
  unfold weightedTargetRank weightedGateBudget
  calc
    (∑ split, weight split * Nat.choose degree split.1) ≤
        ∑ split, weight split * ∑ index, budget split index := by
      apply Finset.sum_le_sum
      intro split _
      exact Nat.mul_le_mul_left (weight split)
        (choose_le_sum_budget constant degree degreeAtLeastTwo circuit
          constructs budget bound split)
    _ = ∑ index, ∑ split, weight split * budget split index := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

/-- A uniform upper bound on each gate's weighted aggregate rank yields an
undivided target-rank/cost tradeoff. -/
theorem weightedTargetRank_le_cost_mul_gateBudget
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
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (bound : IndexedBound constant degree degreeAtLeastTwo circuit budget)
    (gateBudget : Nat)
    (aggregateBound : ∀ index,
      weightedGateBudget degree weight budget index ≤ gateBudget) :
    weightedTargetRank degree weight ≤
      circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        gateBudget := by
  calc
    weightedTargetRank degree weight ≤
        ∑ index, weightedGateBudget degree weight budget index :=
      weightedTargetRank_le_sum_gateBudget constant degree degreeAtLeastTwo
        circuit constructs weight budget bound
    _ ≤ ∑ _index : Fin
          (Rectangular.Decomposition.multiplicationOccurrences constant degree
            circuit).length, gateBudget := by
      apply Finset.sum_le_sum
      intro index _
      exact aggregateBound index
    _ = circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) * gateBudget := by
      simp [Rectangular.Decomposition.multiplicationOccurrences_length]

/-- Ceiling-divided weighted profile lower bound. -/
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
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (bound : IndexedBound constant degree degreeAtLeastTwo circuit budget)
    (gateBudget : Nat)
    (gateBudgetPositive : 0 < gateBudget)
    (aggregateBound : ∀ index,
      weightedGateBudget degree weight budget index ≤ gateBudget) :
    weightedTargetRank degree weight ⌈/⌉ gateBudget ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  (ceilDiv_le_iff_le_mul gateBudgetPositive).2
    (by
      simpa [Nat.mul_comm] using
        (weightedTargetRank_le_cost_mul_gateBudget constant degree
          degreeAtLeastTwo circuit constructs weight budget bound gateBudget
          aggregateBound))

/-- Concentration form: some actual multiplication gate carries at least the
ceiling-average weighted profile budget. -/
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
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (bound : IndexedBound constant degree degreeAtLeastTwo circuit budget)
    (targetPositive : 0 < weightedTargetRank degree weight) :
    ∃ index,
      weightedTargetRank degree weight ⌈/⌉
          circuit.cost
            (Algebraic.Arithmetic.multiplicationCost (K := C)) ≤
        weightedGateBudget degree weight budget index := by
  simpa [Rectangular.Decomposition.multiplicationOccurrences_length] using
    Rank.Occurrence.exists_budget_ge_ceilDiv
      (weightedTargetRank degree weight) targetPositive
      (weightedGateBudget degree weight budget)
      (weightedTargetRank_le_sum_gateBudget constant degree degreeAtLeastTwo
        circuit constructs weight budget bound)

end
end Occurrence
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
