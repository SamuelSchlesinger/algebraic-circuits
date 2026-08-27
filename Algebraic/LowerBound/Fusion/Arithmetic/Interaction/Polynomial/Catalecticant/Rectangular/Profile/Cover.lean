import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Cover
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Block

/-!
# Weighted two-dimensional covers at multiplication occurrences

At each rectangular split and each actual multiplication gate, provide a
rectangle cover of the gate-product catalecticant.  Its weighted size
`∑ min(|R|,|C|)` becomes the local rank matrix used by the generic weighted
Fusion theorem.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Profile
namespace Cover

noncomputable section

variable {K : Type} {C : Type}

/-- Every split/gate catalecticant has a rectangle cover within its assigned
weighted budget. -/
def AtOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat) : Prop :=
  ∀ split index,
    Rectangular.Cover.RankAtMost degree split.1
      (Profile.Support.occurrenceProduct constant degree circuit index)
      (budget split index)

/-- Rectangle covers induce the supported-block hypotheses expected by the
block profile adapter. -/
theorem blockAtOccurrences_of_atOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (covered : AtOccurrences constant degree circuit budget) :
    Profile.Block.AtOccurrences constant degree circuit budget := by
  intro split index
  exact Rectangular.Cover.blockRankAtMost_of_rankAtMost degree split.1
    (Profile.Support.occurrenceProduct constant degree circuit index)
    (budget split index) (covered split index)

/-- A split-by-gate rectangle-cover budget is a valid Fusion rank matrix. -/
theorem indexedBound_of_atOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (covered : AtOccurrences constant degree circuit budget) :
    Occurrence.IndexedBound constant degree degreeAtLeastTwo circuit budget :=
  Profile.Block.indexedBound_of_atOccurrences constant degree degreeAtLeastTwo
    circuit budget
    (blockAtOccurrences_of_atOccurrences constant degree circuit budget
      covered)

/-- Weighted target rank is bounded by the sum of weighted rectangle-cover
budgets over actual multiplication gates. -/
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
    (covered : AtOccurrences constant degree circuit budget) :
    Occurrence.weightedTargetRank degree weight ≤
      ∑ index, Occurrence.weightedGateBudget degree weight budget index :=
  Profile.Block.weightedTargetRank_le_sum_gateBudget constant degree
    degreeAtLeastTwo circuit constructs weight budget
    (blockAtOccurrences_of_atOccurrences constant degree circuit budget
      covered)

/-- If each gate's aggregate weighted cover size is at most `gateBudget`, the
weighted target ratio lower-bounds multiplication cost. -/
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
    (covered : AtOccurrences constant degree circuit budget)
    (gateBudget : Nat)
    (gateBudgetPositive : 0 < gateBudget)
    (aggregateBound : ∀ index,
      Occurrence.weightedGateBudget degree weight budget index ≤
        gateBudget) :
    Occurrence.weightedTargetRank degree weight ⌈/⌉ gateBudget ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Profile.Block.weighted_ceilDiv_lowerBound constant degree degreeAtLeastTwo
    circuit constructs weight budget
    (blockAtOccurrences_of_atOccurrences constant degree circuit budget
      covered)
    gateBudget gateBudgetPositive aggregateBound

/-- Positive target weight forces one gate to carry at least the
ceiling-average rectangle-cover budget. -/
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
    (covered : AtOccurrences constant degree circuit budget)
    (targetPositive : 0 < Occurrence.weightedTargetRank degree weight) :
    ∃ index,
      Occurrence.weightedTargetRank degree weight ⌈/⌉
          circuit.cost
            (Algebraic.Arithmetic.multiplicationCost (K := C)) ≤
        Occurrence.weightedGateBudget degree weight budget index :=
  Profile.Block.exists_gateBudget_ge_weightedTarget_ceilDiv constant degree
    degreeAtLeastTwo circuit constructs weight budget
    (blockAtOccurrences_of_atOccurrences constant degree circuit budget
      covered)
    targetPositive

end
end Cover
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
