import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Block
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Support

/-!
# Block-decomposition profiles at multiplication occurrences

This adapter turns a split-by-gate family of structural block decompositions
into the rank matrix consumed by the generic weighted Fusion theorem.  The
decompositions may vary independently at every catalecticant split and every
actual multiplication occurrence.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Profile
namespace Block

noncomputable section

variable {K : Type} {C : Type}

/-- Every split/gate catalecticant admits a block decomposition within its
assigned budget. -/
def AtOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat) : Prop :=
  ∀ split index,
    Rectangular.Block.RankAtMost degree split.1
      (Profile.Support.occurrenceProduct constant degree circuit index)
      (budget split index)

/-- Structural block decompositions induce the corresponding
split-by-occurrence rank matrix. -/
theorem indexedBound_of_atOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (budget : Fin (degree + 1) →
      Fin (Rectangular.Decomposition.multiplicationOccurrences constant degree
        circuit).length → Nat)
    (restricted : AtOccurrences constant degree circuit budget) :
    Occurrence.IndexedBound constant degree degreeAtLeastTwo circuit budget := by
  intro split index
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split.1
      (Profile.Support.occurrenceProduct constant degree circuit index)) ≤
        budget split index
  exact Rectangular.Block.feature_rank_le degree split.1
    (Profile.Support.occurrenceProduct constant degree circuit index)
    (budget split index) (restricted split index)

/-- Canonical one-block row/column supports are a special case of block
decompositions. -/
theorem canonicalSupport_atOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1) :
    AtOccurrences constant degree circuit
      (Profile.Support.canonicalBudget constant degree circuit) := by
  intro split index
  exact Rectangular.Block.rankAtMost_supportBudget degree split.1
    (Profile.Support.occurrenceProduct constant degree circuit index)

/-- Weighted target rank is bounded by the sum of structural block budgets
over actual gates. -/
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
    (restricted : AtOccurrences constant degree circuit budget) :
    Occurrence.weightedTargetRank degree weight ≤
      ∑ index, Occurrence.weightedGateBudget degree weight budget index :=
  Occurrence.weightedTargetRank_le_sum_gateBudget constant degree
    degreeAtLeastTwo circuit constructs weight budget
    (indexedBound_of_atOccurrences constant degree degreeAtLeastTwo circuit
      budget restricted)

/-- A uniform upper bound on each gate's weighted block budget gives a
multiplication-cost lower bound. -/
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
    (restricted : AtOccurrences constant degree circuit budget)
    (gateBudget : Nat)
    (gateBudgetPositive : 0 < gateBudget)
    (aggregateBound : ∀ index,
      Occurrence.weightedGateBudget degree weight budget index ≤
        gateBudget) :
    Occurrence.weightedTargetRank degree weight ⌈/⌉ gateBudget ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Occurrence.weighted_ceilDiv_lowerBound constant degree degreeAtLeastTwo
    circuit constructs weight budget
    (indexedBound_of_atOccurrences constant degree degreeAtLeastTwo circuit
      budget restricted)
    gateBudget gateBudgetPositive aggregateBound

/-- Positive weighted target rank forces one actual multiplication gate to
carry at least the ceiling-average block budget. -/
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
    (restricted : AtOccurrences constant degree circuit budget)
    (targetPositive : 0 < Occurrence.weightedTargetRank degree weight) :
    ∃ index,
      Occurrence.weightedTargetRank degree weight ⌈/⌉
          circuit.cost
            (Algebraic.Arithmetic.multiplicationCost (K := C)) ≤
        Occurrence.weightedGateBudget degree weight budget index :=
  Occurrence.exists_gateBudget_ge_weightedTarget_ceilDiv constant degree
    degreeAtLeastTwo circuit constructs weight budget
    (indexedBound_of_atOccurrences constant degree degreeAtLeastTwo circuit
      budget restricted)
    targetPositive

end
end Block
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
