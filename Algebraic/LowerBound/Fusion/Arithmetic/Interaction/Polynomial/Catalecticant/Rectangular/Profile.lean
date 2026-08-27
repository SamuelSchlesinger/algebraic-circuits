import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular

/-!
# Rectangular catalecticant rank profiles

A single arithmetic circuit can have very different local interaction ranks at
different catalecticant splits.  This module records those bounds as a profile
`rₖ` and packages the strongest lower bound certified by any split:

`maxₖ ceil(choose d k / rₖ) ≤ multiplication cost`.

Keeping the profile separate from any particular source of local rank bounds
lets decomposition, restriction, and future shifted-flattening arguments share
the same comparison layer.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Profile

noncomputable section

variable {K : Type} {C : Type}

/-- A split-indexed family of local interaction-rank bounds for one circuit. -/
def LocalRankAtMost
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (localRank : Fin (degree + 1) → Nat) : Prop :=
  ∀ split,
    Rectangular.LocalRankAtMost constant degree split.1 degreeAtLeastTwo
      circuit (localRank split)

/-- The strongest cost lower bound supplied by a rectangular rank profile. -/
def certifiedLowerBound
    (degree : Nat)
    (localRank : Fin (degree + 1) → Nat) : Nat :=
  Finset.univ.sup fun split : Fin (degree + 1) ↦
    Nat.choose degree split.1 ⌈/⌉ localRank split

/-- Every individual split contributes a lower bound no larger than the best
profile bound. -/
theorem split_le_certifiedLowerBound
    (degree : Nat)
    (localRank : Fin (degree + 1) → Nat)
    (split : Fin (degree + 1)) :
    Nat.choose degree split.1 ⌈/⌉ localRank split ≤
      certifiedLowerBound degree localRank := by
  exact Finset.le_sup (f := fun index : Fin (degree + 1) ↦
    Nat.choose degree index.1 ⌈/⌉ localRank index) (Finset.mem_univ split)

/-- A profile hypothesis recovers the rectangular Fusion lower bound at each
chosen split. -/
theorem split_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (localRank : Fin (degree + 1) → Nat)
    (rankPositive : ∀ split, 0 < localRank split)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (profile : LocalRankAtMost constant degree degreeAtLeastTwo circuit
      localRank)
    (split : Fin (degree + 1)) :
    Nat.choose degree split.1 ⌈/⌉ localRank split ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Rectangular.choose_ceilDiv_lowerBound constant degree split.1
    degreeAtLeastTwo (localRank split) (rankPositive split) circuit constructs
    (profile split)

/-- The maximum over all rectangular splits is a certified multiplication-cost
lower bound. -/
theorem certifiedLowerBound_le_multiplicationCost
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (localRank : Fin (degree + 1) → Nat)
    (rankPositive : ∀ split, 0 < localRank split)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (profile : LocalRankAtMost constant degree degreeAtLeastTwo circuit
      localRank) :
    certifiedLowerBound degree localRank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Finset.sup_le
  intro split _
  exact split_lowerBound constant degree degreeAtLeastTwo localRank
    rankPositive circuit constructs profile split

end
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
