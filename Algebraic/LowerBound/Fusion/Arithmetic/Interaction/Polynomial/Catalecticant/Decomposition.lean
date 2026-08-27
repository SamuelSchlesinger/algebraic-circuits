import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree

/-!
# Locally decomposable critical layers

Generalize the rank-one critical-layer restriction to multiplication outputs
whose degree-`2n` homogeneous component is a sum of `r` Waring terms.  Rank
subadditivity turns such a semantic decomposition into a local catalecticant
rank bound `r`, yielding the tradeoff

`centralBinom n / r ≤ multiplication cost`.

The `Fin r` presentation allows zero-scaled terms to pad shorter
decompositions, so it represents "at most `r`" terms over a field.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Decomposition

noncomputable section

open Cardinal

variable {K : Type} {C : Type}

/-- The critical homogeneous layer is a sum of at most `termCount` Waring
terms, with zero-scaled terms available as padding. -/
def AtMost
    [Field K]
    (n termCount : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K) : Prop :=
  ∃ terms : Fin termCount → SumOfTerms.Waring.Term K n,
    MvPolynomial.homogeneousComponent (2 * n) polynomial =
      ∑ index, SumOfTerms.Waring.termValue (terms index)

/-- The zero polynomial has an `r`-term decomposition for every `r`. -/
theorem zero_atMost
    [Field K]
    (n termCount : Nat) :
    AtMost n termCount (0 : MvPolynomial (Fin (2 * n)) K) := by
  let zeroTerm : SumOfTerms.Waring.Term K n :=
    { scale := 0
      coefficients := fun _ => 0 }
  refine ⟨fun _ => zeroTerm, ?_⟩
  simp [zeroTerm, SumOfTerms.Waring.termValue]

/-- Decomposition budgets add under polynomial addition. -/
theorem add
    [Field K]
    (n leftCount rightCount : Nat)
    (left right : MvPolynomial (Fin (2 * n)) K)
    (leftDecomposes : AtMost n leftCount left)
    (rightDecomposes : AtMost n rightCount right) :
    AtMost n (leftCount + rightCount) (left + right) := by
  obtain ⟨leftTerms, leftCritical⟩ := leftDecomposes
  obtain ⟨rightTerms, rightCritical⟩ := rightDecomposes
  refine ⟨Fin.addCases leftTerms rightTerms, ?_⟩
  rw [map_add, leftCritical, rightCritical, Fin.sum_univ_add]
  simp

/-- A decomposition can be padded by one zero-scaled Waring term. -/
theorem succ
    [Field K]
    (n termCount : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (decomposes : AtMost n termCount polynomial) :
    AtMost n (termCount + 1) polynomial := by
  obtain ⟨terms, critical⟩ := decomposes
  let zeroTerm : SumOfTerms.Waring.Term K n :=
    { scale := 0
      coefficients := fun _ => 0 }
  refine ⟨Fin.lastCases zeroTerm terms, ?_⟩
  rw [critical, Fin.sum_univ_castSucc]
  simp [zeroTerm, SumOfTerms.Waring.termValue]

/-- One critical-layer Waring term gives a one-term decomposition. -/
theorem atMost_one_of_term
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (term : SumOfTerms.Waring.Term K n)
    (critical : MvPolynomial.homogeneousComponent (2 * n) polynomial =
      SumOfTerms.Waring.termValue term) :
    AtMost n 1 polynomial := by
  refine ⟨fun _ => term, ?_⟩
  simpa using critical

/-- The earlier zero-or-one-power restriction is a one-term decomposition. -/
theorem atMost_one_of_criticalLayerOrPower
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (restricted :
      MvPolynomial.homogeneousComponent (2 * n) polynomial = 0 ∨
        ∃ term : SumOfTerms.Waring.Term K n,
          MvPolynomial.homogeneousComponent (2 * n) polynomial =
            SumOfTerms.Waring.termValue term) :
    AtMost n 1 polynomial := by
  rcases restricted with invisible | ⟨term, critical⟩
  · let zeroTerm : SumOfTerms.Waring.Term K n :=
      { scale := 0
        coefficients := fun _ => 0 }
    apply atMost_one_of_term n polynomial zeroTerm
    rw [invisible]
    simp [zeroTerm, SumOfTerms.Waring.termValue]
  · exact atMost_one_of_term n polynomial term critical

/-- An `r`-term critical-layer decomposition has catalecticant rank at most
`r`. -/
theorem feature_rank_le
    [Field K]
    [CharZero K]
    (n termCount : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (decomposes : AtMost n termCount polynomial) :
    LinearMap.rank (SumOfTerms.Waring.feature K n polynomial) ≤ termCount := by
  obtain ⟨terms, critical⟩ := decomposes
  rw [← Degree.feature_homogeneousComponent n polynomial, critical,
    map_sum]
  calc
    LinearMap.rank
        (∑ index, SumOfTerms.Waring.feature K n
          (SumOfTerms.Waring.termValue (terms index))) ≤
      ∑ index, LinearMap.rank
        (SumOfTerms.Waring.feature K n
          (SumOfTerms.Waring.termValue (terms index))) := by
        simpa using LinearMap.rank_finsetSum_le
          (Finset.univ : Finset (Fin termCount))
          (fun index => SumOfTerms.Waring.feature K n
            (SumOfTerms.Waring.termValue (terms index)))
    _ ≤ ∑ _index : Fin termCount, (1 : Cardinal) := by
      apply Finset.sum_le_sum
      intro index _
      exact SumOfTerms.Waring.term_rank_le_one (terms index)
    _ = termCount := by simp

/-- Circuit-local decomposition predicate for every multiplication output. -/
def AtMultiplications
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (termCount : Nat) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin (2 * n)) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature C)
      (MvPolynomial (Fin (2 * n)) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin (2 * n) →
            MvPolynomial (Fin (2 * n)) K) →
    AtMost n termCount
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- Local `r`-term decompositions imply the atom-level catalecticant rank
bound `r`. -/
theorem multiplicationOutputRankAtMost_of_atMultiplications
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (termCount : Nat)
    (restricted : AtMultiplications constant n circuit termCount) :
    MultiplicationOutputRankAtMost constant n positive circuit termCount := by
  intro arguments present
  change LinearMap.rank
    (SumOfTerms.Waring.feature K n
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))) ≤ termCount
  exact feature_rank_le n termCount _ (restricted arguments present)

/-- Locally `r`-decomposable critical layers force the central-binomial
rank/cost tradeoff. -/
theorem centralBinom_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (termCount : Nat)
    (termCountPositive : 0 < termCount)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : AtMultiplications constant n circuit termCount) :
    Nat.centralBinom n ⌈/⌉ termCount ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Catalecticant.centralBinom_ceilDiv_lowerBound constant n positive termCount
    termCountPositive circuit constructs
      (localRankAtMost_of_multiplicationOutputRankAtMost constant n positive
        circuit termCount
          (multiplicationOutputRankAtMost_of_atMultiplications constant n
            positive circuit termCount restricted))

/-- Undivided form of the locally decomposable critical-layer tradeoff. -/
theorem centralBinom_le_cost_mul_termCount
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (termCount : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : AtMultiplications constant n circuit termCount) :
    Nat.centralBinom n ≤
      circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        termCount :=
  centralBinom_le_cost_mul_rank constant n positive termCount circuit constructs
    (localRankAtMost_of_multiplicationOutputRankAtMost constant n positive
      circuit termCount
        (multiplicationOutputRankAtMost_of_atMultiplications constant n positive
          circuit termCount restricted))

end
end Decomposition
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
