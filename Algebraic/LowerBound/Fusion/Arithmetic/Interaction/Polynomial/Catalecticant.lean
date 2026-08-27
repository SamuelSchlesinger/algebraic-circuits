import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Local
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear
import Algebraic.LowerBound.Fusion.Arithmetic.Combined
import Algebraic.LowerBound.Fusion.SumOfTerms.Waring

/-!
# Local catalecticant-rank bounds for arithmetic circuits

Use the normalized middle catalecticant from the Waring lower bound as a
linear-map feature of an ordinary arithmetic circuit.  Constants and input
variables have zero feature.  With the generic linear interaction certificate,
the interaction created by a multiplication is the catalecticant of that
gate's product output.

Hence an explicit circuit-local restriction—every multiplication output has
middle-catalecticant rank at most `r`—forces the squarefree target to use at
least `centralBinom n / r` multiplication gates.  For `r = 1` this is an
exponential single-output lower bound for the restricted ordinary arithmetic
circuit model.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant

noncomputable section

open Cardinal

variable {K : Type} {C : Type}

/-- Every queried middle-catalecticant exponent is nonzero for a positive
half-degree. -/
theorem entryExponent_ne_zero
    (n : Nat)
    (positive : 0 < n)
    (row column : SumOfTerms.MatrixRank.Layer (2 * n) n) :
    SumOfTerms.Waring.entryExponent n row column ≠ 0 := by
  intro equal
  have sumEqual := congrArg
    (fun exponent : Fin (2 * n) →₀ ℕ =>
      exponent.sum (fun _ multiplicity => multiplicity)) equal
  unfold SumOfTerms.Waring.entryExponent at sumEqual
  rw [SumOfTerms.Waring.exponent_add_complement_sum] at sumEqual
  simp at sumEqual
  omega

/-- Every queried middle-catalecticant exponent has degree bigger than one
for a positive half-degree. -/
theorem entryExponent_ne_single
    (n : Nat)
    (row column : SumOfTerms.MatrixRank.Layer (2 * n) n)
    (input : Fin (2 * n)) :
    SumOfTerms.Waring.entryExponent n row column ≠
      Finsupp.single input 1 := by
  intro equal
  have sumEqual := congrArg
    (fun exponent : Fin (2 * n) →₀ ℕ =>
      exponent.sum (fun _ multiplicity => multiplicity)) equal
  unfold SumOfTerms.Waring.entryExponent at sumEqual
  rw [SumOfTerms.Waring.exponent_add_complement_sum] at sumEqual
  simp at sumEqual

/-- Constants have zero normalized middle catalecticant. -/
theorem catalecticant_C_eq_zero
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (scalar : K) :
    SumOfTerms.Waring.catalecticant K n (MvPolynomial.C scalar) = 0 := by
  classical
  ext row column
  simp [SumOfTerms.Waring.catalecticant_apply, MvPolynomial.coeff_C,
    (entryExponent_ne_zero n positive row column).symm]

/-- Input variables have zero normalized middle catalecticant. -/
theorem catalecticant_X_eq_zero
    [Field K]
    (n : Nat)
    (input : Fin (2 * n)) :
    SumOfTerms.Waring.catalecticant K n (MvPolynomial.X input) = 0 := by
  classical
  ext row column
  simp [SumOfTerms.Waring.catalecticant_apply, MvPolynomial.coeff_X,
    (entryExponent_ne_single n row column input).symm]

/-- Constants have zero catalecticant linear-map feature. -/
theorem feature_C_eq_zero
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (scalar : K) :
    SumOfTerms.Waring.feature K n (MvPolynomial.C scalar) = 0 := by
  simp [SumOfTerms.Waring.feature,
    catalecticant_C_eq_zero n positive scalar]

/-- Input variables have zero catalecticant linear-map feature. -/
theorem feature_X_eq_zero
    [Field K]
    (n : Nat)
    (input : Fin (2 * n)) :
    SumOfTerms.Waring.feature K n (MvPolynomial.X input) = 0 := by
  simp [SumOfTerms.Waring.feature,
    catalecticant_X_eq_zero n input]

/-- Ordinary arithmetic problem of constructing the squarefree product of all
`2n` input variables. -/
abbrev problem
    (K : Type)
    [Field K]
    (n : Nat) : Problem (MvPolynomial (Fin (2 * n)) K) where
  inputCount := 2 * n
  inputs := MvPolynomial.X
  target := SumOfTerms.Waring.target K n

/-- Linear interaction certificate induced by the normalized middle
catalecticant.  A multiplication interaction is the feature of its product. -/
def certificate
    [Field K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n) :
    Interaction.Certificate (K := K)
      (Q := (SumOfTerms.MatrixRank.Layer (2 * n) n → K) →ₗ[K]
        (SumOfTerms.MatrixRank.Layer (2 * n) n → K))
      (fun scalar => MvPolynomial.C (constant scalar))
      (problem K n) :=
  Linear.certificate
    (fun scalar => MvPolynomial.C (constant scalar))
    (problem K n) (SumOfTerms.Waring.feature K n)
    (fun input => feature_X_eq_zero n input)
    (fun scalar => feature_C_eq_zero n positive (constant scalar))

/-- Circuit-local restriction saying that every multiplication output has
normalized middle-catalecticant rank at most `interactionRank`. -/
def LocalRankAtMost
    [Field K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (interactionRank : Nat) : Prop :=
  Rank.Local.CircuitBound (certificate constant n positive) circuit
    interactionRank

/-- General local-rank tradeoff for the squarefree target. -/
theorem centralBinom_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (interactionRank : Nat)
    (rankPositive : 0 < interactionRank)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant n positive circuit
      interactionRank) :
    Nat.centralBinom n ⌈/⌉ interactionRank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Rank.Local.circuit_lowerBound (certificate constant n positive)
    (Nat.centralBinom n) interactionRank
  · exact SumOfTerms.Waring.target_rank_ge n
  · exact rankPositive
  · exact constructs
  · exact localBound

/-- Undivided exponential tradeoff: target rank is at most multiplication
cost times the actual local interaction-rank bound. -/
theorem centralBinom_le_cost_mul_rank
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (interactionRank : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant n positive circuit
      interactionRank) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) *
          interactionRank := by
  exact Rank.Local.targetRank_le_mul_multiplicationCost
    (certificate constant n positive) (Nat.centralBinom n) interactionRank
    (SumOfTerms.Waring.target_rank_ge n) circuit constructs localBound

/-- Rank-one multiplication outputs force a central-binomial multiplication
lower bound. -/
theorem rankOne_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant n positive circuit 1) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  simpa using centralBinom_ceilDiv_lowerBound constant n positive 1
    (by simp) circuit constructs localBound

/-- Explicit exponential single-output multiplication lower bound for locally
rank-one arithmetic circuits. -/
theorem four_pow_lt_mul_multiplicationCost
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant n (by omega) circuit 1) :
    4 ^ n < n * circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      (rankOne_multiplication_lowerBound constant n (by omega) circuit
        constructs localBound))

/-- Explicit exponential raw-size lower bound for locally rank-one arithmetic
circuits. -/
theorem four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant n (by omega) circuit 1) :
    4 ^ n < n * circuit.size :=
  (four_pow_lt_mul_multiplicationCost constant n n_big circuit constructs
    localBound).trans_le
      (Nat.mul_le_mul_left n
        ((Combined.circuit_multiplicationCost_le_gateCost circuit).trans
          (Combined.circuit_gateCost_le_size circuit)))

end
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
