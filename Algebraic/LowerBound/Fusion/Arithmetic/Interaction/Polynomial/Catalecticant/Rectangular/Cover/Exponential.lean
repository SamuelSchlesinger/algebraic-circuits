import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Cover.Occurrence

/-!
# Exponential consequences of middle-layer rectangle covers

For the degree-`2n` squarefree monomial, the middle catalecticant has rank
`centralBinom n`.  If every multiplication occurrence has a rectangle cover
of weighted size at most `r`, then

`centralBinom n ≤ multiplicationCost * r`.

Combining this with Mathlib's explicit central-binomial estimate gives
`4^n < n * (multiplicationCost * r)` for `n ≥ 4`.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Cover
namespace Exponential

noncomputable section

variable {K : Type} {C : Type}

/-- Uniform middle-layer rectangle covers give the central-binomial
multiplication lower bound. -/
theorem centralBinom_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (nPositive : 0 < n)
    (coverBudget : Nat)
    (coverBudgetPositive : 0 < coverBudget)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K (2 * n)).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (covered : Occurrence.AtOccurrences constant (2 * n) n circuit
      (fun _ ↦ coverBudget)) :
    Nat.centralBinom n ⌈/⌉ coverBudget ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  simpa [Nat.centralBinom] using
    Occurrence.choose_ceilDiv_lowerBound constant (2 * n) n (by omega)
      coverBudget coverBudgetPositive circuit constructs covered

/-- Undivided middle-layer tradeoff between multiplication cost and local
rectangle-cover weight. -/
theorem centralBinom_le_cost_mul_coverBudget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (nPositive : 0 < n)
    (coverBudget : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K (2 * n)).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (covered : Occurrence.AtOccurrences constant (2 * n) n circuit
      (fun _ ↦ coverBudget)) :
    Nat.centralBinom n ≤
      circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        coverBudget := by
  simpa [Nat.centralBinom,
    Rectangular.Decomposition.multiplicationOccurrences_length] using
    (Occurrence.choose_le_sum_budget constant (2 * n) n (by omega) circuit
      constructs (fun _ ↦ coverBudget) covered)

/-- Explicit exponential product lower bound for circuits with uniformly
coverable middle-layer gate interactions. -/
theorem four_pow_lt_n_mul_cost_mul_coverBudget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (nBig : 4 ≤ n)
    (coverBudget : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K (2 * n)).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (covered : Occurrence.AtOccurrences constant (2 * n) n circuit
      (fun _ ↦ coverBudget)) :
    4 ^ n < n *
      (circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        coverBudget) :=
  (Nat.four_pow_lt_mul_centralBinom n nBig).trans_le
    (Nat.mul_le_mul_left n
      (centralBinom_le_cost_mul_coverBudget constant n (by omega)
        coverBudget circuit constructs covered))

end
end Exponential
end Cover
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
