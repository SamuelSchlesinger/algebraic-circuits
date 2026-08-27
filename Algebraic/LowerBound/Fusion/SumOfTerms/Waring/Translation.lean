import Algebraic.Basis.Arithmetic.Expression
import Algebraic.Translation.Contextual
import Algebraic.LowerBound.Fusion.SumOfTerms.Waring

/-!
# Compiling Waring sums to ordinary arithmetic circuits

A Waring term is syntactically nullary in the sum-of-terms basis but depends
semantically on a shared family of polynomial variables.  A contextual
translation exposes those variables to every term gadget.  The gadgets are
compiled from reusable arithmetic expressions, giving exact semantics and a
concrete ordinary arithmetic circuit for every sum-of-powers circuit.
-/

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Translation

noncomputable section

variable {K : Type}

/-- Right-associated sum of arithmetic expressions, with a named zero for the
empty sum. -/
def expressionSum
    [Zero K] : List (Algebraic.Arithmetic.Expression K variableCount) →
      Algebraic.Arithmetic.Expression K variableCount
  | [] => .constant 0
  | expression :: expressions => .add expression (expressionSum expressions)

/-- Naive natural power expression.  Tree compilation intentionally exposes
every intermediate product as its own multiplication gate. -/
def expressionPower
    [One K]
    (base : Algebraic.Arithmetic.Expression K variableCount) : Nat →
      Algebraic.Arithmetic.Expression K variableCount
  | 0 => .constant 1
  | exponent + 1 => .mul base (expressionPower base exponent)

/-- Arithmetic expression for the linear form of one Waring term. -/
def linearFormExpression
    [Zero K]
    (term : Term K n) :
    Algebraic.Arithmetic.Expression K (2 * n) :=
  expressionSum <| List.ofFn fun index : Fin (2 * n) =>
    .mul (.constant (term.coefficients index)) (.input index)

/-- Arithmetic expression for one charged Waring term. -/
def termExpression
    [Zero K]
    [One K]
    (term : Term K n) :
    Algebraic.Arithmetic.Expression K (2 * n) :=
  .mul (.constant term.scale)
    (expressionPower (linearFormExpression term) (2 * n))

/-- Arithmetic expression implementing the source addition gate after the
`2n` shared context inputs. -/
def additionExpression
    [Zero K]
    (n : Nat) : Algebraic.Arithmetic.Expression K (2 * n + 2) :=
  .add (.input (Fin.natAdd (2 * n) (0 : Fin 2)))
    (.input (Fin.natAdd (2 * n) (1 : Fin 2)))

/-- A right-associated expression sum has the sum of its subtree costs plus
one addition charge per list entry (including the final addition to zero). -/
theorem weightedCost_expressionSum
    [Zero K]
    (addition multiplication : Nat)
    (expressions : List
      (Algebraic.Arithmetic.Expression K variableCount)) :
    (expressionSum expressions).weightedCost addition multiplication =
      (expressions.map
        (Algebraic.Arithmetic.Expression.weightedCost addition multiplication)).sum +
        addition * expressions.length := by
  induction expressions with
  | nil => rfl
  | cons expression expressions inductionHypothesis =>
      simp [expressionSum, Algebraic.Arithmetic.Expression.weightedCost,
        inductionHypothesis, Nat.mul_succ]
      omega

/-- Naive power compilation repeats the base tree once per exponent step and
adds one multiplication node at that step. -/
theorem weightedCost_expressionPower
    [One K]
    (addition multiplication : Nat)
    (base : Algebraic.Arithmetic.Expression K variableCount)
    (exponent : Nat) :
    (expressionPower base exponent).weightedCost addition multiplication =
      exponent * (base.weightedCost addition multiplication + multiplication) := by
  induction exponent with
  | zero => simp [expressionPower, Algebraic.Arithmetic.Expression.weightedCost]
  | succ exponent inductionHypothesis =>
      simp [expressionPower, Algebraic.Arithmetic.Expression.weightedCost,
        inductionHypothesis, Nat.succ_mul]
      omega

/-- Exact number of multiplications in a compiled linear-form gadget. -/
@[simp] theorem multiplicationCount_linearFormExpression
    [Zero K]
    (term : Term K n) :
    (linearFormExpression term).multiplicationCount = 2 * n := by
  rw [linearFormExpression]
  simp [Algebraic.Arithmetic.Expression.multiplicationCount,
    Algebraic.Arithmetic.Expression.weightedCost,
    weightedCost_expressionSum, Function.comp_apply, List.sum_ofFn]

/-- Exact number of additions in a compiled linear-form gadget. -/
@[simp] theorem additionCount_linearFormExpression
    [Zero K]
    (term : Term K n) :
    (linearFormExpression term).additionCount = 2 * n := by
  rw [linearFormExpression]
  simp [Algebraic.Arithmetic.Expression.additionCount,
    Algebraic.Arithmetic.Expression.weightedCost,
    weightedCost_expressionSum, Function.comp_apply, List.sum_ofFn]

/-- Multiplicative cost of one naive compiled Waring-term gadget. -/
def termMultiplicationCount (n : Nat) : Nat :=
  (2 * n) * (2 * n + 1) + 1

/-- Additive cost of one naive compiled Waring-term gadget. -/
def termAdditionCount (n : Nat) : Nat :=
  (2 * n) * (2 * n)

/-- Exact multiplicative cost of a Waring-term expression. -/
@[simp] theorem multiplicationCount_termExpression
    [Zero K]
    [One K]
    (term : Term K n) :
    (termExpression term).multiplicationCount = termMultiplicationCount n := by
  simp [termExpression, Algebraic.Arithmetic.Expression.multiplicationCount,
    Algebraic.Arithmetic.Expression.weightedCost,
    weightedCost_expressionPower, termMultiplicationCount]

/-- Exact additive cost of a Waring-term expression. -/
@[simp] theorem additionCount_termExpression
    [Zero K]
    [One K]
    (term : Term K n) :
    (termExpression term).additionCount = termAdditionCount n := by
  simp [termExpression, Algebraic.Arithmetic.Expression.additionCount,
    Algebraic.Arithmetic.Expression.weightedCost,
    weightedCost_expressionPower, termAdditionCount]

/-- The source-addition gadget uses no multiplication gates. -/
@[simp] theorem multiplicationCount_additionExpression
    [Zero K]
    (n : Nat) :
    (additionExpression (K := K) n).multiplicationCount = 0 := rfl

/-- The source-addition gadget uses exactly one addition gate. -/
@[simp] theorem additionCount_additionExpression
    [Zero K]
    (n : Nat) :
    (additionExpression (K := K) n).additionCount = 1 := rfl

/-- Evaluation of a right-associated expression sum. -/
theorem eval_expressionSum
    [Semiring R]
    [Zero K]
    (constant : K → R)
    (input : Fin variableCount → R)
    (mapsZero : constant 0 = 0)
    (expressions : List (Algebraic.Arithmetic.Expression K variableCount)) :
    Algebraic.Arithmetic.Expression.eval constant input
        (expressionSum expressions) =
      (expressions.map
        (Algebraic.Arithmetic.Expression.eval constant input)).sum := by
  induction expressions with
  | nil => simp [expressionSum, Algebraic.Arithmetic.Expression.eval, mapsZero]
  | cons expression expressions inductionHypothesis =>
      simp [expressionSum, Algebraic.Arithmetic.Expression.eval,
        inductionHypothesis]

/-- Evaluation of the naive power expression. -/
theorem eval_expressionPower
    [Semiring R]
    [One K]
    (constant : K → R)
    (input : Fin variableCount → R)
    (mapsOne : constant 1 = 1)
    (base : Algebraic.Arithmetic.Expression K variableCount)
    (exponent : Nat) :
    Algebraic.Arithmetic.Expression.eval constant input
        (expressionPower base exponent) =
      (Algebraic.Arithmetic.Expression.eval constant input base) ^ exponent := by
  induction exponent with
  | zero => simp [expressionPower, Algebraic.Arithmetic.Expression.eval, mapsOne]
  | succ exponent inductionHypothesis =>
      simp [expressionPower, Algebraic.Arithmetic.Expression.eval,
        inductionHypothesis, pow_succ']

/-- The linear-form expression evaluates to the polynomial linear form. -/
theorem eval_linearFormExpression
    [CommSemiring K]
    (term : Term K n) :
    Algebraic.Arithmetic.Expression.eval
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        (linearFormExpression term) =
      linearForm term := by
  rw [linearFormExpression, eval_expressionSum]
  · simp [Algebraic.Arithmetic.Expression.eval, linearForm,
      List.sum_ofFn, MvPolynomial.smul_eq_C_mul]
  · exact MvPolynomial.C_0

/-- The term expression evaluates exactly to the charged Waring term. -/
theorem eval_termExpression
    [CommSemiring K]
    (term : Term K n) :
    Algebraic.Arithmetic.Expression.eval
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (termExpression term) =
      termValue term := by
  rw [termExpression, Algebraic.Arithmetic.Expression.eval]
  rw [eval_expressionPower
    (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
    (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    MvPolynomial.C_1]
  rw [eval_linearFormExpression]
  rfl

/-- Contextual compilation of Waring sum-of-terms syntax into the ordinary
arithmetic basis. -/
def translation
    [Semiring K]
    (n : Nat) :
    ContextualTranslation
      (Algebraic.SumOfTerms.signature (Term K n))
      (Algebraic.Arithmetic.signature K) (2 * n) where
  gateCount
    | .add => (additionExpression (K := K) n).gateCount
    | .term term => (termExpression term).gateCount
  operation
    | .add => Algebraic.Arithmetic.Expression.circuit
        (additionExpression (K := K) n)
    | .term term => Algebraic.Arithmetic.Expression.circuit
        (termExpression term)

/-- Pulling target multiplication cost through the Waring translation charges
each source term by the exact naive term-gadget multiplication count and makes
source addition free. -/
theorem pullCost_multiplicationCost
    [Semiring K]
    (n : Nat) :
    (translation (K := K) n).pullCost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      Algebraic.SumOfTerms.weightedCost 0 (termMultiplicationCount n) := by
  funext operation
  cases operation with
  | add =>
      simp [ContextualTranslation.pullCost, translation]
  | term term =>
      simp [ContextualTranslation.pullCost, translation]

/-- Pulling target addition cost through the Waring translation charges one
for every source addition and charges each term by its exact internal
addition count. -/
theorem pullCost_additionCost
    [Semiring K]
    (n : Nat) :
    (translation (K := K) n).pullCost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      Algebraic.SumOfTerms.weightedCost 1 (termAdditionCount n) := by
  funext operation
  cases operation with
  | add =>
      simp [ContextualTranslation.pullCost, translation]
  | term term =>
      simp [ContextualTranslation.pullCost, translation]

/-- Exact multiplication cost of contextual Waring compilation. -/
theorem compile_multiplicationCost
    [Semiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      circuit.cost
        (Algebraic.SumOfTerms.weightedCost 0 (termMultiplicationCount n)) := by
  rw [ContextualTranslation.compile_cost, pullCost_multiplicationCost]

/-- Closed multiplication-cost formula: the naive compiler pays the same
quadratic gadget cost for every Waring term and nothing for source addition. -/
theorem compile_multiplicationCost_eq_termCost
    [Semiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      termMultiplicationCount n *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K n)) := by
  rw [compile_multiplicationCost,
    Algebraic.SumOfTerms.circuit_cost_weightedCost]
  simp

/-- Exact addition cost of contextual Waring compilation. -/
theorem compile_additionCost
    [Semiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      circuit.cost
        (Algebraic.SumOfTerms.weightedCost 1 (termAdditionCount n)) := by
  rw [ContextualTranslation.compile_cost, pullCost_additionCost]

/-- Closed addition-cost formula: source additions remain single additions,
while each Waring term contributes its internal quadratic addition cost. -/
theorem compile_additionCost_eq_sourceCosts
    [Semiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      circuit.cost
          (Algebraic.SumOfTerms.additionCost (T := Term K n)) +
        termAdditionCount n *
          circuit.cost
            (Algebraic.SumOfTerms.termCost (T := Term K n)) := by
  rw [compile_additionCost,
    Algebraic.SumOfTerms.circuit_cost_weightedCost]
  simp

/-- Pulling ordinary polynomial semantics through the contextual translation
recovers Waring sum-of-terms semantics exactly. -/
theorem pull_polynomial
    [CommSemiring K]
    (n : Nat) :
    (translation (K := K) n).pull
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) =
      Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)) := by
  funext operation arguments
  cases operation with
  | add =>
      rw [ContextualTranslation.pull]
      simp only [translation]
      simp only [Algebraic.SumOfTerms.arity] at arguments ⊢
      rw [Algebraic.Arithmetic.Expression.circuit_eval]
      simp [additionExpression,
        Algebraic.Arithmetic.Expression.eval,
        ContextualTranslation.appendInputs,
        Algebraic.SumOfTerms.interpretation]
  | term term =>
      rw [ContextualTranslation.pull]
      simp only [translation]
      simp only [Algebraic.SumOfTerms.arity] at arguments ⊢
      rw [Algebraic.Arithmetic.Expression.circuit_eval]
      have inputEq :
          ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin (2 * n) →
                MvPolynomial (Fin (2 * n)) K)
              arguments =
            (MvPolynomial.X : Fin (2 * n) →
              MvPolynomial (Fin (2 * n)) K) := by
        funext index
        exact Fin.addCases (fun context => by
            rw [ContextualTranslation.appendInputs_context]
            congr 1)
          (fun impossible => Fin.elim0 impossible) index
      rw [inputEq]
      simpa [Algebraic.SumOfTerms.interpretation] using
        eval_termExpression term

/-- Contextual compilation preserves every Waring circuit's polynomial
outputs. -/
theorem compile_eval
    [CommSemiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).eval
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) =
      circuit.eval
        (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))
        (fun input => Fin.elim0 input) := by
  have compiled := (translation (K := K) n).compile_eval circuit
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (fun input => Fin.elim0 input)
  rw [pull_polynomial] at compiled
  have inputEq :
      ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          (fun input : Fin 0 => Fin.elim0 input) =
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) := by
    funext index
    exact Fin.addCases (fun context => by
        rw [ContextualTranslation.appendInputs_context]
        congr 1)
      (fun impossible => Fin.elim0 impossible) index
  rw [inputEq] at compiled
  exact compiled

end
end Translation
end Waring
end SumOfTerms
end Fusion
end Algebraic
