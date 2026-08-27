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
