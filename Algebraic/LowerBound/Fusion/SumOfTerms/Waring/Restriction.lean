import Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation
import Algebraic.LowerBound.Fusion.Arithmetic.Expression
import Algebraic.LowerBound.Fusion.Contextual
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree

/-!
# Graded restriction of compiled Waring circuits

The contextual Waring compiler emits only three kinds of multiplication
outputs: scalar multiples of variables, proper intermediate powers of a
linear form, and full `2n`-th powers (optionally with the term scale).  The
first two are invisible in the critical homogeneous layer; the last kind is a
single Waring term.  Hence every compiled Waring circuit satisfies the
layer-exact rank-one restriction used by catalecticant Fusion.
-/

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Restriction

noncomputable section

open Arithmetic.Interaction.Polynomial.Catalecticant

variable {K : Type}

/-- A polynomial's critical degree-`2n` component is either zero or one
charged Waring term. -/
def CriticalLayerOrPower
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K) : Prop :=
  MvPolynomial.homogeneousComponent (2 * n) polynomial = 0 ∨
    ∃ term : Term K n,
      MvPolynomial.homogeneousComponent (2 * n) polynomial = termValue term

/-- A homogeneous polynomial away from the critical degree is invisible. -/
theorem criticalLayerOrPower_of_isHomogeneous_ne
    [Field K]
    (n degree : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (homogeneous : polynomial.IsHomogeneous degree)
    (notCritical : degree ≠ 2 * n) :
    CriticalLayerOrPower n polynomial := by
  left
  rw [MvPolynomial.homogeneousComponent_of_mem homogeneous]
  simp [notCritical.symm]

/-- A charged Waring term occupies the critical layer by itself. -/
theorem criticalLayerOrPower_termValue
    [Field K]
    (term : Term K n) :
    CriticalLayerOrPower n (termValue term) := by
  right
  exact ⟨term,
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.homogeneousComponent_termValue
      term⟩

/-- Multiplication-property closure under a right-associated expression sum. -/
theorem multiplicationProperty_expressionSum
    [Field K]
    (n : Nat)
    (expressions : List
      (Algebraic.Arithmetic.Expression K (2 * n)))
    (each : ∀ expression ∈ expressions,
      Arithmetic.Expression.MultiplicationProperty
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        (CriticalLayerOrPower n) expression) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.expressionSum expressions) := by
  induction expressions with
  | nil => trivial
  | cons expression expressions inductionHypothesis =>
      exact ⟨each expression (by simp), inductionHypothesis (by
        intro other present
        exact each other (by simp [present]))⟩

/-- Every coefficient-times-variable product in the linear-form gadget is
invisible at positive half-degree. -/
theorem multiplicationProperty_coefficientVariable
    [Field K]
    (n : Nat)
    (_positive : 0 < n)
    (coefficient : K)
    (index : Fin (2 * n)) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (.mul (.constant coefficient) (.input index)) := by
  refine ⟨trivial, trivial, ?_⟩
  apply criticalLayerOrPower_of_isHomogeneous_ne n 1
  · exact MvPolynomial.isHomogeneous_C_mul_X coefficient index
  · omega

/-- Every multiplication in the linear-form expression is invisible at the
critical layer. -/
theorem multiplicationProperty_linearFormExpression
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.linearFormExpression term) := by
  unfold Translation.linearFormExpression
  apply multiplicationProperty_expressionSum n
  intro expression present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact multiplicationProperty_coefficientVariable n positive _ index

/-- Every multiplication in a proper-or-full power expression has an
invisible critical layer or is one full Waring power. -/
theorem multiplicationProperty_expressionPower
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n)
    (exponent : Nat)
    (bounded : exponent ≤ 2 * n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.expressionPower
        (Translation.linearFormExpression term) exponent) := by
  induction exponent with
  | zero => trivial
  | succ exponent inductionHypothesis =>
      refine ⟨multiplicationProperty_linearFormExpression n positive term,
        inductionHypothesis (by omega), ?_⟩
      rw [Translation.eval_expressionPower
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          MvPolynomial.C_1,
        Translation.eval_linearFormExpression]
      rw [← pow_succ']
      by_cases full : exponent + 1 = 2 * n
      · let powerTerm : Term K n :=
          { scale := 1
            coefficients := term.coefficients }
        have powerValue :
            linearForm term ^ (exponent + 1) = termValue powerTerm := by
          rw [full]
          simp [termValue, powerTerm, linearForm]
        rw [powerValue]
        exact criticalLayerOrPower_termValue powerTerm
      · apply criticalLayerOrPower_of_isHomogeneous_ne n (exponent + 1)
        · simpa [Nat.add_comm] using
            (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.linearForm_isHomogeneous
              term).pow
              (exponent + 1)
        · exact full

/-- The complete Waring term expression satisfies the critical-layer
multiplication property. -/
theorem multiplicationProperty_termExpression
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.termExpression term) := by
  unfold Translation.termExpression
  refine ⟨trivial,
    multiplicationProperty_expressionPower n positive term (2 * n) le_rfl,
    ?_⟩
  rw [Translation.eval_expressionPower
    (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
    (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    MvPolynomial.C_1]
  rw [Translation.eval_linearFormExpression]
  exact criticalLayerOrPower_termValue term

/-- Atom-local packaging of the critical-layer property: it only constrains
an atom when that atom is a multiplication. -/
def MultiplicationAtomProperty
    [Field K]
    (n : Nat)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin (2 * n)) K,
    atom = (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) →
    CriticalLayerOrPower n
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- Every atom in an individual contextual Waring gadget satisfies the local
critical-layer multiplication property. -/
theorem gadget_multiplicationAtomProperty
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (operation : Algebraic.SumOfTerms.Op (Term K n))
    (sourceArguments : Fin (Algebraic.SumOfTerms.arity operation) →
      MvPolynomial (Fin (2 * n)) K)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K))
    (present : atom ∈ circuitAtoms
      ((Translation.translation (K := K) n).operation operation)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (Algebraic.ContextualTranslation.appendInputs
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        sourceArguments)) :
    MultiplicationAtomProperty n atom := by
  intro arguments atomEqual
  rw [atomEqual] at present
  cases operation with
  | add =>
      simp only [Translation.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          sourceArguments)
        (CriticalLayerOrPower n)
        (Translation.additionExpression (K := K) n)
      · exact ⟨trivial, trivial⟩
      · exact present
  | term term =>
      simp only [Translation.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      have inputEq :
          Algebraic.ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin (2 * n) →
                MvPolynomial (Fin (2 * n)) K)
              sourceArguments =
            (MvPolynomial.X : Fin (2 * n) →
              MvPolynomial (Fin (2 * n)) K) := by
        funext index
        exact Fin.addCases (fun context => by
            rw [Algebraic.ContextualTranslation.appendInputs_context]
            congr 1)
          (fun impossible => Fin.elim0 impossible) index
      rw [inputEq] at present
      apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        (CriticalLayerOrPower n) (Translation.termExpression term)
      · exact multiplicationProperty_termExpression n positive term
      · exact present

/-- Contextual compilation of any Waring circuit satisfies the layer-exact
rank-one restriction for ordinary arithmetic circuits. -/
theorem compiled_criticalLayerOrPowerAtMultiplications
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.CriticalLayerOrPowerAtMultiplications
      (id : K → K) n ((Translation.translation (K := K) n).compile circuit) := by
  intro arguments present
  change (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) ∈
    circuitAtoms ((Translation.translation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    at present
  have inputEq :
      Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          (fun input : Fin 0 => Fin.elim0 input) =
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) := by
    funext index
    exact Fin.addCases (fun context => by
        rw [Algebraic.ContextualTranslation.appendInputs_context]
        congr 1)
      (fun impossible => Fin.elim0 impossible) index
  rw [← inputEq] at present
  have localProof := Algebraic.Fusion.ContextualTranslation.forall_atoms_compile
    (Translation.translation (K := K) n) circuit
    (Algebraic.Arithmetic.interpretation
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
    (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    (fun input : Fin 0 => Fin.elim0 input)
    (MultiplicationAtomProperty n)
    (gadget_multiplicationAtomProperty n positive)
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) present
  exact localProof arguments rfl

/-- Compilation transports construction of the squarefree Waring target to
construction by an ordinary arithmetic circuit on the shared variables. -/
theorem compiled_constructs
    [Field K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.problem K n).Constructs
      ((Translation.translation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)) := by
  change ((Translation.translation (K := K) n).compile circuit).eval
      (Algebraic.Arithmetic.interpretation MvPolynomial.C) MvPolynomial.X 0 =
    target K n
  rw [Translation.compile_eval]
  exact constructs

/-- The compiled ordinary circuit inherits the central-binomial
multiplication lower bound from layer-exact catalecticant Fusion. -/
theorem compiled_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      ((Translation.translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_multiplication_lowerBound
    id n positive
    ((Translation.translation (K := K) n).compile circuit)
    (compiled_constructs n circuit constructs)
    (compiled_criticalLayerOrPowerAtMultiplications n positive circuit)

/-- Explicit exponential ordinary-circuit size bound for compiled Waring
circuits constructing the squarefree target. -/
theorem compiled_four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    4 ^ n < n * ((Translation.translation (K := K) n).compile circuit).size :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_four_pow_lt_mul_size
    id n n_big
    ((Translation.translation (K := K) n).compile circuit)
    (compiled_constructs n circuit constructs)
    (compiled_criticalLayerOrPowerAtMultiplications n (by omega) circuit)

end
end Restriction
end Waring
end SumOfTerms
end Fusion
end Algebraic
