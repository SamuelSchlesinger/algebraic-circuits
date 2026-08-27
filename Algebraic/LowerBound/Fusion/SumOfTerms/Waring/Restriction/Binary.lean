import Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Restriction
import Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation.Binary

/-!
# Critical-layer restriction for binary-compiled Waring circuits

Binary powering visits a sparse sequence of exponents rather than every
intermediate exponent.  Nevertheless each emitted multiplication is still a
power of the shared linear form of degree at most `2n`; it is therefore either
invisible to the critical layer or is the final full Waring power.
-/

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Restriction
namespace Binary

noncomputable section

open Arithmetic.Interaction.Polynomial.Catalecticant

variable {K : Type}

/-- Any bounded power of a Waring linear form is either outside the critical
degree or is itself one charged Waring term. -/
theorem criticalLayerOrPower_linearForm_pow
    [Field K]
    (n : Nat)
    (term : Term K n)
    (exponent : Nat)
    (_bounded : exponent ≤ 2 * n) :
    CriticalLayerOrPower n (linearForm term ^ exponent) := by
  by_cases full : exponent = 2 * n
  · let powerTerm : Term K n :=
      { scale := 1
        coefficients := term.coefficients }
    have powerValue : linearForm term ^ exponent = termValue powerTerm := by
      rw [full]
      simp [termValue, powerTerm, linearForm]
    rw [powerValue]
    exact criticalLayerOrPower_termValue powerTerm
  · apply criticalLayerOrPower_of_isHomogeneous_ne n exponent
    · simpa using
        (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.linearForm_isHomogeneous
          term).pow exponent
    · exact full

/-- Every multiplication atom in a binary power circuit computes a bounded
power of its input linear form. -/
theorem powerCircuit_multiplicationAtomProperty
    [Field K]
    (n : Nat)
    (term : Term K n)
    (exponent : Nat)
    (bounded : exponent ≤ 2 * n)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K))
    (present : atom ∈ circuitAtoms
      (Algebraic.Arithmetic.Power.binaryCircuit (K := K) exponent).2
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (fun _ : Fin 1 ↦ linearForm term)) :
    MultiplicationAtomProperty n atom := by
  induction exponent using Nat.binaryRecFromOne generalizing atom with
  | zero =>
      intro arguments atomEqual
      rw [atomEqual,
        Algebraic.Arithmetic.Power.binaryCircuit_zero] at present
      simp [circuitAtoms, Algebraic.Arithmetic.Expression.circuit,
        Algebraic.Arithmetic.Expression.compile, lineAtom] at present
      have operationEqual := congrArg Atom.op present
      contradiction
  | one =>
      intro arguments atomEqual
      rw [atomEqual,
        Algebraic.Arithmetic.Power.binaryCircuit_one] at present
      simp [circuitAtoms, Circuit.id] at present
  | bit bit prior nonzero inductionHypothesis =>
      rw [Algebraic.Arithmetic.Power.binaryCircuit_bit bit prior nonzero]
        at present
      cases bit with
      | false =>
          simp only [Nat.bit_false_apply] at bounded
          change atom ∈ circuitAtoms
            (Algebraic.Arithmetic.Power.squareCircuit
              (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2)
            _ _ at present
          simp only [circuitAtoms, Algebraic.Arithmetic.Power.squareCircuit,
            programAtoms_gate] at present
          rcases List.mem_append.mp present with inPrior | inSquare
          · apply inductionHypothesis
            · omega
            · exact inPrior
          · intro arguments atomEqual
            rw [atomEqual] at inSquare
            have atomEq := List.mem_singleton.mp inSquare
            have resultEq := congrArg
              (fun candidate : Atom (Algebraic.Arithmetic.signature K)
                  (MvPolynomial (Fin (2 * n)) K) ↦
                candidate.result
                  (Algebraic.Arithmetic.interpretation MvPolynomial.C))
              atomEq
            change CriticalLayerOrPower n
              ((⟨.mul, arguments⟩ : Atom
                (Algebraic.Arithmetic.signature K)
                (MvPolynomial (Fin (2 * n)) K)).result
                  (Algebraic.Arithmetic.interpretation MvPolynomial.C))
            rw [resultEq]
            change CriticalLayerOrPower n
              (((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                  (Algebraic.Arithmetic.interpretation MvPolynomial.C)
                  (fun _ : Fin 1 ↦ linearForm term) 0) *
                ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                  (Algebraic.Arithmetic.interpretation MvPolynomial.C)
                  (fun _ : Fin 1 ↦ linearForm term) 0))
            rw [Algebraic.Arithmetic.Power.binaryCircuit_eval
              (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
              MvPolynomial.C_1,
              ← pow_add]
            apply criticalLayerOrPower_linearForm_pow n term (prior + prior)
            omega
      | true =>
          simp only [Nat.bit_true_apply] at bounded
          change atom ∈ circuitAtoms
            (Algebraic.Arithmetic.Power.multiplyInputCircuit
              (Algebraic.Arithmetic.Power.squareCircuit
                (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2))
            _ _ at present
          simp only [circuitAtoms,
            Algebraic.Arithmetic.Power.multiplyInputCircuit,
            programAtoms_gate] at present
          rcases List.mem_append.mp present with inSquareCircuit | inOdd
          · change atom ∈ circuitAtoms
              (Algebraic.Arithmetic.Power.squareCircuit
                (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2)
              _ _ at inSquareCircuit
            simp only [circuitAtoms,
              Algebraic.Arithmetic.Power.squareCircuit,
              programAtoms_gate] at inSquareCircuit
            rcases List.mem_append.mp inSquareCircuit with inPrior | inSquare
            · apply inductionHypothesis
              · omega
              · exact inPrior
            · intro arguments atomEqual
              rw [atomEqual] at inSquare
              have atomEq := List.mem_singleton.mp inSquare
              have resultEq := congrArg
                (fun candidate : Atom (Algebraic.Arithmetic.signature K)
                    (MvPolynomial (Fin (2 * n)) K) ↦
                  candidate.result
                    (Algebraic.Arithmetic.interpretation MvPolynomial.C))
                atomEq
              change CriticalLayerOrPower n
                ((⟨.mul, arguments⟩ : Atom
                  (Algebraic.Arithmetic.signature K)
                  (MvPolynomial (Fin (2 * n)) K)).result
                    (Algebraic.Arithmetic.interpretation MvPolynomial.C))
              rw [resultEq]
              change CriticalLayerOrPower n
                (((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                    (Algebraic.Arithmetic.interpretation MvPolynomial.C)
                    (fun _ : Fin 1 ↦ linearForm term) 0) *
                  ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                    (Algebraic.Arithmetic.interpretation MvPolynomial.C)
                    (fun _ : Fin 1 ↦ linearForm term) 0))
              rw [Algebraic.Arithmetic.Power.binaryCircuit_eval
                (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
                MvPolynomial.C_1,
                ← pow_add]
              apply criticalLayerOrPower_linearForm_pow n term (prior + prior)
              omega
          · intro arguments atomEqual
            rw [atomEqual] at inOdd
            have atomEq := List.mem_singleton.mp inOdd
            have resultEq := congrArg
              (fun candidate : Atom (Algebraic.Arithmetic.signature K)
                  (MvPolynomial (Fin (2 * n)) K) ↦
                candidate.result
                  (Algebraic.Arithmetic.interpretation MvPolynomial.C))
              atomEq
            change CriticalLayerOrPower n
              ((⟨.mul, arguments⟩ : Atom
                (Algebraic.Arithmetic.signature K)
                (MvPolynomial (Fin (2 * n)) K)).result
                  (Algebraic.Arithmetic.interpretation MvPolynomial.C))
            rw [resultEq]
            change CriticalLayerOrPower n
              (((Algebraic.Arithmetic.Power.squareCircuit
                  (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2).eval
                    (Algebraic.Arithmetic.interpretation MvPolynomial.C)
                    (fun _ : Fin 1 ↦ linearForm term) 0) * linearForm term)
            rw [Algebraic.Arithmetic.Power.squareCircuit_eval,
              Algebraic.Arithmetic.Power.binaryCircuit_eval
                (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
                MvPolynomial.C_1,
              ← pow_add, ← pow_succ]
            apply criticalLayerOrPower_linearForm_pow n term
              (prior + prior + 1)
            omega

end
end Binary
end Restriction
end Waring
end SumOfTerms
end Fusion
end Algebraic
