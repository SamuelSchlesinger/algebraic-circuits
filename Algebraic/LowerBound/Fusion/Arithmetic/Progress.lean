import Algebraic.LowerBound.Fusion.Framework
import Algebraic.Basis.Arithmetic
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Reverse-substitution progress measures for arithmetic circuits

This is the circuit-DAG form of the enrichment argument used in arithmetic
lower bounds.  Give every input and gate wire its own formal variable, start
with the variable designated as the circuit output, and eliminate gates in
reverse topological order.  Eliminating one gate substitutes its formal
variable by the sum or product of the variables feeding that gate.  A shared
gate is still substituted exactly once, independently of its fanout.

`Measure` packages a quantity that starts at zero on a variable and grows by
at most the charged cost under each such reverse substitution.  The generic
theorem then lower-bounds every constant-free arithmetic circuit producing a
target polynomial.  Schnorr's separated-monomial measure is the classical
addition-cost instance; degree-like measures give multiplication-cost
instances.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress

noncomputable section

/-- Arithmetic interpretation on polynomials with no named constants. -/
def polynomialInterpretation
    (V : Type u) :
    Interpretation (Algebraic.Arithmetic.signature PEmpty)
      (MvPolynomial V ℕ) :=
  Algebraic.Arithmetic.interpretation PEmpty.elim

/-- Formal polynomial computed by one constant-free arithmetic line from
variables naming all wires in its prefix. -/
def lineFormalResult
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    MvPolynomial (Wire n g) ℕ :=
  match line with
  | ⟨.add, wires⟩ =>
      MvPolynomial.X (wires (0 : Fin 2)) +
        MvPolynomial.X (wires (1 : Fin 2))
  | ⟨.mul, wires⟩ =>
      MvPolynomial.X (wires (0 : Fin 2)) *
        MvPolynomial.X (wires (1 : Fin 2))
  | ⟨.constant impossible, _⟩ => PEmpty.elim impossible

/-- Eliminate the new last gate-variable by substituting its formal result;
all earlier wire-variables remain variables. -/
def lineReverseSubstitution
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    MvPolynomial (Wire n (g + 1)) ℕ →ₐ[ℕ]
      MvPolynomial (Wire n g) ℕ :=
  MvPolynomial.bind₁
    (Fin.lastCases (lineFormalResult line) MvPolynomial.X)

@[simp] theorem lineReverseSubstitution_X_last
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    lineReverseSubstitution line
        (MvPolynomial.X (Fin.last (n.add g))) =
      lineFormalResult line := by
  simp [lineReverseSubstitution]

@[simp] theorem lineReverseSubstitution_X_castSucc
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g)
    (wire : Wire n g) :
    lineReverseSubstitution line (MvPolynomial.X wire.castSucc) =
      MvPolynomial.X wire := by
  simp [lineReverseSubstitution]

/-- Expand every formal gate-variable by eliminating gates in reverse
topological order. -/
def programExpansionHom :
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g) →
      MvPolynomial (Wire n g) ℕ →ₐ[ℕ] MvPolynomial (Fin n) ℕ
  | .empty => AlgHom.id ℕ _
  | .gate program line =>
      (programExpansionHom program).comp (lineReverseSubstitution line)

@[simp] theorem programExpansionHom_empty :
    programExpansionHom (Program.empty : Program
      (Algebraic.Arithmetic.signature PEmpty) n 0) =
        AlgHom.id ℕ _ := rfl

@[simp] theorem programExpansionHom_gate
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g)
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    programExpansionHom (program.gate line) =
      (programExpansionHom program).comp (lineReverseSubstitution line) := rfl

/-- Expanding a formal wire-variable gives the polynomial carried by that
wire in the original program. -/
theorem programExpansionHom_X
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g)
    (wire : Wire n g) :
    programExpansionHom program (MvPolynomial.X wire) =
      program.trace (polynomialInterpretation (Fin n)) MvPolynomial.X wire := by
  induction program with
  | empty =>
      refine Fin.addCases (fun input => ?_) (fun impossible => Fin.elim0 impossible)
        wire
      simp only [programExpansionHom_empty, AlgHom.id_apply, Program.trace,
        Fin.addCases_left]
      exact congrArg MvPolynomial.X (Fin.ext rfl)
  | @gate g program line inductionHypothesis =>
      refine Fin.lastCases ?_ (fun priorWire => ?_) wire
      · rw [programExpansionHom_gate, AlgHom.comp_apply]
        have eliminateLast :
            lineReverseSubstitution line
                (MvPolynomial.X (Fin.last (n.add g))) =
              lineFormalResult line := by
          exact lineReverseSubstitution_X_last line
        rw [eliminateLast]
        have outputTrace :
            (program.gate line).trace
                (polynomialInterpretation (Fin n)) MvPolynomial.X
                (Fin.last (n.add g)) =
              line.eval (polynomialInterpretation (Fin n))
                MvPolynomial.X
                (program.eval (polynomialInterpretation (Fin n))
                  MvPolynomial.X) := by
          unfold Program.trace
          rw [show Fin.last (n.add g) =
              Fin.natAdd n (Fin.last g) from Fin.ext rfl]
          rw [Fin.addCases_right]
          simp
        rw [outputTrace]
        cases line with
        | mk op wires =>
            cases op with
            | add =>
                change Fin 2 → Wire n g at wires
                simp [lineFormalResult, Line.eval,
                  polynomialInterpretation, inductionHypothesis,
                  Program.trace, Algebraic.Arithmetic.interpretation,
                  Function.comp_apply]
            | mul =>
                change Fin 2 → Wire n g at wires
                simp [lineFormalResult, Line.eval,
                  polynomialInterpretation, inductionHypothesis,
                  Program.trace, Algebraic.Arithmetic.interpretation,
                  Function.comp_apply]
            | constant impossible =>
                exact PEmpty.elim impossible
      · rw [programExpansionHom_gate, AlgHom.comp_apply,
          lineReverseSubstitution_X_castSucc,
          Program.trace_gate_castSucc]
        exact inductionHypothesis priorWire

/-- The formal output variable of a single-output circuit. -/
def circuitFormalOutput
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1) :
    MvPolynomial (Wire n g) ℕ :=
  MvPolynomial.X (circuit.outputs 0)

/-- Polynomial obtained by reverse-substituting every gate into the formal
output variable. -/
def circuitExpandedOutput
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1) :
    MvPolynomial (Fin n) ℕ :=
  programExpansionHom circuit.program (circuitFormalOutput circuit)

/-- Reverse substitution recovers ordinary polynomial evaluation. -/
theorem circuitExpandedOutput_eq_eval
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1) :
    circuitExpandedOutput circuit =
      circuit.eval (polynomialInterpretation (Fin n)) MvPolynomial.X 0 := by
  exact programExpansionHom_X circuit.program (circuit.outputs 0)

/-- A polymorphic polynomial progress measure compatible with the selected
operation cost. -/
structure Measure
    (operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)) where
  /-- Quantity assigned to polynomials over each finite variable set. -/
  value : ∀ variableCount : Nat,
    MvPolynomial (Fin variableCount) ℕ → Nat
  /-- A single formal variable has zero progress. -/
  variable_zero : ∀ variableCount (coordinate : Fin variableCount),
    value variableCount (MvPolynomial.X coordinate) = 0
  /-- Substituting the last variable by a sum grows by at most the addition
  charge. -/
  add_substitution_le : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
      (left right : Fin variableCount),
    value variableCount
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value (variableCount + 1) polynomial + operationCost .add
  /-- Substituting the last variable by a product grows by at most the
  multiplication charge. -/
  mul_substitution_le : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
      (left right : Fin variableCount),
    value variableCount
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value (variableCount + 1) polynomial + operationCost .mul

/-- One reverse gate substitution obeys the local progress estimate. -/
theorem Measure.reverseSubstitution_le
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g)
    (polynomial : MvPolynomial (Wire n (g + 1)) ℕ) :
    measure.value (n + g) (lineReverseSubstitution line polynomial) ≤
      measure.value (n + g + 1) polynomial + operationCost line.op := by
  cases line with
  | mk op wires =>
      cases op with
      | add =>
          change Fin 2 → Wire n g at wires
          simpa [lineReverseSubstitution, lineFormalResult,
            Nat.add_assoc] using
            measure.add_substitution_le (n + g) polynomial
              (wires (0 : Fin 2)) (wires (1 : Fin 2))
      | mul =>
          change Fin 2 → Wire n g at wires
          simpa [lineReverseSubstitution, lineFormalResult,
            Nat.add_assoc] using
            measure.mul_substitution_le (n + g) polynomial
              (wires (0 : Fin 2)) (wires (1 : Fin 2))
      | constant impossible =>
          exact PEmpty.elim impossible

/-- Reverse substitution telescopes local progress across a whole program. -/
theorem Measure.expansionHom_le_cost
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g)
    (polynomial : MvPolynomial (Wire n g) ℕ) :
    measure.value n (programExpansionHom program polynomial) ≤
      measure.value (n + g) polynomial + program.cost operationCost := by
  induction program with
  | empty => simp
  | @gate g program line inductionHypothesis =>
      calc
        measure.value n
            (programExpansionHom (program.gate line) polynomial) =
            measure.value n
              (programExpansionHom program
                (lineReverseSubstitution line polynomial)) := rfl
        _ ≤ measure.value (n + g) (lineReverseSubstitution line polynomial) +
              program.cost operationCost :=
          inductionHypothesis (lineReverseSubstitution line polynomial)
        _ ≤ (measure.value (n + (g + 1)) polynomial +
                operationCost line.op) +
              program.cost operationCost :=
          Nat.add_le_add_right
            (measure.reverseSubstitution_le line polynomial) _
        _ = measure.value (n + (g + 1)) polynomial +
              (program.gate line).cost operationCost := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The measure of the expanded output is bounded by circuit cost. -/
theorem Measure.expandedOutput_le_cost
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1) :
    measure.value n (circuitExpandedOutput circuit) ≤
      circuit.cost operationCost := by
  have bound := measure.expansionHom_le_cost circuit.program
    (circuitFormalOutput circuit)
  simpa [circuitExpandedOutput, circuitFormalOutput, Circuit.cost,
    measure.variable_zero] using bound

/-- Any constant-free arithmetic circuit producing a target polynomial pays
its progress measure. -/
theorem Measure.circuit_lowerBound
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    measure.value n target ≤ circuit.cost operationCost := by
  change circuit.eval (polynomialInterpretation (Fin n))
      MvPolynomial.X 0 = target at constructs
  rw [← constructs, ← circuitExpandedOutput_eq_eval circuit]
  exact measure.expandedOutput_le_cost circuit

end
end Progress
end Arithmetic
end Fusion
end Algebraic
