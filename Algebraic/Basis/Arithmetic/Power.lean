import Algebraic.Basis.Arithmetic.Expression
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Log

/-!
# Shared arithmetic power circuits

Binary powering is a small but important reusable DAG primitive.  Unlike a
tree expression for repeated multiplication, each recursively computed power
is shared by the squaring gate.  For positive exponent `e`, the resulting
number of multiplication gates is at most `2 * Nat.log2 e`.
-/

namespace Algebraic
namespace Arithmetic
namespace Power

variable {K R : Type}

/-- Append one gate that squares the output of a one-output circuit. -/
def squareCircuit
    (circuit : Circuit (Arithmetic.signature K) 1 g 1) :
    Circuit (Arithmetic.signature K) 1 (g + 1) 1 where
  program := circuit.program.gate
    { op := .mul
      wires := fun _ ↦ circuit.outputs 0 }
  outputs := fun _ ↦ Wire.gate (Fin.last g)

/-- Append one gate that multiplies a circuit's output by its original input.
The original input remains available because programs retain their input-wire
namespace. -/
def multiplyInputCircuit
    (circuit : Circuit (Arithmetic.signature K) 1 g 1) :
    Circuit (Arithmetic.signature K) 1 (g + 1) 1 where
  program := circuit.program.gate
    { op := .mul
      wires := fun argument ↦
        Fin.cases (circuit.outputs 0) (fun _ ↦ Wire.input 0) argument }
  outputs := fun _ ↦ Wire.gate (Fin.last g)

/-- Squaring has the expected semantics. -/
theorem squareCircuit_eval
    [Add R]
    [Mul R]
    (constant : K → R)
    (input : Fin 1 → R)
    (circuit : Circuit (Arithmetic.signature K) 1 g 1) :
    (squareCircuit circuit).eval (Arithmetic.interpretation constant) input 0 =
      circuit.eval (Arithmetic.interpretation constant) input 0 *
        circuit.eval (Arithmetic.interpretation constant) input 0 := by
  change (circuit.program.gate _).trace
      (Arithmetic.interpretation constant) input (Fin.last (1 + g)) = _
  rw [Program.trace_gate_last]
  change circuit.program.trace (Arithmetic.interpretation constant) input
      (circuit.outputs 0) *
        circuit.program.trace (Arithmetic.interpretation constant) input
          (circuit.outputs 0) = _
  rfl

/-- Multiplication by the retained input has the expected semantics. -/
theorem multiplyInputCircuit_eval
    [Add R]
    [Mul R]
    (constant : K → R)
    (input : Fin 1 → R)
    (circuit : Circuit (Arithmetic.signature K) 1 g 1) :
    (multiplyInputCircuit circuit).eval
        (Arithmetic.interpretation constant) input 0 =
      circuit.eval (Arithmetic.interpretation constant) input 0 * input 0 := by
  change (circuit.program.gate _).trace
      (Arithmetic.interpretation constant) input (Fin.last (1 + g)) = _
  rw [Program.trace_gate_last]
  change circuit.program.trace (Arithmetic.interpretation constant) input
      (circuit.outputs 0) *
        circuit.program.trace (Arithmetic.interpretation constant) input
          (Wire.input 0) = _
  rw [Program.trace_input]
  rfl

/-- Squaring adds exactly one multiplication to the circuit cost. -/
@[simp] theorem squareCircuit_multiplicationCost
    (circuit : Circuit (Arithmetic.signature K) 1 g 1) :
    (squareCircuit circuit).cost
        (Arithmetic.multiplicationCost (K := K)) =
      circuit.cost (Arithmetic.multiplicationCost (K := K)) + 1 := rfl

/-- Multiplication by the retained input adds exactly one multiplication. -/
@[simp] theorem multiplyInputCircuit_multiplicationCost
    (circuit : Circuit (Arithmetic.signature K) 1 g 1) :
    (multiplyInputCircuit circuit).cost
        (Arithmetic.multiplicationCost (K := K)) =
      circuit.cost (Arithmetic.multiplicationCost (K := K)) + 1 := rfl

/-- A shared binary-power circuit, packaged with its inferred gate count.
Zero uses one free constant gate; one is the zero-gate identity; each further
binary digit contributes one squaring and, for a one bit, one multiplication
by the retained input. -/
def binaryCircuit
    [One K]
    (exponent : Nat) :
    Σ gateCount, Circuit (Arithmetic.signature K) 1 gateCount 1 :=
  Nat.binaryRecFromOne
    ⟨1, Algebraic.Arithmetic.Expression.circuit (.constant 1)⟩
    ⟨0, Circuit.id (Arithmetic.signature K) 1⟩
    (fun bit _exponent _nonzero prior ↦
      if bit then
        ⟨prior.1 + 2,
          multiplyInputCircuit (squareCircuit prior.2)⟩
      else
        ⟨prior.1 + 1, squareCircuit prior.2⟩)
    exponent

/-- Exact number of multiplication gates used by `binaryCircuit`. -/
def binaryMultiplicationCount (exponent : Nat) : Nat :=
  Nat.binaryRecFromOne 0 0
    (fun bit _exponent _nonzero prior ↦ prior + 1 + bit.toNat)
    exponent

@[simp] theorem binaryCircuit_zero
    [One K] :
    binaryCircuit (K := K) 0 =
      ⟨1, Algebraic.Arithmetic.Expression.circuit (.constant 1)⟩ := by
  simp [binaryCircuit]

@[simp] theorem binaryCircuit_one
    [One K] :
    binaryCircuit (K := K) 1 =
      ⟨0, Circuit.id (Arithmetic.signature K) 1⟩ := by
  simp [binaryCircuit]

theorem binaryCircuit_bit
    [One K]
    (bit : Bool)
    (exponent : Nat)
    (nonzero : exponent ≠ 0) :
    binaryCircuit (K := K) (Nat.bit bit exponent) =
      if bit then
        ⟨(binaryCircuit (K := K) exponent).1 + 2,
          multiplyInputCircuit
            (squareCircuit (binaryCircuit (K := K) exponent).2)⟩
      else
        ⟨(binaryCircuit (K := K) exponent).1 + 1,
          squareCircuit (binaryCircuit (K := K) exponent).2⟩ := by
  unfold binaryCircuit
  rw [Nat.binaryRecFromOne_eq bit exponent nonzero]

@[simp] theorem binaryMultiplicationCount_zero :
    binaryMultiplicationCount 0 = 0 := by
  simp [binaryMultiplicationCount]

@[simp] theorem binaryMultiplicationCount_one :
    binaryMultiplicationCount 1 = 0 := by
  simp [binaryMultiplicationCount]

theorem binaryMultiplicationCount_bit
    (bit : Bool)
    (exponent : Nat)
    (nonzero : exponent ≠ 0) :
    binaryMultiplicationCount (Nat.bit bit exponent) =
      binaryMultiplicationCount exponent + 1 + bit.toNat := by
  unfold binaryMultiplicationCount
  rw [Nat.binaryRecFromOne_eq bit exponent nonzero]

/-- Binary compilation computes the requested natural power. -/
theorem binaryCircuit_eval
    [Semiring R]
    [One K]
    (constant : K → R)
    (mapsOne : constant 1 = 1)
    (input : Fin 1 → R)
    (exponent : Nat) :
    (binaryCircuit (K := K) exponent).2.eval
        (Arithmetic.interpretation constant) input 0 = input 0 ^ exponent := by
  induction exponent using Nat.binaryRecFromOne with
  | zero =>
      rw [binaryCircuit_zero,
        Algebraic.Arithmetic.Expression.circuit_eval]
      simp [Algebraic.Arithmetic.Expression.eval, mapsOne]
  | one =>
      rw [binaryCircuit_one]
      rw [pow_one]
      exact congrFun
        (Circuit.eval_id (σ := Arithmetic.signature K)
          (Arithmetic.interpretation constant) input) 0
  | bit bit exponent nonzero inductionHypothesis =>
      rw [binaryCircuit_bit bit exponent nonzero]
      cases bit with
      | false =>
          rw [if_neg (by decide),
            squareCircuit_eval, inductionHypothesis]
          rw [← pow_add]
          congr 1
          simp only [Nat.bit_false_apply]
          omega
      | true =>
          rw [if_pos rfl, multiplyInputCircuit_eval,
            squareCircuit_eval, inductionHypothesis]
          rw [← pow_add, ← pow_succ]
          congr 1
          simp only [Nat.bit_true_apply]
          omega

/-- The multiplication cost of binary compilation is exactly the recursive
binary count. -/
@[simp] theorem binaryCircuit_multiplicationCost
    [One K]
    (exponent : Nat) :
    (binaryCircuit (K := K) exponent).2.cost
        (Arithmetic.multiplicationCost (K := K)) =
      binaryMultiplicationCount exponent := by
  induction exponent using Nat.binaryRecFromOne with
  | zero =>
      rw [binaryCircuit_zero]
      rfl
  | one =>
      rw [binaryCircuit_one]
      rfl
  | bit bit exponent nonzero inductionHypothesis =>
      rw [binaryCircuit_bit bit exponent nonzero,
        binaryMultiplicationCount_bit bit exponent nonzero]
      cases bit <;> simp [inductionHypothesis]

/-- Binary powering uses at most twice the base-two logarithm many
multiplications for every positive exponent. -/
theorem binaryMultiplicationCount_le_two_mul_log2
    (exponent : Nat)
    (positive : 0 < exponent) :
    binaryMultiplicationCount exponent ≤ 2 * Nat.log2 exponent := by
  revert positive
  induction exponent using Nat.binaryRecFromOne with
  | zero => omega
  | one => simp
  | bit bit exponent nonzero inductionHypothesis =>
      intro _positive
      rw [binaryMultiplicationCount_bit bit exponent nonzero,
        Nat.log2_eq_log_two, Nat.log_two_bit nonzero]
      have prior := inductionHypothesis (Nat.pos_of_ne_zero nonzero)
      rw [Nat.log2_eq_log_two] at prior
      cases bit <;> simp at * <;> omega

end Power
end Arithmetic
end Algebraic
