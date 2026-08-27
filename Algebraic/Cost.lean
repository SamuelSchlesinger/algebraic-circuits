import Algebraic.Circuit

/-!
# Weighted circuit cost

Gate-elimination arguments often count only selected operations. An operation
cost assigns a natural-number weight to every symbol; program and circuit cost
are the corresponding sums over gates. Designating output wires is free.
-/

namespace Algebraic

/-- A natural-number cost assigned to every operation in a signature. -/
abbrev OperationCost (σ : Signature) := σ.Op → Nat

/-- Unit cost charges one for every gate. -/
def OperationCost.unit : OperationCost σ := fun _ => 1

/-- The cost of all gates in a straight-line program. -/
def Program.cost (operationCost : OperationCost σ) :
    Program σ n g → Nat
  | .empty => 0
  | .gate program line =>
      program.cost operationCost + operationCost line.op

@[simp] theorem Program.cost_empty
    (operationCost : OperationCost σ) :
    (Program.empty : Program σ n 0).cost operationCost = 0 := rfl

@[simp] theorem Program.cost_gate
    (operationCost : OperationCost σ)
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).cost operationCost =
      program.cost operationCost + operationCost line.op := rfl

/-- If every operation costs at most `K`, a program of `g` gates costs at most
`K * g`. -/
theorem Program.cost_le_mul_gateCount
    (program : Program σ n g)
    (operationCost : OperationCost σ)
    (bounded : ∀ op, operationCost op ≤ K) :
    program.cost operationCost ≤ K * g := by
  induction program with
  | empty => simp
  | @gate g program line ih =>
      calc
        (program.gate line).cost operationCost =
            program.cost operationCost + operationCost line.op := rfl
        _ ≤ K * g + K := Nat.add_le_add ih (bounded line.op)
        _ = K * (g + 1) := (Nat.mul_succ K g).symm

/-- Unit cost is exactly the number of program gates. -/
@[simp] theorem Program.cost_unit
    (program : Program σ n g) :
    program.cost OperationCost.unit = g := by
  induction program with
  | empty => rfl
  | gate program line ih =>
      simp [Program.cost, OperationCost.unit, ih]

/-- The cost of all gates in a circuit. -/
def Circuit.cost
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost σ) : Nat :=
  circuit.program.cost operationCost

@[simp] theorem Circuit.cost_id
    (operationCost : OperationCost σ) :
    (Circuit.id σ n).cost operationCost = 0 := rfl

/-- If every operation costs at most `K`, circuit cost is at most `K` times
its gate count. -/
theorem Circuit.cost_le_mul_size
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost σ)
    (bounded : ∀ op, operationCost op ≤ K) :
    circuit.cost operationCost ≤ K * circuit.size := by
  exact circuit.program.cost_le_mul_gateCount operationCost bounded

/-- Unit cost is exactly circuit size. -/
@[simp] theorem Circuit.cost_unit
    (circuit : Circuit σ n g m) :
    circuit.cost OperationCost.unit = circuit.size := by
  exact circuit.program.cost_unit

end Algebraic
