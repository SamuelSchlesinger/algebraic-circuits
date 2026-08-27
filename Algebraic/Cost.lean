import Algebraic.Circuit
import Mathlib.Data.Fintype.BigOperators

/-!
# Weighted circuit cost

Gate-elimination arguments often count only selected operations. An operation
cost assigns a natural-number weight to every symbol; program and circuit cost
are the corresponding sums over internal and terminal gates.
-/

namespace Algebraic

/-- A natural-number cost assigned to every operation in a signature. -/
abbrev OperationCost (σ : Signature) := σ.Op → Nat

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

/-- The cost of all internal and terminal gates in a circuit. -/
def Circuit.cost
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost σ) : Nat :=
  circuit.program.cost operationCost +
    ∑ output, operationCost (circuit.outputs output).op

end Algebraic
