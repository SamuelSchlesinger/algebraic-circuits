import Algebraic.Basis.DeMorgan.Restriction

/-!
# Restricting one-output De Morgan circuits

This module adds the terminal output gate to `ProgramRestriction`.  Deleted
charged gates are indexed uniformly by `Fin (g + 1)`: internal gate `k` is
`k.castSucc`, and the terminal output is `Fin.last g`.  The resulting exact
cost identity is exposed as a standard `Circuit.Reduction` certificate.
-/

namespace Algebraic
namespace DeMorgan

/-- Append a one-output circuit's terminal line to its internal program. -/
def outputProgram
    (source : Circuit signature n g 1) : Program signature n (g + 1) :=
  source.program.gate (source.outputs 0)

/-- The last wire of `outputProgram` is the circuit output. -/
@[simp] theorem outputProgram_trace_last
    (source : Circuit signature n g 1)
    (input : Fin n → Bool) :
    (outputProgram source).trace interpretation input (Fin.last (n + g)) =
      source.eval interpretation input 0 := by
  rw [outputProgram, Program.trace_gate_last]
  rfl

/-- The last wire of `outputProgram` has exactly the circuit's input support. -/
@[simp] theorem outputProgram_support_last
    (source : Circuit signature n g 1) :
    (outputProgram source).wireSupport (Fin.last (n + g)) =
      source.inputSupport := by
  rw [outputProgram, Program.wireSupport_gate_last]
  simp [Circuit.inputSupport, Circuit.outputSupport]

/--
Restriction of a one-output De Morgan circuit, with the exact set of deleted
charged source gates.
-/
structure CircuitRestriction
    (source : Circuit signature (n + 1) g 1)
    (selected : Fin (n + 1))
    (fixedValue : Bool) where
  /-- Number of internal gates in the residual circuit. -/
  gateCount : Nat
  /-- Residual circuit on the remaining inputs. -/
  result : Circuit signature n gateCount 1
  /-- Deleted charged gates; `Fin.last g` denotes the terminal output gate. -/
  deleted : Finset (Fin (g + 1))
  /-- Pointwise semantics under the chosen input restriction. -/
  eval_eq : ∀ input,
    result.eval interpretation input =
      source.eval interpretation
        ((InputSubstitution.fix selected fixedValue).apply input)
  /-- The deletion set accounts exactly for the charged-cost decrease. -/
  cost_eq : deleted.card + result.cost binaryCost = source.cost binaryCost

namespace CircuitRestriction

/--
Turn a restriction of the program obtained by appending the sole output line
back into a one-output circuit restriction.  The appended gate's residual value
is exposed through a free terminal line.
-/
def ofOutputProgram
    {source : Circuit signature (n + 1) g 1}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (program : ProgramRestriction
      (outputProgram source) selected fixedValue) :
    CircuitRestriction source selected fixedValue := by
  let outputValue := program.values (Fin.last ((n + 1) + g))
  let result : Circuit signature n program.gateCount 1 :=
    { program := program.result
      outputs := fun _ => outputValue.outputLine }
  exact
    { gateCount := program.gateCount
      result := result
      deleted := program.deleted
      eval_eq := by
        intro input
        funext output
        have output_eq : output = 0 := Fin.eq_zero output
        subst output
        change outputValue.outputLine.eval interpretation input
            (program.result.eval interpretation input) = _
        rw [ResidualValue.outputLine_eval]
        calc
          outputValue.eval program.result input =
              (outputProgram source).trace interpretation
                ((InputSubstitution.fix selected fixedValue).apply input)
                (Fin.last ((n + 1) + g)) :=
            program.trace_eq input (Fin.last ((n + 1) + g))
          _ = source.eval interpretation
                ((InputSubstitution.fix selected fixedValue).apply input) 0 := by
            exact outputProgram_trace_last source _
      cost_eq := by
        have programCost := program.cost_eq
        simpa [result, outputProgram, Circuit.cost] using programCost }

/-- View an exact circuit restriction as a generic certified reduction. -/
def toReduction
    {source : Circuit signature (n + 1) g 1}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : CircuitRestriction source selected fixedValue) :
    Circuit.Reduction binaryCost source interpretation
      (InputSubstitution.fix selected fixedValue) where
  gateCount := restriction.gateCount
  result := restriction.result
  eval_eq := restriction.eval_eq
  saving := restriction.deleted.card
  saving_le := restriction.cost_eq.le

end CircuitRestriction

/-- Partial-evaluate a one-output circuit after fixing one input. -/
noncomputable def restrictCircuit
    (source : Circuit signature (n + 1) g 1)
    (selected : Fin (n + 1))
    (fixedValue : Bool) :
    CircuitRestriction source selected fixedValue := by
  exact CircuitRestriction.ofOutputProgram
    (restrictProgram selected fixedValue
      (outputProgram source))

/-- Circuit restriction exposes exactly the appended program's deletion set. -/
@[simp] theorem restrictCircuit_deleted
    (source : Circuit signature (n + 1) g 1)
    (selected : Fin (n + 1))
    (fixedValue : Bool) :
    (restrictCircuit source selected fixedValue).deleted =
      (restrictProgram selected fixedValue (outputProgram source)).deleted := rfl

end DeMorgan
end Algebraic
