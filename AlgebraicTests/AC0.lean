import Algebraic.Basis.AC0

/-!
# AC0 basis and class regressions

The examples distinguish generic circuit depth from source logical depth on an
input negation and show that arbitrary-width disjunction forms a nonuniform
AC0 family without executable proof certificates.
-/

namespace AlgebraicTests.AC0

open Algebraic

/-- One arbitrary-fan-in OR gate. -/
def orAllCircuit (n : Nat) : Circuit AC0.signature n 1 1 where
  program := .gate .empty {
    op := .or n
    wires := Wire.input
  }
  outputs := fun _ => Wire.gate 0

/-- One input-literal negation. -/
def notInputCircuit : Circuit AC0.signature 1 1 1 where
  program := .gate .empty {
    op := .not
    wires := fun _ => Wire.input 0
  }
  outputs := fun _ => Wire.gate 0

theorem orAllCircuit_eval (input : Fin n -> Bool) :
    (orAllCircuit n).eval AC0.interpretation input 0 =
      decide (Exists fun k => input k = true) := by
  simp only [orAllCircuit, Circuit.eval, Function.comp_apply,
    Program.trace_gateWire, Program.gateFunction_apply]
  rw [show (0 : Fin 1) = Fin.last 0 by rfl, Program.eval_gate_last]
  simp [Line.eval, Program.eval, AC0.interpretation]

example (n : Nat) : (orAllCircuit n).cost AC0.andOrCost = 1 := by
  simp [orAllCircuit, Circuit.cost, Program.cost]

theorem orAllCircuit_logicalDepth (n : Nat) :
    AC0.Circuit.logicalDepth (orAllCircuit n) = 1 := by
  rw [AC0.Circuit.logicalDepth_one_output]
  simp only [AC0.Circuit.logicalOutputDepths, orAllCircuit, Circuit.eval,
    Function.comp_apply, Program.trace_gateWire,
    Program.gateFunction_apply]
  rw [show (0 : Fin 1) = Fin.last 0 by rfl, Program.eval_gate_last]
  simp only [Line.eval, Program.eval]
  have values_eq :
      (Fin.addCases (fun _ : Fin n => 0) Fin.elim0 : Wire n 0 -> Nat) ∘
          Wire.input =
        (fun _ : Fin n => 0) := by
    funext argument
    simp
  rw [values_eq]
  exact AC0.logicalDepthInterpretation_or_zero n

example : notInputCircuit.depth = 1 := rfl

example : AC0.Circuit.logicalDepth notInputCircuit = 0 := rfl

example : notInputCircuit.cost AC0.andOrCost = 0 := rfl

example : AC0.Circuit.NormalForm notInputCircuit := by
  simp [AC0.Circuit.NormalForm, AC0.Program.NegationsAtInputs,
    AC0.Program.Alternating, AC0.Line.NegationAtInput,
    AC0.Line.AlternatesAfter, notInputCircuit]

/-- The all-input disjunction family. -/
def orAllFamily : Circuit.Family AC0.signature 1 where
  gateCount := fun _ => 1
  circuit := orAllCircuit

/-- The semantic all-input disjunction family. -/
def orTarget : Target.Family Bool 1 :=
  Target.scalarFamily fun n input =>
    decide (Exists fun k : Fin n => input k = true)

theorem orAllFamily_computes :
    orAllFamily.Computes AC0.interpretation orTarget := by
  intro n input
  funext output
  have output_eq : output = 0 := Fin.eq_zero output
  subst output
  simpa [orAllFamily, orTarget, Target.scalarFamily] using
    orAllCircuit_eval input

theorem orAllFamily_normal : AC0.Family.NormalForm orAllFamily := by
  intro n
  simp [AC0.Circuit.NormalForm, AC0.Program.NegationsAtInputs,
    AC0.Program.Alternating, AC0.Line.NegationAtInput,
    AC0.Line.AlternatesAfter, orAllFamily, orAllCircuit]

theorem orAllFamily_smallDepth : AC0.Family.IsSmallDepth orAllFamily := by
  refine ⟨?_, ?_, orAllFamily_normal⟩
  · exact ⟨1, 0, fun n => by simp [Circuit.Family.cost, orAllFamily,
      orAllCircuit, Circuit.cost, Program.cost]⟩
  · refine ⟨1, ?_⟩
    intro n
    simpa [AC0.Family.logicalDepth, orAllFamily] using
      Nat.le_of_eq (orAllCircuit_logicalDepth n)

example : AC0.Computable orTarget :=
  ⟨orAllFamily, orAllFamily_computes, orAllFamily_smallDepth⟩

end AlgebraicTests.AC0
