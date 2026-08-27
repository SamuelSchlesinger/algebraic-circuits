import Algebraic.Semantics
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

/-!
# Circuit input support

This file computes the original inputs that can affect each wire and proves
that circuit evaluation depends only on those inputs.
-/

namespace Algebraic

/-- The original inputs supporting a line, given the support of each wire. -/
def Line.inputSupport
    (line : Line σ n g)
    (wireSupport : Wire n g → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion fun k => wireSupport (line.wires k)

/-- Membership in a line's input support comes from one of its arguments. -/
@[simp] theorem Line.mem_inputSupport
    {line : Line σ n g}
    {wireSupport : Wire n g → Finset (Fin n)}
    {input : Fin n} :
    input ∈ line.inputSupport wireSupport ↔
      ∃ argument, input ∈ wireSupport (line.wires argument) := by
  simp [Line.inputSupport]

/-- The input support of every gate in a program. -/
def Program.gateSupport :
    (program : Program σ n g) → Fin g → Finset (Fin n)
  | .empty => Fin.elim0
  | .gate program line =>
      let prior := program.gateSupport
      let wireSupport := Fin.addCases (fun k => {k}) prior
      Fin.lastCases (line.inputSupport wireSupport) prior

/-- The input support of every input or gate wire in a program. -/
def Program.wireSupport
    (program : Program σ n g) : Wire n g → Finset (Fin n) :=
  Fin.addCases (fun k => {k}) program.gateSupport

/-- An input wire is supported only by that input. -/
@[simp] theorem Program.wireSupport_input
    (program : Program σ n g)
    (input : Fin n) :
    program.wireSupport (Wire.input (g := g) input) = {input} := by
  simp [Program.wireSupport, Wire.input]

/-- A gate-output wire has the support of that gate. -/
@[simp] theorem Program.wireSupport_gate
    (program : Program σ n g)
    (gate : Fin g) :
    program.wireSupport (Wire.gate (n := n) gate) =
      program.gateSupport gate := by
  simp [Program.wireSupport, Wire.gate]

/-- Adding a gate preserves the support of every earlier wire. -/
@[simp] theorem Program.wireSupport_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (wire : Wire n g) :
    (program.gate line).wireSupport wire.castSucc = program.wireSupport wire := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) wire
  · simp [Program.wireSupport, Program.gateSupport, Fin.castSucc_castAdd]
  · simp [Program.wireSupport, Program.gateSupport]

/-- The new wire is supported by precisely the inputs supporting the new line. -/
@[simp] theorem Program.wireSupport_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).wireSupport (Fin.last (n + g)) =
      line.inputSupport program.wireSupport := by
  rw [← Fin.natAdd_last (n := n) (m := g)]
  simp only [Program.wireSupport, Program.gateSupport,
    Fin.addCases_right, Fin.lastCases_last]
  rfl

/-- The input support of every designated output wire in a circuit. -/
def Circuit.outputSupport
    (c : Circuit σ n g m) : Fin m → Finset (Fin n) :=
  c.program.wireSupport ∘ c.outputs

/-- The union of the input supports of a circuit's outputs. -/
def Circuit.inputSupport (c : Circuit σ n g m) : Finset (Fin n) :=
  Finset.univ.biUnion c.outputSupport

/-- An input supports a circuit exactly when it supports a designated output wire. -/
@[simp] theorem Circuit.mem_inputSupport
    {c : Circuit σ n g m}
    {input : Fin n} :
    input ∈ c.inputSupport ↔
      ∃ output, input ∈ c.program.wireSupport (c.outputs output) := by
  simp [Circuit.inputSupport, Circuit.outputSupport]

/-- Program gates agree whenever their supporting inputs agree. -/
theorem Program.eval_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (k : Fin g)
    (agree : ∀ i ∈ program.gateSupport k, left i = right i) :
    program.eval interpretation left k = program.eval interpretation right k := by
  induction program with
  | empty => exact Fin.elim0 k
  | @gate g program line ih =>
      revert agree
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro agree
        simp only [Program.eval, Fin.lastCases_last]
        unfold Line.eval
        congr 1
        funext argument
        simp only [Function.comp_apply]
        let wireSupport : Wire n g → Finset (Fin n) :=
          Fin.addCases (fun k => {k}) program.gateSupport
        have agreeOnLine :
            ∀ i ∈ line.inputSupport wireSupport, left i = right i := by
          simpa [Program.gateSupport] using agree
        have wireValueEqual (wire : Wire n g) :
            (∀ i ∈ wireSupport wire, left i = right i) →
            (Fin.addCases left (program.eval interpretation left) wire : U) =
              (Fin.addCases right (program.eval interpretation right) wire : U) := by
          refine Fin.addCases ?_ ?_ wire
          · intro i h
            simpa using h i (by simp [wireSupport])
          · intro j h
            simpa using ih j (fun i hi =>
              h i (by simpa [wireSupport] using hi))
        exact wireValueEqual (line.wires argument) fun i hi =>
          agreeOnLine i (Line.mem_inputSupport.mpr ⟨argument, hi⟩)
      · intro agree
        simp only [Program.eval, Fin.lastCases_castSucc]
        apply ih j
        simpa [Program.gateSupport] using agree

/-- Program traces agree on any wire whose supporting inputs agree. -/
theorem Program.trace_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (wire : Wire n g)
    (agree : ∀ i ∈ program.wireSupport wire, left i = right i) :
    program.trace interpretation left wire =
      program.trace interpretation right wire := by
  unfold Program.trace
  revert agree
  refine Fin.addCases ?_ ?_ wire
  · intro input agree
    simpa using agree input (by simp [Program.wireSupport])
  · intro gate agree
    simp only [Fin.addCases_right]
    apply program.eval_congr interpretation left right gate
    intro input present
    exact agree input (by simpa [Program.wireSupport] using present)

/-- Circuit evaluation depends only on the circuit's structural input support. -/
theorem Circuit.eval_dependsOnlyOn
    (c : Circuit σ n g m)
    (interpretation : Interpretation σ U) :
    DependsOnlyOn (c.eval interpretation) c.inputSupport := by
  intro left right agree
  funext output
  apply c.program.trace_congr interpretation left right (c.outputs output)
  intro input present
  exact agree input (Circuit.mem_inputSupport.mpr ⟨output, present⟩)

/-- A computed function depends only on the circuit's structural input support. -/
theorem Circuit.Computes.dependsOnlyOn
    {c : Circuit σ n g m}
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    (computes : c.Computes interpretation target) :
    DependsOnlyOn target c.inputSupport := by
  intro left right agree
  rw [← computes left, ← computes right]
  exact c.eval_dependsOnlyOn interpretation left right agree

end Algebraic
