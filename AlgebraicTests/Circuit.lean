import Algebraic.Basis.DeMorgan
import Algebraic.Basis.DeMorgan.Wiring
import Algebraic.Support

/-!
# Circuit API regressions

These tests exercise shared gates, direct and duplicated outputs, nullary
operations, zero-output circuits, and the size, depth, support, and cost
conventions of the public circuit model.
-/

namespace AlgebraicTests.Circuit

open Algebraic

/-- Conjoin the first two inputs. -/
def andInputs : Line DeMorgan.signature 3 0 where
  op := .and
  wires := Fin.cases (Wire.input 0) fun _ => Wire.input 1

/-- Negate the shared conjunction. -/
def notConjunction : Line DeMorgan.signature 3 1 where
  op := .not
  wires := fun _ => Wire.gate 0

/-- A two-gate program with one shared intermediate value. -/
def sharedProgram : Program DeMorgan.signature 3 2 :=
  .gate (.gate .empty andInputs) notConjunction

/-- Expose the negated conjunction twice and the untouched third input once. -/
def sharedCircuit : Circuit DeMorgan.signature 3 2 3 where
  program := sharedProgram
  outputs := Fin.cases (Wire.gate 1) <| Fin.cases (Wire.input 2) fun _ =>
    Wire.gate 1

def sampleInput : Fin 3 → Bool :=
  Fin.cases true <| Fin.cases false fun _ => true

example : sharedCircuit.eval DeMorgan.interpretation sampleInput 0 = true := rfl

example : sharedCircuit.eval DeMorgan.interpretation sampleInput 1 = true := rfl

example : sharedCircuit.eval DeMorgan.interpretation sampleInput 2 = true := rfl

example : sharedCircuit.size = 2 := rfl

example : sharedCircuit.depth = 2 := rfl

example : sharedCircuit.cost DeMorgan.binaryCost = 1 := rfl

example : sharedCircuit.inputSupport = Finset.univ := by
  native_decide

example : sharedCircuit.FanInAtMost 2 := by
  decide

/-- A zero-gate circuit may designate input wires directly. -/
def swap : Circuit DeMorgan.signature 2 0 2 where
  program := .empty
  outputs := Fin.cases (Wire.input 1) fun _ => Wire.input 0

def trueFalse : Fin 2 → Bool :=
  Fin.cases true fun _ => false

example : swap.eval DeMorgan.interpretation trueFalse 0 = false := rfl

example : swap.eval DeMorgan.interpretation trueFalse 1 = true := rfl

example : swap.size = 0 := rfl

example : swap.depth = 0 := rfl

/-- A circuit with no designated outputs has depth and support zero. -/
def noOutputs : Circuit DeMorgan.signature 3 2 0 where
  program := sharedProgram
  outputs := Fin.elim0

example : noOutputs.depth = 0 := rfl

example : noOutputs.inputSupport = ∅ := by
  native_decide

/-- A nullary gate remains available when there are no original inputs. -/
def falseCircuit : Circuit DeMorgan.signature 0 1 1 where
  program := .gate .empty { op := .false, wires := Fin.elim0 }
  outputs := fun _ => Wire.gate 0

example :
    falseCircuit.eval DeMorgan.interpretation Fin.elim0 0 = false := rfl

example : falseCircuit.depth = 1 := rfl

example : falseCircuit.inputSupport = ∅ := by
  native_decide

example : falseCircuit.FanInAtMost 0 := by
  decide

/-! A wiring specification mixes existing inputs with free constants. -/

def sampleWiring : Fin 3 → DeMorgan.Wiring 2 :=
  ![.input 1, .constant true, .input 0]

example :
    (DeMorgan.Wiring.circuit sampleWiring).eval
      DeMorgan.interpretation trueFalse 0 = false := by
  rw [DeMorgan.Wiring.circuit_eval]
  rfl

example :
    (DeMorgan.Wiring.circuit sampleWiring).eval
      DeMorgan.interpretation trueFalse 1 = true := by
  rw [DeMorgan.Wiring.circuit_eval]
  rfl

example :
    (DeMorgan.Wiring.circuit sampleWiring).cost
      DeMorgan.standardCost = 0 := by
  simp

end AlgebraicTests.Circuit
