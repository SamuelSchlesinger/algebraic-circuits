import Algebraic.Basis.DeMorgan.CircuitRestriction
import Algebraic.Basis.DeMorgan.RestrictionAnalysis

/-!
# Source-gate restriction regressions

Exercise free input outputs, constant and negated residual outputs, and
charged deletion accounting using only focused restriction imports.
-/

namespace AlgebraicTests.Restriction

open Algebraic Algebraic.DeMorgan

private def projection (index : Fin 2) : Circuit signature 2 0 1 where
  program := .empty
  outputs := fun _ => Wire.input index

-- A surviving input is reused without adding any output gate.
example (value : Bool) : (restrictCircuit (projection 1) 0 value).gateCount = 0 := rfl

example (value : Bool) (input : Fin 1 → Bool) :
    (restrictCircuit (projection 1) 0 value).result.eval interpretation input 0 = input 0 := rfl

-- Fixing the output itself needs one free constant gate, even with no inputs left.
private def singleInput : Circuit signature 1 0 1 where
  program := .empty
  outputs := fun _ => Wire.input 0

example (value : Bool) : (restrictCircuit singleInput 0 value).gateCount = 1 := rfl

example (value : Bool) (input : Fin 0 → Bool) :
    (restrictCircuit singleInput 0 value).result.eval interpretation input 0 = value := by
  cases value <;> rfl

private def negatedInput : Circuit signature 2 1 1 where
  program := Program.empty.gate (notLine (Wire.input 1))
  outputs := fun _ => Wire.gate 0

-- A signed residual output must materialize its final negation.
example (value : Bool) : (restrictCircuit negatedInput 0 value).gateCount = 1 := rfl

example (value : Bool) (input : Fin 1 → Bool) :
    (restrictCircuit negatedInput 0 value).result.eval interpretation input 0 = !(input 0) := rfl

example (value : Bool) : (restrictCircuit negatedInput 0 value).result.cost binaryCost = 0 := rfl

private def conjunction : Circuit signature 2 1 1 where
  program := Program.empty.gate (binaryLine .and (Wire.input 0) (Wire.input 1))
  outputs := fun _ => Wire.gate 0

-- Deleting a charged gate records its actual source index.
example (value : Bool) :
    (0 : Fin 1) ∈ (restrictCircuit conjunction 0 value).deleted := by
  apply restrictProgram_deleted_of_readsInput
  exact ⟨rfl, ⟨0, by decide⟩, false, rfl⟩

example (value : Bool) : (restrictCircuit conjunction 0 value).deleted.card = 1 := by
  have member : (0 : Fin 1) ∈ (restrictCircuit conjunction 0 value).deleted := by
    apply restrictProgram_deleted_of_readsInput
    exact ⟨rfl, ⟨0, by decide⟩, false, rfl⟩
  have bound := Finset.card_le_univ (s := (restrictCircuit conjunction 0 value).deleted)
  have positive := Finset.card_pos.mpr ⟨0, member⟩
  simpa using Nat.le_antisymm bound positive

example (value : Bool) : (restrictCircuit conjunction 0 value).result.cost binaryCost = 0 := by
  have accounting := (restrictCircuit conjunction 0 value).cost_eq
  have member : (0 : Fin 1) ∈ (restrictCircuit conjunction 0 value).deleted := by
    apply restrictProgram_deleted_of_readsInput
    exact ⟨rfl, ⟨0, by decide⟩, false, rfl⟩
  have positive := Finset.card_pos.mpr ⟨0, member⟩
  change _ + _ = 1 at accounting
  omega

-- A designated output may precede unused source gates.
private def unusedGate : Circuit signature 2 1 1 where
  program := conjunction.program
  outputs := fun _ => Wire.input 1

example (input : Fin 1 → Bool) :
    (restrictCircuit unusedGate 0 false).result.eval interpretation input 0 = input 0 := by
  calc
    _ = unusedGate.eval interpretation ((InputSubstitution.fix 0 false).apply input) 0 :=
      congrFun ((restrictCircuit unusedGate 0 false).eval_eq input) 0
    _ = input 0 := rfl

end AlgebraicTests.Restriction
