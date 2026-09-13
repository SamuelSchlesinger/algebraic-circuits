import Algebraic.Core
import Algebraic.Basis.DeMorgan.ShannonLupanov
import Algebraic.LowerBound.Counting.Sharp

/-!
# CSLib Boolean interoperability regressions

Import both public circuit APIs and both counting developments. Exercise
generic and Boolean computation together, multi-output round trips, and the
identity/constant cases where the two cost conventions differ.
-/

namespace AlgebraicTests.Boolean

open Algebraic

-- Arbitrary interpretations still use generic computation, including the
-- old explicitly qualified name.
example (circuit : Circuit σ n g m) (interpretation : Interpretation σ Nat) :
    Algebraic.Circuit.Computes circuit interpretation (circuit.eval interpretation) :=
  fun _ => rfl

-- The native scalar predicate and generic predicate can coexist in one import.
example : (Circuit.id Cslib.Circuits.Boolean.signature 1).Computes (fun input => input 0) := by
  intro input
  simp

example (circuit : Circuit Cslib.Circuits.Boolean.signature n g 1)
    (function : ScalarFunction Bool n) (computes : circuit.Computes function) :
    (DeMorgan.fromBoolean.compile circuit).ComputesWith DeMorgan.interpretation
      (fun input _ => function input) :=
  (DeMorgan.fromBoolean_computes circuit function).2 computes

-- All designated outputs, including direct input wires, survive a round trip.
example (circuit : Circuit DeMorgan.signature n g m) (input : Fin n → Bool) :
    (DeMorgan.fromBoolean.compile (DeMorgan.toBoolean.compile circuit)).eval
      DeMorgan.interpretation input = circuit.eval DeMorgan.interpretation input := by
  rw [Realization.compile_eval, Realization.compile_eval]

example (circuit : Circuit DeMorgan.signature n g m) :
    (DeMorgan.fromBoolean.compile (DeMorgan.toBoolean.compile circuit)).size ≤ circuit.size := by
  rw [DeMorgan.fromBoolean_size]
  exact DeMorgan.toBoolean_size_le circuit

-- Identity becomes a wire; constants remain gates with zero weighted cost.
example : (DeMorgan.toBoolean.operation .id).size = 0 := rfl

example : (DeMorgan.fromBoolean.compile
    ((Translation.id Cslib.Circuits.Boolean.signature).operation (.const false))).size = 1 := by
  rw [DeMorgan.fromBoolean_size]
  rfl

example : (DeMorgan.fromBoolean.compile
    ((Translation.id Cslib.Circuits.Boolean.signature).operation (.const false))).cost
      DeMorgan.standardCost = 0 := rfl

example (value : Bool) :
    (DeMorgan.toBoolean.compile
      ((Translation.id DeMorgan.signature).operation (if value then .true else .false))).Computes
        (fun _ => value) := by
  rw [DeMorgan.toBoolean_computes]
  intro input
  funext output
  have equal : output = 0 := Subsingleton.elim _ _
  rw [equal]
  cases value <;>
    exact congrFun
      (congrFun (Translation.pull_id (σ := DeMorgan.signature) DeMorgan.interpretation) _) input

-- Both sharp bounds apply to the same local minimum-gate complexity measure.
example (ε : Real) (positive : 0 < ε) :
    ∃ N : Nat, ∀ n ≥ N, ∃ function : ScalarFunction Bool n,
      2 ^ n / (n : Real) < (DeMorgan.complexity function : Real) ∧
        (DeMorgan.complexity function : Real) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨lowerCutoff, lower⟩ := DeMorgan.exists_complexity_gt_two_pow_div
  obtain ⟨upperCutoff, upper⟩ := DeMorgan.eventually_complexity_le_lupanov ε positive
  refine ⟨max lowerCutoff upperCutoff, fun n large => ?_⟩
  obtain ⟨function, hard⟩ := lower n ((le_max_left _ _).trans large)
  exact ⟨function, hard, upper n ((le_max_right _ _).trans large) function⟩

end AlgebraicTests.Boolean
