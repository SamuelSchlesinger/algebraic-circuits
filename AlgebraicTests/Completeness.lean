import Algebraic.Basis.DeMorgan.Completeness

/-!
# Elementary Boolean synthesis without sharp synthesis imports

These examples use only the completeness module. The import check prevents
minimum-complexity or asymptotic synthesis infrastructure from becoming a
prerequisite for elementary representability.
-/

open Algebraic Algebraic.DeMorgan

example (value : Bool) :
    Expression.ofFunction (fun _ : Fin 0 → Bool => value) = .constant value := rfl

example (input : Fin 2 → Bool) :
    (Expression.ofFunction (fun values : Fin 2 → Bool => Bool.xor (values 0) (values 1))).eval
      input = Bool.xor (input 0) (input 1) := by
  simp

example (function : ScalarFunction Bool n) :
    (Expression.ofFunction function).circuit.ComputesWith interpretation
      (fun input _ => function input) := by
  intro input
  funext output
  have equal : output = 0 := Fin.eq_zero output
  simp [equal]

example (target : Target Bool 0 3) :
    ∃ gates, ∃ circuit : Circuit signature 0 gates 3,
      circuit.ComputesWith interpretation target :=
  functionallyComplete 0 3 target

example (target : Target Bool 2 0) :
    ∃ gates, ∃ circuit : Circuit signature 2 gates 0,
      circuit.ComputesWith interpretation target :=
  functionallyComplete 2 0 target

run_cmd do
  for name in (← Lean.getEnv).header.moduleNames do
    if (`Algebraic.MassProduction).isPrefixOf name ||
        (`Algebraic.LowerBound).isPrefixOf name || name == `Algebraic.Complexity ||
        name == `Algebraic.Basis.DeMorgan.Complexity ||
        name.toString.startsWith "Cslib.Computability.Circuit.Boolean.Lupanov" then
      throwError "Elementary completeness unexpectedly imports {name}"
