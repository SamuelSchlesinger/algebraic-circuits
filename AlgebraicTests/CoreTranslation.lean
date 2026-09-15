import Algebraic.Core

/-!
# Translation integration through the Core import

A two-gate unary program exports both an original input and the final gate.
Replacing each unary operation by a zero-gate projection must erase both
gates while preserving both outputs. This exercises free-output substitution
without importing any Boolean basis or application module.
-/

namespace AlgebraicTests.CoreTranslation

open Algebraic

private abbrev unarySignature : Signature where
  Op := Unit
  Arity := fun _ => 1

private def source : Circuit unarySignature 1 2 2 where
  program := ((Program.empty : Program unarySignature 1 0).gate
    { op := (), wires := fun _ => Wire.input 0 }).gate
    { op := (), wires := fun _ => Wire.gate 0 }
  outputs := ![Wire.input 0, Wire.gate 1]

private def erase (signature : Signature) : Algebraic.Translation unarySignature signature where
  gateCount := fun _ => 0
  operation := fun _ => Circuit.id signature 1

example (signature : Signature) : ((erase signature).compile source).size = 0 := rfl

example (interpretation : Interpretation signature U) (input : Fin 1 → U) :
    ((erase signature).compile source).eval interpretation input =
      ![input 0, input 0] := by
  funext output
  refine Fin.cases rfl (fun last => ?_) output
  have equal : last = 0 := Fin.eq_zero last
  subst last
  rfl

example (operationCost : OperationCost signature) :
    ((erase signature).compile source).cost operationCost = 0 := rfl

example (translation : Algebraic.Translation σ τ)
    (left : Circuit σ n g m) (right : Circuit σ n h k)
    (interpretation : Interpretation τ U) (input : Fin n → U) :
    (translation.compile (left.parallel right)).eval interpretation input =
      Fin.append ((translation.compile left).eval interpretation input)
        ((translation.compile right).eval interpretation input) := by
  simp only [Algebraic.Translation.compile_eval, Circuit.eval_parallel]

example (translation : Algebraic.Translation σ τ)
    (left : Circuit σ n g m) (right : Circuit σ n h k)
    (operationCost : OperationCost τ) :
    (translation.compile (left.parallel right)).cost operationCost =
      (translation.compile left).cost operationCost +
        (translation.compile right).cost operationCost := by
  simp only [Algebraic.Translation.compile_cost, Circuit.cost_parallel]

end AlgebraicTests.CoreTranslation
