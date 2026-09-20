import Algebraic.Complexity.RelativeCounting
import Algebraic.Complexity.RelativeTransport
import Algebraic.ConditionalComplexity

/-!
# Relative complexity regressions

Exercise source information loss, non-Boolean interpretations, non-binary
gates, non-unit costs, infinite domains and carriers, and the pointwise bridge.
-/

namespace AlgebraicTests.RelativeComplexity

open Algebraic

-- No choice of gates repairs information erased by a constant source family.
example (interpretation : Interpretation σ Bool) (operationCost : OperationCost σ) :
    Circuit.relativeCostComplexity interpretation operationCost
      (fun b (_ : Fin 1) => b) (fun (_ : Bool) (_ : Fin 1) => false) = ⊤ := by
  apply Circuit.relativeCostComplexity_eq_top_of_fiber_collision
    (x := false) (y := true) _ _ _ _ rfl
  intro equal
  have impossible : false = true := congrFun equal 0
  cases impossible

-- Your conditional convention retains the original input, so this same
-- target is free even if the extra supplied values are all constant.
example (interpretation : Interpretation σ Bool) :
    Circuit.conditionalGateComplexity interpretation
      (fun input : Fin 1 → Bool => input) (fun _ (_ : Fin 1) => false) = 0 := by
  rw [Circuit.conditionalGateComplexity_eq_zero_iff]
  exact ⟨Fin.castAdd 1, fun input => funext (Fin.append_left input _)⟩

private abbrev ternarySignature : Signature where
  Op := Unit
  Arity := fun _ => 3

private def ternaryInterpretation : Interpretation ternarySignature Nat :=
  fun _ args => args 0 + args 1 + args 2

private def sumCircuit : Circuit ternarySignature 3 1 1 where
  program := .gate .empty ⟨(), Wire.input⟩
  outputs := fun _ => Wire.gate 0

-- A seven-cost ternary gate acts on supplied functions of an arbitrary domain.
example :
    Circuit.relativeCostComplexity ternaryInterpretation (fun _ => 7)
      (fun x (_ : Fin 1) => x + (x + 1) + (x + 2))
      (fun x (i : Fin 3) => x + i.val) ≤ 7 := by
  have computes : sumCircuit.ComputesFrom ternaryInterpretation
      (fun x (_ : Fin 1) => x + (x + 1) + (x + 2))
      (fun x (i : Fin 3) => x + i.val) := by
    intro x
    funext i
    change (x + 0) + (x + 1) + (x + 2) = x + (x + 1) + (x + 2)
    rw [Nat.add_zero]
  exact Circuit.relativeCostComplexity_le (fun _ => 7) computes

-- Counting a finite set of programs needs neither a finite carrier nor a finite domain.
example [Fintype σ.Op] (interpretation : Interpretation σ Nat)
    (sources : Nat → Fin n → Nat) (m budget : Nat) :
    (Circuit.relativeFunctionsAtMost interpretation sources m budget).card ≤
      σ.orderedBudget n m budget :=
  Circuit.card_relativeFunctionsAtMost_le interpretation sources m budget

-- Whole rows of an infinite table and their coordinate functions give the same cost.
example (interpretation : Interpretation σ Nat) (operationCost : OperationCost σ)
    (target : Nat → Fin m → Nat) (sources : Nat → Fin n → Nat) :
    Circuit.relativeCostComplexity (interpretation.pointwise Nat) operationCost
      (fun (_ : Unit) i x => target x i) (fun (_ : Unit) i x => sources x i) =
        Circuit.relativeCostComplexity interpretation operationCost target sources :=
  Circuit.relativeCostComplexity_pointwise interpretation operationCost target sources

end AlgebraicTests.RelativeComplexity
