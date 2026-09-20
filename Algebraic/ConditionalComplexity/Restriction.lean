import Algebraic.ConditionalComplexity

/-!
# Lower bounds by parameterizing the original inputs

Constructing the tuple `(rho y, given (rho y))` and then applying a
conditional circuit computes the restricted target. The source tuple is
charged jointly, so any sharing in its implementation is retained.
-/

open Algebraic

namespace Cslib.Circuits.Circuit

/-- Build all restricted source values jointly, then run the conditional circuit. -/
theorem costComplexity_precomp_le_conditional_add
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) (map : Target U d n) :
    costComplexity interpretation operationCost (target ∘ map) ≤
      conditionalCostComplexity interpretation operationCost target given +
        costComplexity interpretation operationCost
          (fun input => Fin.append (map input) (given (map input))) :=
  relativeCostComplexity_precomp_triangle interpretation operationCost target
    (fun input => Fin.append input (given input)) map (fun input => input)

/-- A hard restricted target and a cheap joint source tuple give a lower
bound on conditional complexity. Natural subtraction truncates at zero. -/
theorem conditionalCostComplexity_lowerBound_of_precomp
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) (map : Target U d n)
    (lower budget : Nat)
    (hard : (lower : ℕ∞) ≤ costComplexity interpretation operationCost (target ∘ map))
    (cheap : costComplexity interpretation operationCost
      (fun input => Fin.append (map input) (given (map input))) ≤ budget) :
    ((lower - budget : Nat) : ℕ∞) ≤
      conditionalCostComplexity interpretation operationCost target given := by
  have bound := hard.trans
    ((costComplexity_precomp_le_conditional_add interpretation operationCost target given map).trans
      (add_le_add le_rfl cheap))
  by_cases infinite : conditionalCostComplexity interpretation operationCost target given = ⊤
  · simp [infinite]
  · lift conditionalCostComplexity interpretation operationCost target given to Nat using infinite with value
    norm_cast at bound ⊢
    omega

end Cslib.Circuits.Circuit

namespace Algebraic.Circuit

export Cslib.Circuits.Circuit
  (costComplexity_precomp_le_conditional_add conditionalCostComplexity_lowerBound_of_precomp)

end Algebraic.Circuit
