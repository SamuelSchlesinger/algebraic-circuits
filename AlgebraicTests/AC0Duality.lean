import Algebraic.LowerBound.AC0.Duality

/-!
# AC0 normal-form duality regression tests
-/

namespace AlgebraicTests.AC0Duality

open Algebraic
open Algebraic.AC0

example (set : LiteralSet n) :
    set.negate.negate = set := by simp

example (set : LiteralSet n) :
    set.negate.width = set.width := by simp

example (formula : DNF n) :
    formula.negate.negate = formula := by simp

example (formula : CNF n) :
    formula.negate.negate = formula := by simp

example
    (formula : DNF n)
    (input : Fin n -> Bool) :
    formula.negate.eval input = !formula.eval input := by simp

example
    (formula : CNF n)
    (input : Fin n -> Bool) :
    formula.negate.eval input = !formula.eval input := by simp

example
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.restrict rho).negate = formula.negate.restrict rho :=
  formula.negate_restrict rho

example
    (formula : CNF n)
    (rho : PartialAssignment n) :
    (formula.restrict rho).negate = formula.negate.restrict rho :=
  formula.negate_restrict rho

example
    (function : ScalarFunction Bool n)
    (bound : Nat) :
    DecisionTree.DepthAtLeast (fun input => !(function input)) bound ↔
      DecisionTree.DepthAtLeast function bound := by simp

end AlgebraicTests.AC0Duality
