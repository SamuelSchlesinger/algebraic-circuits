import Algebraic.Basis.AC0.Normalization

/-!
# AC0 dual-rail normalization regressions

These examples exercise the public operation-level simulation and exact cost
law on concrete gates. The generic theorems themselves cover every fan-in.
-/

namespace AlgebraicTests.AC0Normalization

open Algebraic

example (input : Fin 3 -> Bool) :
    AC0.DualRail.encode (AC0.interpretation (.and 3) input) =
      (AC0.DualRail.translation.operation (.and 3)).eval
        AC0.interpretation
        (Block.flatten (AC0.DualRail.encode ∘ input)) :=
  AC0.DualRail.operation_encode (.and 3) input

example :
    AC0.DualRail.translation.pullCost AC0.andOrCost (.and 7) = 2 := by
  rw [AC0.DualRail.pullCost_andOrCost]
  rfl

example :
    AC0.DualRail.translation.pullCost AC0.andOrCost .not = 0 := by
  rw [AC0.DualRail.pullCost_andOrCost]
  rfl

example (input : Fin 5 -> Nat) :
    AC0.DualRail.duplicateDepth
        (AC0.logicalDepthInterpretation (.or 5) input) =
      (AC0.DualRail.translation.operation (.or 5)).eval
        AC0.logicalDepthInterpretation
        (Block.flatten (AC0.DualRail.duplicateDepth ∘ input)) :=
  AC0.DualRail.operation_duplicateDepth (.or 5) input

end AlgebraicTests.AC0Normalization
