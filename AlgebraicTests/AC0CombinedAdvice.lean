import Algebraic.LowerBound.AC0.Switching.CombinedAdvice

/-!
# AC0 combined switching-advice regression tests
-/

namespace AlgebraicTests.AC0CombinedAdvice

open Algebraic.AC0.Switching

example : Fintype.card (BlockAdvice 4 2) = 24 := by
  norm_num [card_blockAdvice, Nat.choose]

example : Fintype.card (ContinuingBlockAdvice 4 2) = 18 := by
  norm_num [card_continuingBlockAdvice, Nat.choose]

example (width pathLength : Nat) (positive : 0 < width) :
    (Fintype.card (CombinedAdvice width pathLength) : Real) ≤
      (((5 : Real) * width - 1) / 2) ^ pathLength :=
  card_combinedAdvice_cast_le width pathLength positive

end AlgebraicTests.AC0CombinedAdvice
