import Algebraic.LowerBound.AC0.Switching.CombinedCanonicalEncoding

/-!
# AC0 combined canonical-encoding regression tests
-/

namespace AlgebraicTests.AC0CombinedCanonicalEncoding

open Algebraic
open Algebraic.AC0
open Algebraic.AC0.Switching

example (advice : CombinedAdvice width pathLength) :
    advice.toQueryList.length = pathLength :=
  advice.length_toQueryList

example
    (block : BlockAdvice width (remaining + 1))
    (lengthLeWidth : remaining + 1 ≤ width) :
    (CombinedAdvice.ofFinalBlock block lengthLeWidth).toQueryList =
      block.toQueryList false := by
  simp

example
    (block : ContinuingBlockAdvice width (blockRemaining + 1))
    (tail : CombinedAdvice width tailLength)
    (blockLeWidth : blockRemaining + 1 ≤ width)
    (tailPositive : 0 < tailLength) :
    (CombinedAdvice.prependBlock block tail blockLeWidth
      tailPositive).toQueryList =
      block.val.toQueryList true ++ tail.toQueryList := by
  simp

example
    (formula : DNF n)
    (state : PartialAssignment n)
    (currentTerm : Option (Term n))
    (advice : List (QueryAdvice width)) :
    replayIndices formula state currentTerm (clearLastClose advice) =
      replayIndices formula state currentTerm advice :=
  replayIndices_clearLastClose formula state currentTerm advice

end AlgebraicTests.AC0CombinedCanonicalEncoding
