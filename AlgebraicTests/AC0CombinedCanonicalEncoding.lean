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
    (formula : DNF n)
    (state : PartialAssignment n)
    (currentTerm : Option (Term n))
    (advice : List (QueryAdvice width)) :
    replayIndices formula state currentTerm (clearLastClose advice) =
      replayIndices formula state currentTerm advice :=
  replayIndices_clearLastClose formula state currentTerm advice

end AlgebraicTests.AC0CombinedCanonicalEncoding
