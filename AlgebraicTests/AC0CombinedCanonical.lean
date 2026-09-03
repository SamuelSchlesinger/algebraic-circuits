import Algebraic.LowerBound.AC0.Switching.CombinedCanonical

/-!
# AC0 combined canonical-injection regression tests
-/

namespace AlgebraicTests.AC0CombinedCanonical

open Algebraic
open Algebraic.AC0
open Algebraic.AC0.Switching

example [NeZero width] (pathLength : Nat) :
    CombinedAdvice width pathLength :=
  defaultCombinedAdvice pathLength

example
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat) :
    ∀ left, formula.CanonicalDepthAtLeast left pathLength →
      ∀ right, formula.CanonicalDepthAtLeast right pathLength →
        combinedCanonicalEncoding formula bounded pathLength left =
          combinedCanonicalEncoding formula bounded pathLength right →
          left = right :=
  combinedCanonicalEncoding_injectiveOn_deep formula bounded pathLength

example
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (RandomRestriction.fixedWeight p : ENNReal) ^ pathLength *
        RandomRestriction.probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) ^ pathLength) *
        (p : ENNReal) ^ pathLength :=
  RandomRestriction.probability_canonicalDepthAtLeast_combined_scaled_le
    formula bounded pathLength p atMostOne

example
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength :=
  RandomRestriction.probability_canonicalDepthAtLeast_le_five
    formula bounded pathLength p atMostOne

end AlgebraicTests.AC0CombinedCanonical
