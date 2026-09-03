import Algebraic.LowerBound.AC0.Switching.Canonical

/-!
# AC0 canonical switching-injection regression tests
-/

namespace AlgebraicTests.AC0CanonicalSwitching

open Algebraic
open Algebraic.AC0
open Algebraic.AC0.Switching
open Algebraic.AC0.RandomRestriction
open scoped ENNReal

example
    {widthBound : Nat}
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat) :
    ∀ left, formula.CanonicalDepthAtLeast left pathLength →
      ∀ right, formula.CanonicalDepthAtLeast right pathLength →
        canonicalEncoding (widthBound := widthBound)
            formula pathLength left =
          canonicalEncoding (widthBound := widthBound)
            formula pathLength right →
          left = right :=
  canonicalEncoding_injectiveOn_deep formula bounded pathLength

example
    {widthBound : Nat}
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ pathLength *
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((4 * widthBound : Nat) : ENNReal) ^ pathLength *
        (p : ENNReal) ^ pathLength :=
  probability_canonicalDepthAtLeast_scaled_le
    formula bounded pathLength p atMostOne

example
    {widthBound : Nat}
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (small : p ≤ 1 / 9) :
    probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((9 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength :=
  probability_canonicalDepthAtLeast_le_nine
    formula bounded pathLength p atMostOne small

example
    (formula : DNF n)
    (bounded : formula.WidthAtMost 0)
    (pathLength : Nat)
    (positive : 0 < pathLength)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) = 0 :=
  probability_canonicalDepthAtLeast_eq_zero_of_widthAtMost_zero
    formula bounded pathLength positive p atMostOne

end AlgebraicTests.AC0CanonicalSwitching
