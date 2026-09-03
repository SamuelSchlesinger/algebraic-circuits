import Algebraic.LowerBound.AC0.Switching.CombinedCanonicalPacking

/-!
# AC0 combined canonical-packing regression tests
-/

namespace AlgebraicTests.AC0CombinedCanonicalPacking

open Algebraic
open Algebraic.AC0
open Algebraic.AC0.Switching

example
    (block : List (RelativeQuery width))
    (positionsSorted : (block.map Prod.fst).Pairwise (· < ·))
    (closesBlock : Bool) :
    (BlockAdvice.ofRelativeBlock block positionsSorted).toQueryList
        closesBlock =
      relativeBlockToQueryList block closesBlock :=
  BlockAdvice.toQueryList_ofRelativeBlock block positionsSorted closesBlock

example
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    (trace.combinedAdvice bounded).toQueryList =
      clearLastClose (trace.adviceList (widthBound := widthBound)) :=
  trace.toQueryList_combinedAdvice bounded

example
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : formula.CanonicalPath rho pathLength)
    (trace : formula.CanonicalTrace rho path.steps)
    (bounded : formula.WidthAtMost widthBound) :
    decodeCombined formula
        (rho.refine
          (trace.satisfyingAssignment (widthBound := widthBound)),
          trace.combinedAdviceOfLength bounded path.length_steps) =
      rho :=
  path.decodeCombined_satisfyingEncoding trace bounded

end AlgebraicTests.AC0CombinedCanonicalPacking
