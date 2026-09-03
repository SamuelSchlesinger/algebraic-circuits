import Algebraic.LowerBound.AC0.Switching.CombinedCanonicalTrace

/-!
# AC0 combined canonical-trace regression tests
-/

namespace AlgebraicTests.AC0CombinedCanonicalTrace

open Algebraic
open Algebraic.AC0
open Algebraic.AC0.Switching

example
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    (trace.combinedBlocks (widthBound := widthBound)).flatten =
      (trace.adviceList (widthBound := widthBound)).map
        QueryAdvice.toRelativeQuery :=
  trace.flatten_combinedBlocks

example
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    ((trace.combinedBlocks (widthBound := widthBound)).map
      List.length).sum = steps.length :=
  trace.sum_length_combinedBlocks

example
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    ∀ block ∈ trace.combinedBlocks (widthBound := widthBound),
      block ≠ [] ∧
      (block.map Prod.fst).Pairwise (· < ·) ∧
      block.length ≤ widthBound := by
  intro block present
  exact ⟨trace.combinedBlocks_nonempty block present,
    trace.combinedBlocks_positions_pairwise bounded block present,
    trace.combinedBlock_length_le_width bounded present⟩

example
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    RelativeBlocksHaveContinuingMismatch
      (trace.combinedBlocks (widthBound := widthBound)) :=
  trace.combinedBlocks_haveContinuingMismatch

end AlgebraicTests.AC0CombinedCanonicalTrace
