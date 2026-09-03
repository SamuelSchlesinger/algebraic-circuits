import Algebraic.LowerBound.AC0.Switching.CanonicalEncoding

/-!
# AC0 canonical switching-advice regression tests
-/

namespace AlgebraicTests.AC0CanonicalEncoding

open Algebraic
open Algebraic.AC0
open Algebraic.AC0.Switching

example (widthBound pathLength : Nat) :
    Fintype.card (Advice widthBound pathLength) =
      (4 * widthBound) ^ pathLength :=
  card_advice widthBound pathLength

example
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    ∀ record ∈ trace.queryRecords (widthBound := widthBound),
      QueryRecord.WellFormed record :=
  trace.queryRecords_wellFormed bounded

example
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : DNF.CanonicalPath formula rho pathLength)
    (trace : DNF.CanonicalTrace formula rho path.steps) :
    (trace.satisfyingAssignment (widthBound := widthBound)).fixedCount =
        pathLength ∧
      (trace.satisfyingAssignment
          (widthBound := widthBound)).fixedVariables ⊆ rho.liveVariables ∧
      (trace.adviceList (widthBound := widthBound)).length = pathLength := by
  exact ⟨path.satisfyingAssignment_fixedCount trace,
    path.satisfyingAssignment_fixesOnlyLive trace,
    trace.length_adviceList.trans path.length_steps⟩

end AlgebraicTests.AC0CanonicalEncoding
