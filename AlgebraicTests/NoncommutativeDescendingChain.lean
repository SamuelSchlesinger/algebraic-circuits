import Algebraic.LowerBound.Noncommutative.DescendingChain

/-!
# Public regressions for descending-chain rank envelopes
-/

namespace AlgebraicTests

open Algebraic.LowerBound.Noncommutative.DescendingChain

example : envelope 3 2 = 72 := by
  native_decide

example
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank)
    {targetRank : Nat}
    (target_le : targetRank ≤ totalRank gateRank 7 3) :
    targetRank ≤ 7 * 2 ^ 3 * Nat.choose 9 3 := by
  simpa using recurrence.targetRank_le_degree_choose
    (targetRank := targetRank) (gates := 7) (degree := 5)
    (by omega) (by omega) target_le

example
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank)
    {targetRank gates : Nat}
    (target_le : targetRank ≤ totalRank gateRank gates 0) :
    targetRank ≤ gates :=
  recurrence.targetRank_le_gates_of_degree_two target_le

end AlgebraicTests
