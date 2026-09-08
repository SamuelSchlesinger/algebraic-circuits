import Algebraic.Basis.DeMorgan.Geometry
import Algebraic.BooleanCube.Cubical

/-!
# Continuous contraction of circuit-complexity sublevels

Fill every truth-table cube face all of whose vertices have circuit
complexity at most `s`. For positive input width `n`, the inclusion from
budget `s` to budget `s + n` is null-homotopic. The proof supplies a coherent
continuous contraction, using the concrete threshold circuits.
-/

namespace Algebraic.DeMorgan

/-- Every circuit-complexity sublevel contracts inside the sublevel `n` gates higher. -/
theorem sublevel_inclusion_nullhomotopic (positive : 0 < n) (budget : Nat) :
    (BooleanCube.inclusion (@complexity n) budget n).Nullhomotopic := by
  apply BooleanCube.inclusion_nullhomotopic inputRank inputRank_injective
    (2 ^ n) inputRank_lt complexity budget n
  · intro threshold function
    exact complexity_erase_le positive function threshold
  · have := complexity_constant_le n false
    omega

end Algebraic.DeMorgan
