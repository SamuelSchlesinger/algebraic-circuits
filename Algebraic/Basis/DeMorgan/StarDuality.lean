import Algebraic.Basis.DeMorgan.StarObstructions
import Algebraic.BooleanCube.AlexanderHomologyF2

/-!
# Homology of circuit links and their obstruction duals

The link lives on all `2^n` input assignments, including directions whose
singletons are absent at the current budget. Alexander duality uses this
fixed ground set and reverses reduced degrees by `2^n-i-3`.
-/

namespace Algebraic.DeMorgan

open BooleanCube.SimplicialF2

/-- The reduced homology of a constant link is the shifted reduced cohomology of its obstruction dual. -/
noncomputable def constantLinkAlexanderDuality (n budget : Nat) (value : Bool) (degree : ℤ) :
    ReducedHomology (constantLink n budget value) degree ≃ₗ[ZMod 2]
      ReducedCohomology (constantLinkDual n budget value) (((2 ^ n : Nat) : ℤ) - degree - 3) := by
  have equivalence := reducedAlexanderDuality (fun _ : Fin n => false) (constantLink n budget value)
    (fun included member => BooleanCube.link_downward included member) degree
  have cardinality : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  exact cardinality ▸ equivalence

/-- Every reduced Betti number of the constant link is recorded by cohomology of the obstruction dual. -/
theorem constantLink_betti_dual_eq (n budget : Nat) (value : Bool) (degree : ℤ) :
    reducedBetti (constantLink n budget value) degree =
      reducedCoBetti (constantLinkDual n budget value) (((2 ^ n : Nat) : ℤ) - degree - 3) :=
  (constantLinkAlexanderDuality n budget value degree).finrank_eq

end Algebraic.DeMorgan
