import Algebraic.Basis.DeMorgan.Topology
import Algebraic.BooleanCube.Homology

/-!
# Vanishing homology maps for circuit-complexity sublevels

Every positive-degree singular homology class present at size budget `s`
maps to zero at budget `s + n`. This is an induced-map theorem; it does not
assert that the larger sublevel has no newly born homology classes.
-/

namespace Algebraic.DeMorgan

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  [CategoryWithHomology C]

/-- Increasing the circuit budget by the input width kills every positive-degree homology class. -/
theorem sublevel_homologyMap_eq_zero (positive : 0 < n) (budget : Nat)
    (coefficients : C) (degree : Nat) (nonzero : degree ≠ 0) :
    ((singularHomologyFunctor C degree).obj coefficients).map
      (TopCat.ofHom (BooleanCube.inclusion (@complexity n) budget n)) = 0 :=
  BooleanCube.homologyMap_eq_zero_of_nullhomotopic _
    (sublevel_inclusion_nullhomotopic positive budget) coefficients degree nonzero

end Algebraic.DeMorgan
