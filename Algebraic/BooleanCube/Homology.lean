import Algebraic.BooleanCube.Cubical
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Homology of null-homotopic sublevel inclusions

A null-homotopic map induces the same map as a constant in every singular
homology degree. In positive degrees its induced map is zero, since a
constant factors through a point. These results use Mathlib's actual
singular homology functor with arbitrary admissible coefficients.
-/

namespace Algebraic.BooleanCube

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]
  {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- A null-homotopic map acts as a constant on singular homology in every degree. -/
theorem homologyMap_eq_const_of_nullhomotopic (map : C(X, Y)) (null : map.Nullhomotopic)
    (coefficients : C) (degree : Nat) :
    ∃ point : Y,
      ((singularHomologyFunctor C degree).obj coefficients).map (TopCat.ofHom map) =
        ((singularHomologyFunctor C degree).obj coefficients).map
          (TopCat.ofHom (ContinuousMap.const X point)) := by
  obtain ⟨point, ⟨homotopy⟩⟩ := null
  refine ⟨point, ?_⟩
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom map) (g := TopCat.ofHom (ContinuousMap.const X point))
    homotopy coefficients degree

/-- A null-homotopic map induces the zero map on positive-degree singular homology. -/
theorem homologyMap_eq_zero_of_nullhomotopic (map : C(X, Y)) (null : map.Nullhomotopic)
    (coefficients : C) (degree : Nat) (positive : degree ≠ 0) :
    ((singularHomologyFunctor C degree).obj coefficients).map (TopCat.ofHom map) = 0 := by
  obtain ⟨point, equal⟩ := homologyMap_eq_const_of_nullhomotopic map null coefficients degree
  let homology := (singularHomologyFunctor C degree).obj coefficients
  let toPoint : TopCat.of X ⟶ TopCat.of PUnit.{w + 1} :=
    TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let fromPoint : TopCat.of PUnit.{w + 1} ⟶ TopCat.of Y :=
    TopCat.ofHom (ContinuousMap.const _ point)
  have factor : TopCat.ofHom (ContinuousMap.const X point) = toPoint ≫ fromPoint := by
    ext x
    rfl
  have pointZero : IsZero (homology.obj (TopCat.of PUnit.{w + 1})) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C degree coefficients
      (TopCat.of PUnit.{w + 1}) positive
  rw [equal, factor, Functor.map_comp]
  change homology.map toPoint ≫ homology.map fromPoint = 0
  rw [pointZero.eq_zero_of_tgt (homology.map toPoint), zero_comp]

end Algebraic.BooleanCube
