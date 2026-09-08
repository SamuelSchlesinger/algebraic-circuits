import Algebraic.BooleanCube.Translation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Distance to an easy set and neighborhood volume

Distance to a nonempty finite family is the minimum unnormalized Hamming
distance. Nearest points exist, this distance is one-Lipschitz, and its
sublevels are precisely unions of Hamming balls.
-/

namespace Algebraic.BooleanCube

variable {ι : Type*} [Fintype ι]

/-- The minimum number of coordinate changes needed to enter a nonempty vertex family. -/
def distanceTo (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty) (point : ι → Bool) : Nat :=
  vertices.inf' nonempty (hammingDist point)

/-- A nearest vertex always exists in the specified family. -/
theorem exists_nearest (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty) (point : ι → Bool) :
    ∃ nearest ∈ vertices, distanceTo vertices nonempty point = hammingDist point nearest :=
  Finset.exists_mem_eq_inf' nonempty _

/-- Distance to the family is at most distance to any one of its vertices. -/
theorem distanceTo_le (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty)
    (point : ι → Bool) {vertex : ι → Bool} (member : vertex ∈ vertices) :
    distanceTo vertices nonempty point ≤ hammingDist point vertex := Finset.inf'_le _ member

/-- Zero distance is exactly membership in the original vertex family. -/
@[simp] theorem distanceTo_eq_zero (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty)
    (point : ι → Bool) : distanceTo vertices nonempty point = 0 ↔ point ∈ vertices := by
  constructor
  · intro zero
    obtain ⟨nearest, member, equal⟩ := exists_nearest vertices nonempty point
    have same := hammingDist_eq_zero.mp (equal.symm.trans zero)
    simpa [same] using member
  · intro member
    have bound := distanceTo_le vertices nonempty point member
    simpa using bound

/-- A distance sublevel has an actual nearby witness in the family. -/
theorem distanceTo_le_iff (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty)
    (point : ι → Bool) (radius : Nat) :
    distanceTo vertices nonempty point ≤ radius ↔ ∃ vertex ∈ vertices, hammingDist point vertex ≤ radius := by
  exact Finset.inf'_le_iff nonempty

/-- Enlarging the target family can only decrease the distance to it. -/
theorem distanceTo_antitone {left right : Finset (ι → Bool)}
    (hl : left.Nonempty) (hr : right.Nonempty) (included : left ⊆ right) (point : ι → Bool) :
    distanceTo right hr point ≤ distanceTo left hl point := by
  obtain ⟨nearest, member, equal⟩ := exists_nearest left hl point
  rw [equal]
  exact distanceTo_le right hr point (included member)

/-- Moving the query point changes its distance by at most the length of the move. -/
theorem distanceTo_le_add (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty)
    (left right : ι → Bool) :
    distanceTo vertices nonempty left ≤ hammingDist left right + distanceTo vertices nonempty right := by
  obtain ⟨nearest, member, equal⟩ := exists_nearest vertices nonempty right
  rw [equal]
  exact (distanceTo_le vertices nonempty left member).trans (hammingDist_triangle left right nearest)

/-- Distance to any nonempty family is one-Lipschitz in Hamming distance. -/
theorem distanceTo_dist_le (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty)
    (left right : ι → Bool) :
    Nat.dist (distanceTo vertices nonempty left) (distanceTo vertices nonempty right) ≤ hammingDist left right := by
  have forward := distanceTo_le_add vertices nonempty left right
  have backward := distanceTo_le_add vertices nonempty right left
  rw [hammingDist_comm right left] at backward
  unfold Nat.dist
  omega

variable [DecidableEq ι]

/-- The closed Hamming ball of an integer radius. -/
def ball (center : ι → Bool) (radius : Nat) : Finset (ι → Bool) :=
  Finset.univ.filter (fun point => hammingDist center point ≤ radius)

/-- The Hamming sphere of an integer radius. -/
def sphere (center : ι → Bool) (radius : Nat) : Finset (ι → Bool) :=
  Finset.univ.filter (fun point => hammingDist center point = radius)

/-- Hamming neighborhoods are unions of balls around the allowed vertices. -/
def neighborhood (vertices : Finset (ι → Bool)) (radius : Nat) : Finset (ι → Bool) :=
  vertices.biUnion (fun center => ball center radius)

/-- Neighborhood membership agrees exactly with the distance sublevel. -/
theorem mem_neighborhood_iff (vertices : Finset (ι → Bool)) (nonempty : vertices.Nonempty)
    (point : ι → Bool) (radius : Nat) :
    point ∈ neighborhood vertices radius ↔ distanceTo vertices nonempty point ≤ radius := by
  simp [neighborhood, ball, distanceTo_le_iff, hammingDist_comm]

/-- Flipping a support changes exactly its cardinality many coordinates. -/
@[simp] theorem hammingDist_corner (base : ι → Bool) (directions : Finset ι) :
    hammingDist base (corner base directions) = directions.card := by
  have support : Finset.univ.filter (fun i => base i ≠ corner base directions i) = directions := by
    ext i
    by_cases present : i ∈ directions <;> simp [corner, present]
  exact congrArg Finset.card support

/-- The direction set to a vertex has cardinality equal to its Hamming distance. -/
theorem card_directionsTo (base vertex : ι → Bool) : (directionsTo base vertex).card = hammingDist base vertex := by
  simpa using (hammingDist_corner base (directionsTo base vertex)).symm

/-- A sphere is the image of the fixed-cardinality support family under the corner equivalence. -/
theorem sphere_eq_image (center : ι → Bool) (radius : Nat) :
    sphere center radius = (Finset.univ.powersetCard radius).image (corner center) := by
  ext point
  constructor
  · intro member
    refine Finset.mem_image.mpr ⟨directionsTo center point, ?_, corner_directionsTo center point⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (card_directionsTo center point).trans (Finset.mem_filter.mp member).2⟩
  · intro member
    obtain ⟨support, property, rfl⟩ := Finset.mem_image.mp member
    simp [sphere, (Finset.mem_powersetCard.mp property).2]

/-- The exact number of vertices at Hamming distance `r`. -/
theorem card_sphere (center : ι → Bool) (radius : Nat) :
    (sphere center radius).card = (Fintype.card ι).choose radius := by
  rw [sphere_eq_image, Finset.card_image_of_injective _ (corner_injective center),
    Finset.card_powersetCard, Finset.card_univ]

/-- A closed Hamming ball is the disjoint union of its spheres. -/
theorem ball_eq_biUnion_spheres (center : ι → Bool) (radius : Nat) :
    ball center radius = (Finset.range (radius + 1)).biUnion (sphere center) := by
  ext point
  simp only [ball, sphere, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Finset.mem_range]
  constructor
  · intro bounded
    exact ⟨hammingDist center point, by omega, rfl⟩
  · rintro ⟨distance, bounded, equal⟩
    omega

/-- The exact Hamming-ball volume is the sum of binomial coefficients. -/
theorem card_ball (center : ι → Bool) (radius : Nat) :
    (ball center radius).card = ∑ k ∈ Finset.range (radius + 1), (Fintype.card ι).choose k := by
  rw [ball_eq_biUnion_spheres, Finset.card_biUnion]
  · simp only [card_sphere]
  · intro left _ right _ different
    apply Finset.disjoint_left.mpr
    intro point hl hr
    exact different ((Finset.mem_filter.mp hl).2.symm.trans (Finset.mem_filter.mp hr).2)

/-- Counting balls gives a volume bound without assuming anything about their overlaps. -/
theorem card_neighborhood_le (vertices : Finset (ι → Bool)) (radius : Nat) :
    (neighborhood vertices radius).card ≤
      vertices.card * ∑ k ∈ Finset.range (radius + 1), (Fintype.card ι).choose k := by
  calc
    _ ≤ ∑ center ∈ vertices, (ball center radius).card := Finset.card_biUnion_le
    _ = _ := by simp [card_ball]

/-- Neighborhoods never exceed the whole ambient Boolean cube. -/
theorem card_neighborhood_le_cube (vertices : Finset (ι → Bool)) (radius : Nat) :
    (neighborhood vertices radius).card ≤ 2 ^ Fintype.card ι := by
  simpa using Finset.card_le_card (Finset.subset_univ (neighborhood vertices radius))

end Algebraic.BooleanCube
