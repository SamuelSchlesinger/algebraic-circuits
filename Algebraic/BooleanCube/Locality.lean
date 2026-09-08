import Algebraic.BooleanCube.Witness

/-!
# Sparse faces and cochain locality

Zeroing fixed coordinates outside a chosen set preserves a face's dimension.
Every vertex of the resulting face has at most the chosen-set size plus the
face dimension many true coordinates. This operation tests how much of the
truth table a nonbounding certificate must retain.
-/

namespace Algebraic.BooleanCube
namespace Face

/-- Keep free coordinates and chosen fixed coordinates; set all other coordinates to false. -/
def truncate (coordinates : Finset (Fin n)) (face : Face n) : Face n :=
  fun i => if face i = none ∨ i ∈ coordinates then face i else some false

/-- Truncation preserves precisely the free coordinates. -/
@[simp] theorem free_truncate (coordinates : Finset (Fin n)) (face : Face n) :
    (face.truncate coordinates).free = face.free := by
  ext i
  constructor
  · intro member
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have constraint := (Finset.mem_filter.mp member).2
    change (if face i = none ∨ i ∈ coordinates then face i else some false) = none at constraint
    split_ifs at constraint
    exact constraint
  · intro member
    have free := (Finset.mem_filter.mp member).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (if face i = none ∨ i ∈ coordinates then face i else some false) = none
    simp [free]

/-- Truncation preserves face dimension. -/
@[simp] theorem dimension_truncate (coordinates : Finset (Fin n)) (face : Face n) :
    (face.truncate coordinates).dimension = face.dimension := by
  simp [dimension]

/-- A true coordinate of a truncated-face vertex is chosen or free. -/
theorem true_support_subset_of_contains_truncate (coordinates : Finset (Fin n)) (face : Face n)
    {vertex : Fin n → Bool} (contained : (face.truncate coordinates).Contains vertex) :
    Finset.univ.filter (fun i => vertex i = true) ⊆ coordinates ∪ face.free := by
  intro i member
  have value := (Finset.mem_filter.mp member).2
  by_contra outside
  have fixed : face i ≠ none := by
    intro free
    exact outside (Finset.mem_union_right _ (by simp [Face.free, free]))
  have missing : i ∉ coordinates := fun h => outside (Finset.mem_union_left _ h)
  have constraint := contained i
  simp [truncate, fixed, missing, value] at constraint

/-- A truncated face has uniformly sparse vertices. -/
theorem card_true_support_le_of_contains_truncate (coordinates : Finset (Fin n)) (face : Face n)
    {vertex : Fin n → Bool} (contained : (face.truncate coordinates).Contains vertex) :
    (Finset.univ.filter (fun i => vertex i = true)).card ≤ coordinates.card + face.dimension :=
  (Finset.card_le_card (true_support_subset_of_contains_truncate coordinates face contained)).trans
    (Finset.card_union_le _ _)

end Face

namespace Chains

variable (R : Type*) [CommRing R]

/-- If cheap face replacements preserve every boundary evaluation, the cochain kills all cycles. -/
theorem cochain_eq_zero_of_face_replacement (vertices : Set (Fin n → Bool)) (degree : Nat)
    (positive : 0 < degree) (cochain : Chains R n →ₗ[R] R)
    (vanishes : ∀ face : Face n, face.Allowed vertices → face.dimension = degree + 1 →
      cochain (boundary R n (Finsupp.single face 1)) = 0)
    (replace : ∀ face : Face n, face.dimension = degree + 1 →
      ∃ replacement : Face n, replacement.Allowed vertices ∧ replacement.dimension = degree + 1 ∧
        cochain (boundary R n (Finsupp.single replacement 1)) =
          cochain (boundary R n (Finsupp.single face 1)))
    {chain : Chains R n} (closed : chain ∈ cycles R Set.univ degree) :
    cochain chain = 0 := by
  have allFaces : ∀ face : Face n, face.Allowed Set.univ → face.dimension = degree + 1 →
      cochain (boundary R n (Finsupp.single face 1)) = 0 := by
    intro face _ dim
    obtain ⟨replacement, allowed, replacementDim, equal⟩ := replace face dim
    rw [← equal]
    exact vanishes replacement allowed replacementDim
  by_contra nonzero
  have notBoundary := not_mem_boundaries_of_cochain R Set.univ degree cochain allFaces nonzero
  exact notBoundary (cycles_le_boundaries R Set.univ Set.univ degree positive
    (fun _ _ _ => Set.mem_univ _) closed)

end Chains
end Algebraic.BooleanCube
