import Algebraic.BooleanCube.Betti

/-!
# Rank bounds for newly available fillings

Rank-nullity bounds the increase in boundary dimension by the increase in
chain dimension. Applied to erasure, this turns old homology into a lower
bound on the number of newly admitted cube faces and Boolean functions.
-/

namespace Algebraic.BooleanCube.CubicalHomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Rank-nullity inside an ambient subspace, retaining its ambient kernel intersection. -/
theorem finrank_map_add_finrank_inf_ker (map : V →ₗ[K] V) (space : Submodule K V) :
    Module.finrank K (space.map map) + Module.finrank K (space ⊓ LinearMap.ker map : Submodule K V) =
      Module.finrank K space := by
  let equiv : LinearMap.ker (map.comp space.subtype) ≃ₗ[K]
      (space ⊓ LinearMap.ker map : Submodule K V) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have dimension := (map.comp space.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype, equiv.finrank_eq] at dimension
  exact dimension

/-- The increase in image dimension is bounded by the increase in source dimension. -/
theorem finrank_map_growth_le (map : V →ₗ[K] V) (old new : Submodule K V) (included : old ≤ new) :
    Module.finrank K (new.map map) + Module.finrank K old ≤
      Module.finrank K new + Module.finrank K (old.map map) := by
  have oldRank := finrank_map_add_finrank_inf_ker map old
  have newRank := finrank_map_add_finrank_inf_ker map new
  have kernels := Submodule.finrank_mono (inf_le_inf_right (LinearMap.ker map) included)
  omega

variable (K)

/-- Positive-degree homology requires at least as many new filling faces. -/
theorem betti_le_card_new_faces (left right : Set (Fin n → Bool)) (degree : Nat)
    (positive : 0 < degree) (included : left ⊆ right)
    (erases : ∀ threshold vertex, vertex ∈ left → erase Fin.val threshold vertex ∈ right) :
    betti K left degree ≤ (Face.faces right (degree + 1) \ Face.faces left (degree + 1)).card := by
  classical
  have filled := Submodule.finrank_mono (Chains.cycles_le_boundaries K left right degree positive erases)
  have growth := finrank_map_growth_le (Chains.boundary K n)
    (Chains.level K left (degree + 1)) (Chains.level K right (degree + 1))
    (Chains.level_mono K included (degree + 1))
  have quotient := betti_add_finrank_boundaries K left degree
  change Module.finrank K (Chains.boundaries K right degree) +
      Module.finrank K (Chains.level K left (degree + 1)) ≤
    Module.finrank K (Chains.level K right (degree + 1)) +
      Module.finrank K (Chains.boundaries K left degree) at growth
  rw [finrank_level, finrank_level] at growth
  have faces := Finset.card_sdiff_add_card_eq_card (Face.faces_mono included (degree + 1))
  omega

/-- A cubical Betti number lower-bounds the number of newly admitted Boolean vertices. -/
theorem betti_le_choose_mul_card_new_vertices (left right : Set (Fin n → Bool)) (degree : Nat)
    (positive : 0 < degree) (included : left ⊆ right)
    (erases : ∀ threshold vertex, vertex ∈ left → erase Fin.val threshold vertex ∈ right) :
    betti K left degree ≤ n.choose (degree + 1) * (Face.newVertices left right).card :=
  (betti_le_card_new_faces K left right degree positive included erases).trans
    (Face.card_new_faces_le left right (degree + 1))

end Algebraic.BooleanCube.CubicalHomology
