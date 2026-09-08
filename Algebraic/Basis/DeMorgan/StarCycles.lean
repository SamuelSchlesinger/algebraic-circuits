import Algebraic.Basis.DeMorgan.Star
import Algebraic.BooleanCube.EdgeFaces

/-!
# Counts and graph cycles in the constant links

At budget `n > 0`, the constant link has `2^n` vertices and
`n*2^(n-1)` edges. Its graph incidence kernel has dimension
`n*2^(n-1)+1-2^n` over any field. This counts cycles in the link graph;
the closed star itself is contractible. No comparison with singular
homology is assumed here.
-/

namespace Algebraic.DeMorgan

/-- Admitted direction sets of a specified cardinality in a constant link. -/
abbrev ConstantLinkFace (n budget : Nat) (value : Bool) (r : Nat) :=
  {directions : Finset (Fin n → Bool) // directions ∈ constantLink n budget value ∧ directions.card = r}

/-- The number of link faces with `r` directions, equivalently incident cubes of dimension `r`. -/
noncomputable def constantLinkFaceCount (n budget : Nat) (value : Bool) (r : Nat) : Nat :=
  Nat.card (ConstantLinkFace n budget value r)

/-- Link vertices at budget `n` are precisely the Boolean input assignments. -/
noncomputable def constantLinkVertexEquiv (positive : 0 < n) (value : Bool) :
    (Fin n → Bool) ≃ ConstantLinkFace n n value 1 :=
  Equiv.ofBijective (fun point => ⟨{point}, singleton_mem_constantLink positive value point, by simp⟩)
    ⟨by
      intro left right equal
      have singletonEqual := congrArg Subtype.val equal
      simpa using singletonEqual,
    by
      intro face
      obtain ⟨point, equal⟩ := Finset.card_eq_one.mp face.property.2
      exact ⟨point, Subtype.ext equal.symm⟩⟩

/-- The constant link has one direction for every input assignment. -/
theorem constantLinkFaceCount_one (positive : 0 < n) (value : Bool) :
    constantLinkFaceCount n n value 1 = 2 ^ n := by
  simpa [constantLinkFaceCount] using (Nat.card_congr (constantLinkVertexEquiv positive value)).symm

private def cubeEdgeToLink (positive : 0 < n) (value : Bool) (edge : BooleanCube.GraphCycles.Edge n) :
    ConstantLinkFace n n value 2 :=
  ⟨BooleanCube.edgeDirections edge,
    (pair_mem_constantLink_iff positive value _ _ (BooleanCube.edgeEnd_ne edge)).mpr
      (BooleanCube.hammingDist_edgeEnd edge.property), BooleanCube.card_edgeDirections edge⟩

/-- Canonical input edges enumerate exactly the two-direction faces of either constant link. -/
noncomputable def constantLinkEdgeEquiv (positive : 0 < n) (value : Bool) :
    BooleanCube.GraphCycles.Edge n ≃ ConstantLinkFace n n value 2 :=
  Equiv.ofBijective (cubeEdgeToLink positive value) ⟨by
    intro left right equal
    exact BooleanCube.edgeDirections_injective n (congrArg Subtype.val equal), by
    intro face
    obtain ⟨left, right, different, equal⟩ := Finset.card_eq_two.mp face.property.2
    have adjacent := (pair_mem_constantLink_iff positive value left right different).mp
      (equal ▸ face.property.1)
    obtain ⟨edge, directions⟩ := BooleanCube.exists_edgeDirections_eq adjacent
    exact ⟨edge, Subtype.ext (directions.trans equal.symm)⟩⟩

/-- The edge correspondence preserves the actual unordered endpoint pair. -/
@[simp] theorem constantLinkEdgeEquiv_val (positive : 0 < n) (value : Bool)
    (edge : BooleanCube.GraphCycles.Edge n) :
    (constantLinkEdgeEquiv positive value edge).val = BooleanCube.edgeDirections edge := rfl

/-- The constant link has exactly as many edges as the input cube. -/
theorem constantLinkFaceCount_two (positive : 0 < n) (value : Bool) :
    constantLinkFaceCount n n value 2 = n * 2 ^ (n - 1) := by
  rw [constantLinkFaceCount, ← Nat.card_congr (constantLinkEdgeEquiv positive value)]
  simpa [BooleanCube.GraphCycles.Edge] using (BooleanCube.card_edges (ι := Fin n))

/-- No higher-dimensional link faces exist at the input-width budget. -/
theorem constantLinkFaceCount_eq_zero (positive : 0 < n) (value : Bool) (large : 2 < r) :
    constantLinkFaceCount n n value r = 0 := by
  have : IsEmpty (ConstantLinkFace n n value r) := ⟨fun face => by
    have bound := card_le_two_of_mem_constantLink positive value face.property.1
    rw [face.property.2] at bound
    omega⟩
  simp [constantLinkFaceCount]

variable (K : Type*) [Field K]

/-- The graph boundary on actual link edges, oriented using their unique input-cube orientation. -/
noncomputable def constantLinkBoundary (positive : 0 < n) (value : Bool) :
    (ConstantLinkFace n n value 2 →₀ K) →ₗ[K] ((Fin n → Bool) →₀ K) :=
  (BooleanCube.GraphCycles.boundary K n).comp
    (Finsupp.domLCongr (constantLinkEdgeEquiv positive value).symm).toLinearMap

/-- Number of independent edge cycles in the constant link at budget `n`. -/
noncomputable def constantLinkCycleRank (positive : 0 < n) (value : Bool) : Nat :=
  Module.finrank K (LinearMap.ker (constantLinkBoundary K positive value))

/-- Passing from canonical cube edges to actual link edges preserves the cycle rank. -/
theorem constantLinkCycleRank_eq_cube (positive : 0 < n) (value : Bool) :
    constantLinkCycleRank K positive value = BooleanCube.GraphCycles.cycleRank K n := by
  classical
  let : Fintype (ConstantLinkFace n n value 2) := Fintype.ofFinite _
  have sameRange : LinearMap.range (constantLinkBoundary K positive value) =
      LinearMap.range (BooleanCube.GraphCycles.boundary K n) := by
    ext chain
    constructor
    · rintro ⟨edges, rfl⟩
      exact ⟨(Finsupp.domLCongr (constantLinkEdgeEquiv positive value).symm : _ ≃ₗ[K] _) edges, rfl⟩
    · rintro ⟨edges, rfl⟩
      refine ⟨(Finsupp.domLCongr (constantLinkEdgeEquiv positive value) : _ ≃ₗ[K] _) edges, ?_⟩
      simp only [constantLinkBoundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        ← Finsupp.domLCongr_symm, LinearEquiv.symm_apply_apply]
  have linkRank : Module.finrank K (LinearMap.range (constantLinkBoundary K positive value)) +
      constantLinkCycleRank K positive value = Module.finrank K (ConstantLinkFace n n value 2 →₀ K) :=
    (constantLinkBoundary K positive value).finrank_range_add_finrank_ker
  have cubeRank : Module.finrank K (LinearMap.range (BooleanCube.GraphCycles.boundary K n)) +
      BooleanCube.GraphCycles.cycleRank K n = Module.finrank K (BooleanCube.GraphCycles.Edge n →₀ K) :=
    (BooleanCube.GraphCycles.boundary K n).finrank_range_add_finrank_ker
  have counts := Fintype.card_congr (constantLinkEdgeEquiv positive value)
  rw [sameRange] at linkRank
  simp only [Module.finrank_finsupp_self, ← counts] at linkRank
  simp only [Module.finrank_finsupp_self] at cubeRank
  omega

/-- The exact graph cycle rank of either constant link, over any coefficient field. -/
theorem constantLinkCycleRank_eq (positive : 0 < n) (value : Bool) :
    constantLinkCycleRank K positive value = n * 2 ^ (n - 1) + 1 - 2 ^ n := by
  rw [constantLinkCycleRank_eq_cube, BooleanCube.GraphCycles.cycleRank_eq]

end Algebraic.DeMorgan
