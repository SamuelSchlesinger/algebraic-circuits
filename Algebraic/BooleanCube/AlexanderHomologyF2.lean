import Algebraic.BooleanCube.SimplicialSpacesF2
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Combinatorial Alexander duality over F2

The proof follows the elementary relative-chain argument of Björner and Tancer,
<https://arxiv.org/abs/0710.1172>. Full-simplex contraction identifies relative
homology with shifted reduced homology. Complementing faces identifies the same
relative quotient with reduced cohomology of the Alexander dual. The coefficient
field is F2; no claim about integral torsion is made.
-/

namespace Algebraic.BooleanCube.SimplicialF2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Representatives of relative cycles of the full simplex modulo the face family. -/
def relativeCycles (faces : Set (Finset ι)) (degree : ℤ) : Submodule (ZMod 2) (Chains ι) :=
  graded degree ⊓ (chainSpace faces (degree - 1)).comap boundary

/-- Relative boundaries include ambient boundaries and all chains in the face family. -/
def relativeBoundaries (faces : Set (Finset ι)) (degree : ℤ) : Submodule (ZMod 2) (Chains ι) :=
  (graded (degree + 1)).map boundary ⊔ chainSpace faces degree

/-- Relative homology expressed using ambient representatives. -/
abbrev RelativeHomology (faces : Set (Finset ι)) (degree : ℤ) :=
  (relativeCycles faces degree) ⧸
    (relativeBoundaries faces degree).comap (relativeCycles faces degree).subtype

/-- The relative boundary submodule lies in the relative cycle module. -/
theorem relativeBoundaries_le_cycles (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    relativeBoundaries faces degree ≤ relativeCycles faces degree := by
  apply sup_le
  · rintro _ ⟨chain, member, rfl⟩
    exact ⟨by simpa using boundary_graded member, by simp⟩
  · intro chain member
    exact ⟨member.2, boundary_chainSpace faces downward member⟩

/-- Boundary sends a relative cycle to a reduced cycle in the face family. -/
def relativeToCycles (faces : Set (Finset ι)) (degree : ℤ) :
    relativeCycles faces degree →ₗ[ZMod 2] cycles faces (degree - 1) :=
  (boundary.comp (relativeCycles faces degree).subtype).codRestrict _
    (fun chain => ⟨chain.property.2, boundary_boundary (chain : Chains ι)⟩)

/-- The connecting map to reduced homology before quotienting relative boundaries. -/
def relativeToHomology (faces : Set (Finset ι)) (degree : ℤ) :
    relativeCycles faces degree →ₗ[ZMod 2] Homology faces (degree - 1) :=
  ((boundaries faces (degree - 1)).comap (cycles faces (degree - 1)).subtype).mkQ.comp
    (relativeToCycles faces degree)

/-- A cycle in the full augmented simplex is filled by its cone. -/
theorem boundary_cone_eq (vertex : ι) {chain : Chains ι} (cycle : boundary chain = 0) :
    boundary (cone vertex chain) = chain := by
  simpa [cycle] using boundary_cone_add_cone_boundary vertex chain

/-- A relative cycle maps to a boundary exactly when it is a relative boundary. -/
theorem boundary_mem_boundaries_iff (vertex : ι) (faces : Set (Finset ι)) (degree : ℤ)
    {chain : Chains ι} (member : chain ∈ relativeCycles faces degree) :
    boundary chain ∈ boundaries faces (degree - 1) ↔ chain ∈ relativeBoundaries faces degree := by
  constructor
  · rintro ⟨inside, insideMember, same⟩
    have insideMember' : inside ∈ chainSpace faces degree := by simpa using insideMember
    have closed : boundary (chain + inside) = 0 := by rw [map_add, same]; exact CharTwo.add_self_eq_zero _
    have filled := boundary_cone_eq vertex closed
    refine Submodule.mem_sup.mpr ⟨boundary (cone vertex (chain + inside)),
      ⟨cone vertex (chain + inside), cone_graded vertex ((graded degree).add_mem member.1 insideMember'.2), rfl⟩,
      inside, insideMember', ?_⟩
    rw [filled]
    simp [add_assoc, CharTwo.add_self_eq_zero]
  · intro present
    obtain ⟨outside, ⟨filling, _, rfl⟩, inside, insideMember, rfl⟩ := Submodule.mem_sup.mp present
    rw [map_add, boundary_boundary, zero_add]
    exact ⟨inside, by simpa using insideMember, rfl⟩

/-- The connecting map has precisely the relative boundary kernel. -/
theorem relativeToHomology_ker (vertex : ι) (faces : Set (Finset ι)) (degree : ℤ) :
    LinearMap.ker (relativeToHomology faces degree) =
      (relativeBoundaries faces degree).comap (relativeCycles faces degree).subtype := by
  ext chain
  change Submodule.Quotient.mk (relativeToCycles faces degree chain) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact boundary_mem_boundaries_iff vertex faces degree chain.property

/-- Every reduced homology class is the boundary of a relative cone class. -/
theorem relativeToHomology_surjective (vertex : ι) (faces : Set (Finset ι)) (degree : ℤ) :
    Function.Surjective (relativeToHomology faces degree) := by
  intro target
  obtain ⟨cycle, rfl⟩ := ((boundaries faces (degree - 1)).comap (cycles faces (degree - 1)).subtype).mkQ_surjective target
  have filled := boundary_cone_eq vertex cycle.property.2
  refine ⟨⟨cone vertex cycle, by
    refine ⟨by simpa using cone_graded vertex cycle.property.1.2, ?_⟩
    change boundary (cone vertex cycle) ∈ chainSpace faces (degree - 1)
    rw [filled]
    exact cycle.property.1⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk cycle
  congr 1
  exact Subtype.ext filled

/-- Full-simplex contraction induces the degree-shifted relative homology equivalence. -/
noncomputable def relativeHomologyEquiv (vertex : ι) (faces : Set (Finset ι)) (degree : ℤ) :
    RelativeHomology faces degree ≃ₗ[ZMod 2] Homology faces (degree - 1) :=
  (Submodule.quotEquivOfEq _ _ (relativeToHomology_ker vertex faces degree).symm).trans
    ((relativeToHomology faces degree).quotKerEquivOfSurjective (relativeToHomology_surjective vertex faces degree))

/-- Vanishing after complementary dual projection is exactly support on the original family. -/
theorem project_dual_complement_eq_zero_iff (faces : Set (Finset ι)) (chain : Chains ι) :
    project (Complex.dual faces) (complement chain) = 0 ↔ chain ∈ supported faces := by
  classical
  constructor
  · intro equal support absent
    have coefficient := congrFun equal supportᶜ
    simpa [project_apply, absent] using coefficient
  · intro member
    ext support
    by_cases present : supportᶜ ∈ faces
    · simp [project_apply, present]
    · simp [project_apply, present, member _ present]

/-- Relative cycles give cocycles after complementing and retaining only dual faces. -/
theorem project_dual_complement_cocycle (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ)
    {chain : Chains ι} (member : chain ∈ relativeCycles faces degree) :
    project (Complex.dual faces) (complement chain) ∈ cocycles (Complex.dual faces) ((Fintype.card ι : ℤ) - degree) := by
  refine ⟨project_chainSpace _ (complement_graded member.1), ?_⟩
  change delta _ (project _ (complement chain)) = 0
  rw [delta_project _ (Complex.dual_downward faces downward), delta_apply, coboundary_complement]
  exact (project_dual_complement_eq_zero_iff faces _).mpr member.2.1

/-- A dual cocycle, complemented, is a relative cycle. -/
theorem complement_cocycle_relative (faces : Set (Finset ι)) (degree : ℤ)
    {chain : Chains ι} (member : chain ∈ cocycles (Complex.dual faces) ((Fintype.card ι : ℤ) - degree)) :
    complement chain ∈ relativeCycles faces degree := by
  have grade : complement chain ∈ graded degree := by
    simpa only [sub_sub_cancel] using complement_graded member.1.2
  refine ⟨grade, ?_, boundary_graded grade⟩
  · apply (project_dual_complement_eq_zero_iff faces _).mp
    rw [← coboundary_complement, complement_complement]
    exact member.2

/-- Complementation followed by dual projection induces a map to reduced cohomology. -/
noncomputable def relativeToCohomology (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    relativeCycles faces degree →ₗ[ZMod 2] Cohomology (Complex.dual faces) ((Fintype.card ι : ℤ) - degree) :=
  let target := cocycles (Complex.dual faces) ((Fintype.card ι : ℤ) - degree)
  let map := (((project (Complex.dual faces)).comp complement.toLinearMap).comp
    (relativeCycles faces degree).subtype).codRestrict target
      (fun chain => project_dual_complement_cocycle faces downward degree chain.property)
  ((coboundaries (Complex.dual faces) ((Fintype.card ι : ℤ) - degree)).comap target.subtype).mkQ.comp map

/-- Every dual cohomology class has a complementary relative-chain representative. -/
theorem relativeToCohomology_surjective (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    Function.Surjective (relativeToCohomology faces downward degree) := by
  intro target
  obtain ⟨cycle, rfl⟩ := ((coboundaries (Complex.dual faces) ((Fintype.card ι : ℤ) - degree)).comap
    (cocycles (Complex.dual faces) ((Fintype.card ι : ℤ) - degree)).subtype).mkQ_surjective target
  refine ⟨⟨complement cycle, complement_cocycle_relative faces degree cycle.property⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk cycle
  congr 1
  apply Subtype.ext
  change project _ (complement (complement (cycle : Chains ι))) = _
  rw [complement_complement, project_eq_self _ cycle.property.1.1]

/-- Complementary projection is a coboundary exactly for relative boundary representatives. -/
theorem project_dual_complement_mem_coboundaries_iff (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ)
    {chain : Chains ι} (member : chain ∈ graded degree) :
    project (Complex.dual faces) (complement chain) ∈
      coboundaries (Complex.dual faces) ((Fintype.card ι : ℤ) - degree) ↔
    chain ∈ relativeBoundaries faces degree := by
  constructor
  · rintro ⟨primitive, primitiveMember, same⟩
    have primitiveGrade : complement primitive ∈ graded (degree + 1) := by
      have grade := complement_graded primitiveMember.2
      have degreeEq : (Fintype.card ι : ℤ) - ((Fintype.card ι : ℤ) - degree - 1) = degree + 1 := by omega
      simpa only [degreeEq] using grade
    have boundaryGrade : boundary (complement primitive) ∈ graded degree := by
      simpa using boundary_graded primitiveGrade
    have inside : chain + boundary (complement primitive) ∈ supported faces := by
      apply (project_dual_complement_eq_zero_iff faces _).mp
      rw [map_add, map_add, ← coboundary_complement, complement_complement, ← delta_apply, same]
      exact CharTwo.add_self_eq_zero _
    refine Submodule.mem_sup.mpr ⟨boundary (complement primitive), ⟨complement primitive, primitiveGrade, rfl⟩,
      chain + boundary (complement primitive), ⟨inside, (graded degree).add_mem member boundaryGrade⟩, ?_⟩
    simp [add_left_comm, CharTwo.add_self_eq_zero]
  · intro present
    obtain ⟨outside, ⟨primitive, primitiveGrade, rfl⟩, inside, insideMember, rfl⟩ := Submodule.mem_sup.mp present
    have dualGrade : complement primitive ∈ graded ((Fintype.card ι : ℤ) - degree - 1) := by
      have grade := complement_graded primitiveGrade
      have degreeEq : (Fintype.card ι : ℤ) - (degree + 1) = (Fintype.card ι : ℤ) - degree - 1 := by omega
      simpa only [degreeEq] using grade
    refine ⟨project (Complex.dual faces) (complement primitive), project_chainSpace _ dualGrade, ?_⟩
    rw [delta_project _ (Complex.dual_downward faces downward), delta_apply, coboundary_complement]
    rw [map_add, map_add, (project_dual_complement_eq_zero_iff faces inside).mpr insideMember.1, add_zero]

/-- The dual cohomology map has the same relative boundary kernel as the connecting map. -/
theorem relativeToCohomology_ker (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    LinearMap.ker (relativeToCohomology faces downward degree) =
      (relativeBoundaries faces degree).comap (relativeCycles faces degree).subtype := by
  ext chain
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact project_dual_complement_mem_coboundaries_iff faces downward degree chain.property.1

/-- Complementing faces induces the relative-homology to dual-cohomology equivalence. -/
noncomputable def relativeCohomologyEquiv (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    RelativeHomology faces degree ≃ₗ[ZMod 2] Cohomology (Complex.dual faces) ((Fintype.card ι : ℤ) - degree) :=
  (Submodule.quotEquivOfEq _ _ (relativeToCohomology_ker faces downward degree).symm).trans
    ((relativeToCohomology faces downward degree).quotKerEquivOfSurjective
      (relativeToCohomology_surjective faces downward degree))

private def homologyRegrade (faces : Set (Finset ι)) {left right : ℤ} (equal : left = right) :
    Homology faces left ≃ₗ[ZMod 2] Homology faces right := by
  subst right
  exact LinearEquiv.refl _ _

private noncomputable def cohomologyRegrade (faces : Set (Finset ι)) {left right : ℤ} (equal : left = right) :
    Cohomology faces left ≃ₗ[ZMod 2] Cohomology faces right := by
  subst right
  exact LinearEquiv.refl _ _

/-- Alexander duality in cardinality grading: `H[k]` is `H^[N-k-1]` of the dual. -/
noncomputable def alexanderDuality (vertex : ι) (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    Homology faces degree ≃ₗ[ZMod 2] Cohomology (Complex.dual faces) ((Fintype.card ι : ℤ) - degree - 1) := by
  have equivalence := (relativeHomologyEquiv vertex faces (degree + 1)).symm.trans
    (relativeCohomologyEquiv faces downward (degree + 1))
  have degreeEq : (Fintype.card ι : ℤ) - (degree + 1) = (Fintype.card ι : ℤ) - degree - 1 := by omega
  exact ((homologyRegrade faces (show degree + 1 - 1 = degree by omega)).symm.trans equivalence).trans
    (cohomologyRegrade (Complex.dual faces) degreeEq)

/-- Traditional reduced-degree indexing for simplicial homology. -/
abbrev ReducedHomology (faces : Set (Finset ι)) (degree : ℤ) := Homology faces (degree + 1)

/-- Traditional reduced-degree indexing for simplicial cohomology. -/
abbrev ReducedCohomology (faces : Set (Finset ι)) (degree : ℤ) := Cohomology faces (degree + 1)

/-- Combinatorial Alexander duality, including augmented and out-of-range degrees. -/
noncomputable def reducedAlexanderDuality (vertex : ι) (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    ReducedHomology faces degree ≃ₗ[ZMod 2]
      ReducedCohomology (Complex.dual faces) ((Fintype.card ι : ℤ) - degree - 3) := by
  have equivalence := alexanderDuality vertex faces downward (degree + 1)
  have degreeEq : (Fintype.card ι : ℤ) - (degree + 1) - 1 = ((Fintype.card ι : ℤ) - degree - 3) + 1 := by omega
  exact equivalence.trans (cohomologyRegrade (Complex.dual faces) degreeEq)

/-- The reduced homological Betti number over F2. -/
noncomputable def reducedBetti (faces : Set (Finset ι)) (degree : ℤ) : ℕ :=
  Module.finrank (ZMod 2) (ReducedHomology faces degree)

/-- The reduced cohomological Betti number over F2. -/
noncomputable def reducedCoBetti (faces : Set (Finset ι)) (degree : ℤ) : ℕ :=
  Module.finrank (ZMod 2) (ReducedCohomology faces degree)

/-- Alexander duality transports actual homological dimensions to dual cohomological dimensions. -/
theorem reducedBetti_dual_eq (vertex : ι) (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    reducedBetti faces degree = reducedCoBetti (Complex.dual faces) ((Fintype.card ι : ℤ) - degree - 3) :=
  (reducedAlexanderDuality vertex faces downward degree).finrank_eq

end Algebraic.BooleanCube.SimplicialF2
