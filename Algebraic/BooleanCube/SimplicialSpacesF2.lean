import Algebraic.BooleanCube.SimplicialF2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Graded chains, cochains, and reduced homology over F2

Integer cardinality grading retains the augmented empty face and makes out-of-range
degrees zero. Homology and cohomology are the actual cycle modules modulo images
of the appropriate differentials, rather than Euler-characteristic expressions.
-/

namespace Algebraic.BooleanCube.SimplicialF2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficients supported on a specified face family. -/
def supported (faces : Set (Finset ι)) : Submodule (ZMod 2) (Chains ι) where
  carrier := {chain | ∀ support, support ∉ faces → chain support = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb support absent; simp [ha support absent, hb support absent]
  smul_mem' := by intro a b hb support absent; simp [hb support absent]

/-- Chains concentrated in one cardinality degree; degree zero is the empty simplex. -/
def graded (degree : ℤ) : Submodule (ZMod 2) (Chains ι) where
  carrier := {chain | ∀ support, (support.card : ℤ) ≠ degree → chain support = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb support wrong; simp [ha support wrong, hb support wrong]
  smul_mem' := by intro a b hb support wrong; simp [hb support wrong]

/-- The augmented chain or cochain space of a family in a fixed cardinality degree. -/
def chainSpace (faces : Set (Finset ι)) (degree : ℤ) : Submodule (ZMod 2) (Chains ι) :=
  supported faces ⊓ graded degree

/-- Delete all coefficients outside the face family. -/
noncomputable def project (faces : Set (Finset ι)) : Chains ι →ₗ[ZMod 2] Chains ι := by
  classical
  exact {
    toFun := fun chain support => if support ∈ faces then chain support else 0
    map_add' := by intro a b; ext support; by_cases member : support ∈ faces <;> simp [member]
    map_smul' := by intro a b; ext support; by_cases member : support ∈ faces <;> simp [member] }

omit [Fintype ι] [DecidableEq ι] in
open scoped Classical in
/-- Projection retains exactly the coefficients on the family. -/
theorem project_apply (faces : Set (Finset ι)) (chain : Chains ι) (support : Finset ι) :
    project faces chain support = if support ∈ faces then chain support else 0 := by
  classical
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Projection always has the requested support. -/
theorem project_supported (faces : Set (Finset ι)) (chain : Chains ι) :
    project faces chain ∈ supported faces := by
  classical
  intro support absent
  simp [project_apply, absent]

omit [Fintype ι] [DecidableEq ι] in
/-- Projection fixes a chain already supported on the family. -/
theorem project_eq_self (faces : Set (Finset ι)) {chain : Chains ι} (member : chain ∈ supported faces) :
    project faces chain = chain := by
  classical
  ext support
  by_cases present : support ∈ faces
  · simp [project_apply, present]
  · simp [project_apply, present, member support present]

omit [Fintype ι] [DecidableEq ι] in
/-- Projection respects cardinality grading. -/
theorem project_graded (faces : Set (Finset ι)) {chain : Chains ι} (member : chain ∈ graded degree) :
    project faces chain ∈ graded degree := by
  classical
  intro support wrong
  simp [project_apply, member support wrong]

omit [Fintype ι] [DecidableEq ι] in
/-- A projected chain belongs to the corresponding graded chain space. -/
theorem project_chainSpace (faces : Set (Finset ι)) {chain : Chains ι} (member : chain ∈ graded degree) :
    project faces chain ∈ chainSpace faces degree :=
  ⟨project_supported faces chain, project_graded faces member⟩

/-- Deleting a vertex lowers cardinality degree by one. -/
theorem boundary_graded {chain : Chains ι} (member : chain ∈ graded degree) :
    boundary chain ∈ graded (degree - 1) := by
  intro support wrong
  apply Finset.sum_eq_zero
  intro i _
  by_cases present : i ∈ support
  · simp [present]
  · rw [if_neg present]
    apply member
    rw [Finset.card_insert_of_notMem present, Nat.cast_add, Nat.cast_one]
    omega

/-- Downward closure makes the boundary preserve support. -/
theorem boundary_supported (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces)
    {chain : Chains ι} (member : chain ∈ supported faces) : boundary chain ∈ supported faces := by
  intro support absent
  apply Finset.sum_eq_zero
  intro i _
  have missing : insert i support ∉ faces := fun present => absent (downward (Finset.subset_insert _ _) present)
  simp [member _ missing]

/-- The boundary maps each simplicial chain space into the previous degree. -/
theorem boundary_chainSpace (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces)
    {chain : Chains ι} (member : chain ∈ chainSpace faces degree) :
    boundary chain ∈ chainSpace faces (degree - 1) :=
  ⟨boundary_supported faces downward member.1, boundary_graded member.2⟩

omit [Fintype ι] in
/-- Coning raises the cardinality degree by one. -/
theorem cone_graded (vertex : ι) {chain : Chains ι} (member : chain ∈ graded degree) :
    cone vertex chain ∈ graded (degree + 1) := by
  intro support wrong
  rw [cone_apply]
  split_ifs with present
  · apply member
    have card := Finset.card_erase_add_one present
    omega
  · rfl

omit [Fintype ι] in
/-- The transpose differential raises cardinality degree by one. -/
theorem coboundary_graded {chain : Chains ι} (member : chain ∈ graded degree) :
    coboundary chain ∈ graded (degree + 1) := by
  intro support wrong
  apply Finset.sum_eq_zero
  intro i present
  apply member
  have card := Finset.card_erase_add_one present
  omega

/-- Complementation reverses cardinality degrees in the finite Boolean lattice. -/
theorem complement_graded {chain : Chains ι} (member : chain ∈ graded degree) :
    complement chain ∈ graded ((Fintype.card ι : ℤ) - degree) := by
  intro support wrong
  apply member
  have card := Finset.card_add_card_compl support
  omega

/-- The coboundary of a complex is the transpose restricted to its faces. -/
noncomputable def delta (faces : Set (Finset ι)) : Chains ι →ₗ[ZMod 2] Chains ι :=
  (project faces).comp coboundary

omit [Fintype ι] in
/-- The differential discards cofaces outside the complex. -/
theorem delta_apply (faces : Set (Finset ι)) (chain : Chains ι) :
    delta faces chain = project faces (coboundary chain) := rfl

omit [Fintype ι] in
/-- Downward closure allows input coefficients outside the complex to be discarded first. -/
theorem delta_project (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (chain : Chains ι) :
    delta faces (project faces chain) = delta faces chain := by
  classical
  ext support
  simp only [delta_apply, project_apply]
  by_cases present : support ∈ faces
  · simp only [present, ↓reduceIte, coboundary_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp [project_apply, downward (Finset.erase_subset _ _) present]
  · simp [present]

/-- The restricted transpose is a differential. -/
theorem delta_delta (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (chain : Chains ι) :
    delta faces (delta faces chain) = 0 := by
  change delta faces (project faces (coboundary chain)) = 0
  rw [delta_project faces downward, delta_apply, coboundary_coboundary, map_zero]

omit [Fintype ι] in
/-- The restricted transpose maps into the next graded cochain space. -/
theorem delta_chainSpace (faces : Set (Finset ι)) {chain : Chains ι} (member : chain ∈ graded degree) :
    delta faces chain ∈ chainSpace faces (degree + 1) :=
  project_chainSpace faces (coboundary_graded member)

/-- Reduced cycles in cardinality degree `degree`. -/
def cycles (faces : Set (Finset ι)) (degree : ℤ) : Submodule (ZMod 2) (Chains ι) :=
  chainSpace faces degree ⊓ LinearMap.ker boundary

/-- Reduced boundaries in cardinality degree `degree`. -/
def boundaries (faces : Set (Finset ι)) (degree : ℤ) : Submodule (ZMod 2) (Chains ι) :=
  (chainSpace faces (degree + 1)).map boundary

/-- Reduced cocycles in cardinality degree `degree`. -/
noncomputable def cocycles (faces : Set (Finset ι)) (degree : ℤ) : Submodule (ZMod 2) (Chains ι) :=
  chainSpace faces degree ⊓ LinearMap.ker (delta faces)

/-- Reduced coboundaries in cardinality degree `degree`. -/
noncomputable def coboundaries (faces : Set (Finset ι)) (degree : ℤ) : Submodule (ZMod 2) (Chains ι) :=
  (chainSpace faces (degree - 1)).map (delta faces)

/-- Boundaries are cycles in a downward-closed family. -/
theorem boundaries_le_cycles (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    boundaries faces degree ≤ cycles faces degree := by
  rintro _ ⟨chain, member, rfl⟩
  exact ⟨by simpa using boundary_chainSpace faces downward member, boundary_boundary chain⟩

/-- Coboundaries are cocycles in a downward-closed family. -/
theorem coboundaries_le_cocycles (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces) (degree : ℤ) :
    coboundaries faces degree ≤ cocycles faces degree := by
  rintro _ ⟨chain, member, rfl⟩
  exact ⟨by simpa using delta_chainSpace faces member.2, delta_delta faces downward chain⟩

/-- Reduced simplicial homology: the cycle module modulo the boundary submodule. -/
abbrev Homology (faces : Set (Finset ι)) (degree : ℤ) :=
  (cycles faces degree) ⧸ (boundaries faces degree).comap (cycles faces degree).subtype

/-- Reduced simplicial cohomology: the cocycle module modulo the coboundary submodule. -/
abbrev Cohomology (faces : Set (Finset ι)) (degree : ℤ) :=
  (cocycles faces degree) ⧸ (coboundaries faces degree).comap (cocycles faces degree).subtype

end Algebraic.BooleanCube.SimplicialF2
