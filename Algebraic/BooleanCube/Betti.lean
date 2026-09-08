import Algebraic.BooleanCube.ChainSupport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finite cubical homology and shell counting

Cubical homology is the quotient of cycles by boundaries in the oriented
finite face complex. A bounded erasure fills every positive-degree cycle.
Rank-nullity then bounds the old Betti number by the number of new faces.
-/

namespace Algebraic.BooleanCube
namespace Chains

variable (R : Type*) [CommRing R]

/-- Chains supported on admitted faces of one dimension. -/
noncomputable def level (vertices : Set (Fin n → Bool)) (degree : Nat) : Submodule R (Chains R n) :=
  Finsupp.supported R R {face | face.Allowed vertices ∧ face.dimension = degree}

/-- Degreewise chain modules are monotone in the admitted vertices. -/
theorem level_mono {left right : Set (Fin n → Bool)} (included : left ⊆ right) (degree : Nat) :
    level R left degree ≤ level R right degree :=
  Finsupp.supported_mono (fun _ h => ⟨Face.allowed_mono included h.1, h.2⟩)

/-- Boundary preserves the admitted vertices and lowers the degree by one. -/
theorem boundary_mem_level (vertices : Set (Fin n → Bool)) (degree : Nat)
    {chain : Chains R n} (member : chain ∈ level R vertices (degree + 1)) :
    boundary R n chain ∈ level R vertices degree := by
  apply map_supported R (boundary R n) _ (level R vertices degree) _ member
  intro face allowed result support
  have faceDim := allowed.2
  obtain ⟨subface, dim⟩ := boundary_support R face support
  exact ⟨fun vertex contained => allowed.1 vertex (subface vertex contained), by omega⟩

/-- Augmentation vanishes on all positive-degree chains. -/
theorem augmentation_eq_zero (vertices : Set (Fin n → Bool)) (degree : Nat) (positive : 0 < degree)
    {chain : Chains R n} (member : chain ∈ level R vertices degree) :
    augmentation R n chain = 0 := by
  apply (show augmentation R n chain ∈ (⊥ : Submodule R (Chains R n)) from ?_)
  apply map_supported R (augmentation R n) _ ⊥ _ member
  intro face allowed
  have faceDim := allowed.2
  exact augmentation_single_eq_zero R face (by omega)

/-- The prism stays in any vertex set containing the prefix erasures of the source. -/
theorem prism_mem_level (left right : Set (Fin n → Bool)) (degree : Nat)
    (erases : ∀ threshold vertex, vertex ∈ left → erase Fin.val threshold vertex ∈ right)
    {chain : Chains R n} (member : chain ∈ level R left degree) :
    prism R n chain ∈ level R right (degree + 1) := by
  apply map_supported R (prism R n) _ (level R right (degree + 1)) _ member
  intro face allowed result support
  have faceDim := allowed.2
  obtain ⟨dim, swept⟩ := prism_support R face support
  refine ⟨?_, by omega⟩
  intro vertex contained
  obtain ⟨original, originalContains, threshold, rfl⟩ := swept vertex contained
  exact erases threshold original (allowed.1 original originalContains)

/-- Cubical cycles in one degree. -/
noncomputable def cycles (vertices : Set (Fin n → Bool)) (degree : Nat) : Submodule R (Chains R n) :=
  level R vertices degree ⊓ LinearMap.ker (boundary R n)

/-- The cycle module is an additive commutative group. -/
noncomputable instance cyclesAddCommGroup (vertices : Set (Fin n → Bool)) (degree : Nat) :
    AddCommGroup (cycles R vertices degree) := inferInstance

/-- Cubical boundaries in one degree, as a submodule of the ambient chain module. -/
noncomputable def boundaries (vertices : Set (Fin n → Bool)) (degree : Nat) : Submodule R (Chains R n) :=
  (level R vertices (degree + 1)).map (boundary R n)

/-- Every cubical boundary is a cubical cycle. -/
theorem boundaries_le_cycles (vertices : Set (Fin n → Bool)) (degree : Nat) :
    boundaries R vertices degree ≤ cycles R vertices degree := by
  rintro _ ⟨chain, member, rfl⟩
  exact ⟨boundary_mem_level R vertices degree member, boundary_boundary R n chain⟩

/-- Boundaries viewed inside the cycle module. -/
noncomputable def cycleBoundaries (vertices : Set (Fin n → Bool)) (degree : Nat) :
    Submodule R (cycles R vertices degree) :=
  (boundaries R vertices degree).comap (cycles R vertices degree).subtype

/-- Finite cubical homology, with the standard cycles-modulo-boundaries definition. -/
abbrev Homology (vertices : Set (Fin n → Bool)) (degree : Nat) :=
  cycles R vertices degree ⧸ cycleBoundaries R vertices degree

/-- Every positive-degree source cycle bounds in a set containing its prefix erasures. -/
theorem cycles_le_boundaries (left right : Set (Fin n → Bool)) (degree : Nat) (positive : 0 < degree)
    (erases : ∀ threshold vertex, vertex ∈ left → erase Fin.val threshold vertex ∈ right) :
    cycles R left degree ≤ boundaries R right degree := by
  intro chain member
  refine ⟨prism R n chain, prism_mem_level R left right degree erases member.1, ?_⟩
  have identity := boundary_prism_add_prism_boundary R n chain
  have augmentation := augmentation_eq_zero R left degree positive member.1
  have closed : boundary R n chain = 0 := member.2
  simpa [closed, augmentation] using identity

end Chains

namespace CubicalHomology

variable (K : Type*) [Field K]

/-- The cubical Betti number over a field. -/
noncomputable def betti (vertices : Set (Fin n → Bool)) (degree : Nat) : Nat :=
  Module.finrank K (Chains.Homology K vertices degree)

/-- An admitted face is one basis vector of the corresponding finite chain module. -/
theorem finrank_level (vertices : Set (Fin n → Bool)) (degree : Nat) :
    Module.finrank K (Chains.level K vertices degree) = (Face.faces vertices degree).card := by
  classical
  rw [Chains.level, (Finsupp.supportedEquivFinsupp (R := K) _).finrank_eq]
  simp [Face.faces]

/-- The quotient definition gives the usual cycles-minus-boundaries dimension formula. -/
theorem betti_add_finrank_boundaries (vertices : Set (Fin n → Bool)) (degree : Nat) :
    betti K vertices degree + Module.finrank K (Chains.boundaries K vertices degree) =
      Module.finrank K (Chains.cycles K vertices degree) := by
  have dimension := (Chains.cycleBoundaries K vertices degree).finrank_quotient_add_finrank
  have same := (Submodule.comapSubtypeEquivOfLe
    (Chains.boundaries_le_cycles K vertices degree)).finrank_eq
  change Module.finrank K (Chains.cycleBoundaries K vertices degree) =
    Module.finrank K (Chains.boundaries K vertices degree) at same
  simpa only [← same, betti, Chains.Homology] using dimension

/-- A cycle which is not a boundary certifies a positive cubical Betti number. -/
theorem betti_pos_of_cycle (vertices : Set (Fin n → Bool)) (degree : Nat)
    (chain : Chains K n) (closed : chain ∈ Chains.cycles K vertices degree)
    (nonboundary : chain ∉ Chains.boundaries K vertices degree) :
    0 < betti K vertices degree := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨Submodule.Quotient.mk ⟨chain, closed⟩, ?_⟩
  intro zero
  have member : (⟨chain, closed⟩ : Chains.cycles K vertices degree) ∈
      Chains.cycleBoundaries K vertices degree :=
    (Submodule.Quotient.mk_eq_zero _).mp zero
  exact nonboundary member

end CubicalHomology
end Algebraic.BooleanCube
