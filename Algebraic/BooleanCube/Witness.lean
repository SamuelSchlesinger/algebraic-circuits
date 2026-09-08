import Algebraic.BooleanCube.Betti

/-!
# Localized witnesses from cubical cycles

A positive-degree cycle has an explicit filling whose vertices are prefix
erasures of vertices in its support. If the cycle does not bound in a target
complex, this finite list contains a vertex outside that complex. A linear
cochain provides a reusable certificate that a chain is not a boundary.
-/

namespace Algebraic.BooleanCube.Chains

variable (R : Type*) [CommRing R]

/-- The vertices of all faces with nonzero coefficient in a chain. -/
noncomputable def vertices (chain : Chains R n) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun vertex => ∃ face ∈ chain.support, face.Contains vertex)

/-- Membership in a chain's vertex support. -/
@[simp] theorem mem_vertices (chain : Chains R n) (vertex : Fin n → Bool) :
    vertex ∈ vertices R chain ↔ ∃ face ∈ chain.support, face.Contains vertex := by
  classical
  simp [vertices]

/-- A supported chain uses only vertices of its admitted vertex set. -/
theorem vertices_subset {left : Set (Fin n → Bool)} {degree : Nat} {chain : Chains R n}
    (member : chain ∈ level R left degree) : (vertices R chain : Set (Fin n → Bool)) ⊆ left := by
  intro vertex contained
  obtain ⟨face, support, contains⟩ := (mem_vertices R chain vertex).mp contained
  exact (member support).1 vertex contains

/-- Restricting a chain to its own vertex support preserves its degree. -/
theorem mem_level_vertices {left : Set (Fin n → Bool)} {degree : Nat} {chain : Chains R n}
    (member : chain ∈ level R left degree) : chain ∈ level R (vertices R chain) degree := by
  intro face support
  exact ⟨fun vertex contains => (mem_vertices R chain vertex).mpr ⟨face, support, contains⟩,
    (member support).2⟩

/-- Erasing beyond the last coordinate is the same as erasing through it. -/
theorem erase_min_dimension (threshold : Nat) (vertex : Fin n → Bool) :
    erase Fin.val (min threshold n) vertex = erase Fin.val threshold vertex := by
  funext i
  simp [erase, patch, i.isLt]

/-- The finite candidate list used by the erasure filling of a chain. -/
noncomputable def erasureVertices (chain : Chains R n) : Finset (Fin n → Bool) := by
  classical
  exact ((Finset.range (n + 1)).product (vertices R chain)).image
    (fun pair => erase Fin.val pair.1 pair.2)

/-- Candidates are precisely bounded prefix erasures of supported vertices. -/
@[simp] theorem mem_erasureVertices (chain : Chains R n) (vertex : Fin n → Bool) :
    vertex ∈ erasureVertices R chain ↔
      ∃ threshold ≤ n, ∃ original ∈ vertices R chain,
        erase Fin.val threshold original = vertex := by
  classical
  constructor
  · intro candidate
    obtain ⟨⟨threshold, original⟩, pairMember, equal⟩ := Finset.mem_image.mp candidate
    obtain ⟨bound, member⟩ := Finset.mem_product.mp pairMember
    exact ⟨threshold, by simpa using bound, original, member, equal⟩
  · rintro ⟨threshold, bound, original, member, equal⟩
    exact Finset.mem_image.mpr ⟨(threshold, original),
      Finset.mem_product.mpr ⟨by simpa using bound, member⟩, equal⟩

/-- Every prefix erasure occurs in the finite candidate list. -/
theorem erase_mem_erasureVertices (chain : Chains R n) (threshold : Nat)
    {vertex : Fin n → Bool} (member : vertex ∈ vertices R chain) :
    erase Fin.val threshold vertex ∈ erasureVertices R chain :=
  (mem_erasureVertices R chain _).mpr
    ⟨min threshold n, Nat.min_le_right _ _, vertex, member, erase_min_dimension threshold vertex⟩

/-- The candidate list has at most one vertex per source vertex and threshold. -/
theorem card_erasureVertices_le (chain : Chains R n) :
    (erasureVertices R chain).card ≤ (n + 1) * (vertices R chain).card := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp)

/-- A nonbounding positive-degree cycle forces a missing vertex in its erasure list. -/
theorem exists_erasure_vertex_not_mem (left right : Set (Fin n → Bool))
    (degree : Nat) (positive : 0 < degree) (chain : Chains R n)
    (closed : chain ∈ cycles R left degree)
    (nonboundary : chain ∉ boundaries R right degree) :
    ∃ vertex ∈ erasureVertices R chain, vertex ∉ right := by
  classical
  by_contra! allInside
  apply nonboundary
  apply cycles_le_boundaries R (vertices R chain) right degree positive
    (fun threshold vertex member => allInside _ (erase_mem_erasureVertices R chain threshold member))
  exact ⟨mem_level_vertices R closed.1, closed.2⟩

/-- A cochain detecting a chain and annihilating admitted face boundaries certifies nonbounding. -/
theorem not_mem_boundaries_of_cochain (vertices : Set (Fin n → Bool)) (degree : Nat)
    (cochain : Chains R n →ₗ[R] R)
    (vanishes : ∀ face : Face n, face.Allowed vertices → face.dimension = degree + 1 →
      cochain (boundary R n (Finsupp.single face 1)) = 0)
    {chain : Chains R n} (detected : cochain chain ≠ 0) :
    chain ∉ boundaries R vertices degree := by
  rintro ⟨filling, member, rfl⟩
  apply detected
  exact map_supported R (cochain.comp (boundary R n)) _ (⊥ : Submodule R R)
    (fun face allowed => vanishes face allowed.1 allowed.2) member

end Algebraic.BooleanCube.Chains
