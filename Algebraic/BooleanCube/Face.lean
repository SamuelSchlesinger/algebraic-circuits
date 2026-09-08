import Algebraic.BooleanCube.Sweep
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite cube faces

`none` denotes a free coordinate; `some false` and `some true` denote fixed
coordinates. Faces are admitted exactly when all their vertices are admitted.
-/

namespace Algebraic.BooleanCube

/-- A face of the coordinate cube. -/
abbrev Face (n : Nat) := Fin n → Option Bool

namespace Face

/-- The set of free coordinates of a face. -/
def free (face : Face n) : Finset (Fin n) := Finset.univ.filter (fun i => face i = none)

/-- The dimension of a cube face. -/
def dimension (face : Face n) : Nat := face.free.card

/-- A Boolean vertex lies in a face when it agrees with every fixed coordinate. -/
def Contains (face : Face n) (vertex : Fin n → Bool) : Prop :=
  ∀ i, face i = none ∨ face i = some (vertex i)

/-- A face is admitted when all its vertices belong to the specified set. -/
def Allowed (vertices : Set (Fin n → Bool)) (face : Face n) : Prop :=
  ∀ vertex, face.Contains vertex → vertex ∈ vertices

/-- Prepend a fixed or free coordinate to a face. -/
def cons (bit : Option Bool) (face : Face n) : Face (n + 1) := Fin.cons bit face

/-- The newly prepended coordinate has the specified value. -/
@[simp] theorem cons_zero (bit : Option Bool) (face : Face n) : face.cons bit 0 = bit := rfl

/-- Prepending a coordinate preserves all tail coordinates. -/
@[simp] theorem cons_succ (bit : Option Bool) (face : Face n) (i : Fin n) :
    face.cons bit i.succ = face i := rfl

/-- Every face decomposes into its first coordinate and its tail. -/
theorem cons_tail (face : Face (n + 1)) : cons (face 0) (Fin.tail face) = face := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- A free coordinate increases face dimension by one; a fixed coordinate preserves it. -/
@[simp] theorem dimension_cons (bit : Option Bool) (face : Face n) :
    (face.cons bit).dimension = face.dimension + if bit = none then 1 else 0 := by
  classical
  simp only [dimension, free, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp only [cons, Fin.cons_zero, Fin.cons_succ]
  omega

/-- Vertex containment separates into head and tail conditions. -/
@[simp] theorem contains_cons (bit : Option Bool) (face : Face n)
    (value : Bool) (vertex : Fin n → Bool) :
    (face.cons bit).Contains (Fin.cons value vertex) ↔
      (bit = none ∨ bit = some value) ∧ face.Contains vertex := by
  simp [Contains, Fin.forall_fin_succ]

/-- The canonical vertex chooses false in every free coordinate. -/
def vertex (face : Face n) : Fin n → Bool := fun i => (face i).getD false

/-- Every face contains its canonical vertex. -/
theorem contains_vertex (face : Face n) : face.Contains face.vertex := by
  intro i
  cases h : face i <;> simp [vertex, h]

/-- A face is determined by any one of its vertices and its free coordinates. -/
theorem eq_of_contains_of_free_eq {left right : Face n} {vertex : Fin n → Bool}
    (hl : left.Contains vertex) (hr : right.Contains vertex) (same : left.free = right.free) :
    left = right := by
  funext i
  have freeSame : left i = none ↔ right i = none := by
    simpa [free] using Finset.ext_iff.mp same i
  rcases hl i with h | h
  · exact h.trans (freeSame.mp h).symm
  · rcases hr i with h' | h'
    · exact (freeSame.mpr h').trans h'.symm
    · exact h.trans h'.symm

/-- Enlarging the admitted vertex set enlarges the admitted faces. -/
theorem allowed_mono {left right : Set (Fin n → Bool)} (included : left ⊆ right)
    {face : Face n} (allowed : face.Allowed left) : face.Allowed right :=
  fun vertex member => included (allowed vertex member)

/-- The finite set of admitted faces in a fixed dimension. -/
noncomputable def faces (vertices : Set (Fin n → Bool)) (degree : Nat) : Finset (Face n) := by
  classical
  exact Finset.univ.filter (fun face => face.Allowed vertices ∧ face.dimension = degree)

/-- Membership in the finite face set is exactly admission and dimension. -/
@[simp] theorem mem_faces (vertices : Set (Fin n → Bool)) (degree : Nat) (face : Face n) :
    face ∈ faces vertices degree ↔ face.Allowed vertices ∧ face.dimension = degree := by
  classical
  simp [faces]

/-- Face sets are monotone in their admitted vertices. -/
theorem faces_mono {left right : Set (Fin n → Bool)} (included : left ⊆ right) (degree : Nat) :
    faces left degree ⊆ faces right degree := by
  intro face member
  obtain ⟨allowed, dim⟩ := (mem_faces _ _ _).mp member
  exact (mem_faces _ _ _).mpr ⟨allowed_mono included allowed, dim⟩

/-- Every newly admitted face has at least one newly admitted vertex. -/
theorem exists_new_vertex {left right : Set (Fin n → Bool)} {face : Face n}
    (new : face.Allowed right) (old : ¬face.Allowed left) :
    ∃ vertex, face.Contains vertex ∧ vertex ∈ right \ left := by
  classical
  simp only [Allowed, not_forall] at old
  obtain ⟨vertex, h⟩ := old
  obtain ⟨member, missing⟩ := h
  exact ⟨vertex, member, new vertex member, missing⟩

/-- The vertices admitted by the second set but absent from the first. -/
noncomputable def newVertices (left right : Set (Fin n → Bool)) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun vertex => vertex ∈ right \ left)

/-- Membership in the new-vertex set is exactly membership in the set difference. -/
@[simp] theorem mem_newVertices (left right : Set (Fin n → Bool)) (vertex : Fin n → Bool) :
    vertex ∈ newVertices left right ↔ vertex ∈ right \ left := by
  classical
  simp [newVertices]

/-- Each newly admitted vertex can account for at most `choose n degree` new faces. -/
theorem card_new_faces_le (left right : Set (Fin n → Bool)) (degree : Nat) :
    (faces right degree \ faces left degree).card ≤
      n.choose degree * (newVertices left right).card := by
  classical
  let newFaces := faces right degree \ faces left degree
  have witness : ∀ face ∈ newFaces,
      ∃ vertex, face.Contains vertex ∧ vertex ∈ right \ left := by
    intro face member
    obtain ⟨new, old⟩ := Finset.mem_sdiff.mp member
    obtain ⟨allowed, dim⟩ := (mem_faces _ _ _).mp new
    apply exists_new_vertex allowed
    intro h
    exact old ((mem_faces _ _ _).mpr ⟨h, dim⟩)
  choose chosen contains member using witness
  let encode (face : Face n) (h : face ∈ newFaces) := (face.free, chosen face h)
  have bound : newFaces.card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard degree).product
        (newVertices left right)).card := by
    have lands : ∀ face h, encode face h ∈
        ((Finset.univ : Finset (Fin n)).powersetCard degree).product (newVertices left right) := by
      intro face h
      refine Finset.mem_product.mpr ⟨?_, by simpa using member face h⟩
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      exact ((mem_faces _ _ _).mp (Finset.mem_sdiff.mp h).1).2
    apply Finset.card_le_card_of_injective
      (f := fun face => ⟨encode face.val face.property, lands face.val face.property⟩)
    intro left right same
    apply Subtype.ext
    have coords := congrArg (fun x => x.val.1) same
    have vertices := congrArg (fun x => x.val.2) same
    dsimp [encode] at coords vertices
    exact eq_of_contains_of_free_eq (contains left.val left.property)
      (vertices.symm ▸ contains right.val right.property) coords
  simpa [Finset.card_product, Finset.card_powersetCard] using bound

end Face
end Algebraic.BooleanCube
