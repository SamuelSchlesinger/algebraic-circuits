import Algebraic.BooleanCube.Face
import Algebraic.BooleanCube.Cubical

/-!
# The finite face model realizes the geometric cubical sublevel

The faces used by the finite chain complex are exactly the closed faces
whose union defines `BooleanCube.cubical`. This is a geometric comparison;
it does not assert a singular-to-cubical homology comparison theorem.
-/

namespace Algebraic.BooleanCube.Face

/-- The closed geometric face specified by fixed and free coordinates. -/
def realization (face : Face n) : Set (Fin n → Real) :=
  {point | (∀ i, 0 ≤ point i ∧ point i ≤ 1) ∧
    ∀ i bit, face i = some bit → point i = if bit then 1 else 0}

/-- An admitted closed face lies in the vertex-induced geometric cubical complex. -/
theorem realization_subset_cubical {vertices : Set (Fin n → Bool)} {face : Face n}
    (allowed : face.Allowed vertices) : face.realization ⊆ cubical vertices := by
  intro point member
  refine ⟨member.1, ?_⟩
  intro vertex compatible
  apply allowed vertex
  intro i
  cases h : face i with
  | none => exact Or.inl rfl
  | some bit =>
      right
      have equal := member.2 i bit h
      cases bit
      · have value := (compatible i).1 equal
        simp [value]
      · have value := (compatible i).2 equal
        simp [value]

/-- The finite admitted-face model realizes precisely the previously defined cubical complex. -/
theorem mem_cubical_iff_exists_face (vertices : Set (Fin n → Bool)) (point : Fin n → Real) :
    point ∈ cubical vertices ↔ ∃ face : Face n, face.Allowed vertices ∧ point ∈ face.realization := by
  classical
  constructor
  · intro member
    let face : Face n := fun i => if point i = 0 then some false
      else if point i = 1 then some true else none
    refine ⟨face, ?_, member.1, ?_⟩
    · intro vertex contained
      apply member.2 vertex
      intro i
      constructor
      · intro zero
        have h := contained i
        have value : false = vertex i := by simpa [face, zero] using h
        exact value.symm
      · intro one
        have h := contained i
        have value : true = vertex i := by simpa [face, one] using h
        exact value.symm
    · intro i bit equal
      dsimp [face] at equal
      split_ifs at equal with zero one
      · cases equal
        exact zero
      · cases equal
        exact one
  · rintro ⟨face, allowed, member⟩
    exact realization_subset_cubical allowed member

end Algebraic.BooleanCube.Face
