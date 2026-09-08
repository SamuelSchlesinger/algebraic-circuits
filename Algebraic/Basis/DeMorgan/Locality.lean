import Algebraic.Basis.DeMorgan.Witness
import Algebraic.BooleanCube.Locality

/-!
# A locality obstruction for cubical lower-bound certificates

If a degree-`k` cochain's face-boundary evaluations are unchanged when fixed
coordinates outside `Q` are zeroed, it cannot detect a nonbounding cycle at
budget `s >= 1 + 2*n*(|Q|+k+1)`. This is a restriction on that precise
locality condition, not on arbitrary cochains or all topological methods.
-/

namespace Algebraic.DeMorgan

/-- Sparse truth tables have circuits obtained by updating the zero function. -/
theorem orderedComplexity_le_true_support (vector : Fin (2 ^ n) → Bool) :
    orderedComplexity n vector ≤
      1 + 2 * n * (Finset.univ.filter (fun i => vector i = true)).card := by
  classical
  have distance : hammingDist (fun _ : Fin n → Bool => false) (truthTableEquiv n vector) ≤
      (Finset.univ.filter (fun i => vector i = true)).card := by
    unfold hammingDist
    apply Finset.card_le_card_of_injective
      (f := fun input => ⟨inputIndex n input.val, ?_⟩)
    · intro left right equal
      exact Subtype.ext ((inputIndex_bijective n).injective (congrArg Subtype.val equal))
    · have h := (Finset.mem_filter.mp input.property).2
      simp only [truthTableEquiv] at h
      simpa using h
  have upper := complexity_le_add_hammingDist (fun _ : Fin n → Bool => false)
    (truthTableEquiv n vector)
  exact upper.trans (Nat.add_le_add (complexity_constant_le n false)
    (Nat.mul_le_mul_left (2 * n) distance))

/-- Zeroing unchosen fixed coordinates makes every vertex uniformly cheap. -/
theorem orderedComplexity_le_of_contains_truncate (coordinates : Finset (Fin (2 ^ n)))
    (face : BooleanCube.Face (2 ^ n)) {vertex : Fin (2 ^ n) → Bool}
    (contained : (face.truncate coordinates).Contains vertex) :
    orderedComplexity n vertex ≤ 1 + 2 * n * (coordinates.card + face.dimension) :=
  (orderedComplexity_le_true_support vertex).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left (2 * n)
      (BooleanCube.Face.card_true_support_le_of_contains_truncate coordinates face contained)) 1)

/-- A truncation-invariant boundary certificate vanishes on all positive-degree cycles
once its sparse replacement faces fit the circuit budget. -/
theorem cochain_eq_zero_of_truncate_invariant (R : Type*) [CommRing R]
    (budget degree : Nat) (positive : 0 < degree) (coordinates : Finset (Fin (2 ^ n)))
    (large : 1 + 2 * n * (coordinates.card + degree + 1) ≤ budget)
    (cochain : BooleanCube.Chains R (2 ^ n) →ₗ[R] R)
    (vanishes : ∀ face : BooleanCube.Face (2 ^ n),
      face.Allowed {vector | orderedComplexity n vector ≤ budget} →
      face.dimension = degree + 1 →
      cochain (BooleanCube.Chains.boundary R _ (Finsupp.single face 1)) = 0)
    (locality : ∀ face : BooleanCube.Face (2 ^ n), face.dimension = degree + 1 →
      cochain (BooleanCube.Chains.boundary R _ (Finsupp.single (face.truncate coordinates) 1)) =
        cochain (BooleanCube.Chains.boundary R _ (Finsupp.single face 1)))
    {chain : BooleanCube.Chains R (2 ^ n)}
    (closed : chain ∈ BooleanCube.Chains.cycles R Set.univ degree) :
    cochain chain = 0 := by
  apply BooleanCube.Chains.cochain_eq_zero_of_face_replacement R
    {vector | orderedComplexity n vector ≤ budget} degree positive cochain vanishes _ closed
  intro face dim
  refine ⟨face.truncate coordinates, ?_, by simpa using dim, locality face dim⟩
  intro vertex contained
  have upper := orderedComplexity_le_of_contains_truncate coordinates face contained
  rw [dim] at upper
  exact upper.trans (by simpa [Nat.add_assoc] using large)

/-- Detecting a cycle forces a budget below the locality threshold. -/
theorem budget_lt_of_local_cochain (R : Type*) [CommRing R]
    (budget degree : Nat) (positive : 0 < degree) (coordinates : Finset (Fin (2 ^ n)))
    (cochain : BooleanCube.Chains R (2 ^ n) →ₗ[R] R)
    (vanishes : ∀ face : BooleanCube.Face (2 ^ n),
      face.Allowed {vector | orderedComplexity n vector ≤ budget} →
      face.dimension = degree + 1 →
      cochain (BooleanCube.Chains.boundary R _ (Finsupp.single face 1)) = 0)
    (locality : ∀ face : BooleanCube.Face (2 ^ n), face.dimension = degree + 1 →
      cochain (BooleanCube.Chains.boundary R _ (Finsupp.single (face.truncate coordinates) 1)) =
        cochain (BooleanCube.Chains.boundary R _ (Finsupp.single face 1)))
    {chain : BooleanCube.Chains R (2 ^ n)}
    (closed : chain ∈ BooleanCube.Chains.cycles R Set.univ degree)
    (detected : cochain chain ≠ 0) :
    budget < 1 + 2 * n * (coordinates.card + degree + 1) := by
  by_contra! large
  exact detected (cochain_eq_zero_of_truncate_invariant R budget degree positive coordinates
    large cochain vanishes locality closed)

end Algebraic.DeMorgan
