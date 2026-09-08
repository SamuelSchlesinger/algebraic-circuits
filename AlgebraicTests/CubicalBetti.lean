import Algebraic.CircuitGeometry

/-!
# Regression certificates for finite cubical homology

Besides the public shell theorem, the tests include the six-cycle obtained
by deleting opposite vertices of a three-cube. An explicit nonboundary
cycle ensures the Betti invariant detects actual holes.
-/

namespace AlgebraicTests.CubicalBetti

open Algebraic Algebraic.BooleanCube

private def hexagon : Set (Fin 3 → Bool) :=
  {vertex | vertex ≠ (fun _ => false) ∧ vertex ≠ (fun _ => true)}

private noncomputable def hexCycle : Chains ℚ 3 :=
  Finsupp.single ![some true, none, some false] 1 -
  Finsupp.single ![none, some true, some false] 1 +
  Finsupp.single ![some false, some true, none] 1 -
  Finsupp.single ![some false, none, some true] 1 +
  Finsupp.single ![none, some false, some true] 1 -
  Finsupp.single ![some true, some false, none] 1

private theorem hexCycle_mem : hexCycle ∈ Chains.level ℚ hexagon 1 := by
  have basis (face : Face 3) (allowed : face.Allowed hexagon ∧ face.dimension = 1) :
      Finsupp.single face (1 : ℚ) ∈ Chains.level ℚ hexagon 1 :=
    Finsupp.single_mem_supported ℚ 1 allowed
  unfold hexCycle
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · apply Submodule.sub_mem
      · apply Submodule.add_mem
        · apply Submodule.sub_mem
          · apply basis
            unfold Face.Allowed Face.Contains hexagon
            decide
          · apply basis
            unfold Face.Allowed Face.Contains hexagon
            decide
        · apply basis
          unfold Face.Allowed Face.Contains hexagon
          decide
      · apply basis
        unfold Face.Allowed Face.Contains hexagon
        decide
    · apply basis
      unfold Face.Allowed Face.Contains hexagon
      decide
  · apply basis
    unfold Face.Allowed Face.Contains hexagon
    decide

private theorem hexCycle_closed : Chains.boundary ℚ 3 hexCycle = 0 := by
  simp [hexCycle, Chains.boundary, Chains.push_single, Face.cons,
    Finsupp.linearCombination_single, map_sub, map_add]

private theorem hexagon_no_squares : ∀ face : Face 3,
    face.dimension = 2 → ¬face.Allowed hexagon := by
  unfold Face.Allowed Face.Contains hexagon
  decide

private theorem hexagon_boundaries_zero : Chains.boundaries ℚ hexagon 1 = ⊥ := by
  have empty : Chains.level ℚ hexagon 2 = ⊥ := by
    apply le_antisymm _ bot_le
    intro chain member
    apply Finsupp.ext
    intro face
    by_contra nonzero
    have allowed := member (Finsupp.mem_support_iff.mpr nonzero)
    exact hexagon_no_squares face allowed.2 allowed.1
  simp [Chains.boundaries, empty]

/-- The six-cycle has nonzero first homology over the rationals. -/
example : 0 < CubicalHomology.betti ℚ hexagon 1 := by
  apply CubicalHomology.betti_pos_of_cycle ℚ hexagon 1 hexCycle
    ⟨hexCycle_mem, hexCycle_closed⟩
  rw [hexagon_boundaries_zero]
  intro zero
  have coefficient := congrArg (fun chain : Chains ℚ 3 => chain ![some true, none, some false]) zero
  norm_num [hexCycle, Finsupp.single_apply] at coefficient
  split_ifs at coefficient <;> simp_all

/-- Every positive-degree Betti number of the full cube vanishes. -/
example (K : Type*) [Field K] (n degree : Nat) (positive : 0 < degree) :
    CubicalHomology.betti K (Set.univ : Set (Fin n → Bool)) degree = 0 := by
  have bound := CubicalHomology.betti_le_card_new_faces K (n := n) Set.univ Set.univ degree positive
    (fun _ h => h) (fun _ _ _ => Set.mem_univ _)
  simpa using bound

/-- No positive-dimensional chain exists in the zero-coordinate cube. -/
example (K : Type*) [Field K] (degree : Nat) (positive : 0 < degree) :
    CubicalHomology.betti K (Set.univ : Set (Fin 0 → Bool)) degree = 0 := by
  have bound := CubicalHomology.betti_le_card_new_faces K (n := 0) Set.univ Set.univ degree positive
    (fun _ h => h) (fun _ _ _ => Set.mem_univ _)
  simpa using bound

/-- The shell theorem is available over every field, with the exact binomial coefficient. -/
example (K : Type*) [Field K] (budget degree : Nat) (positive : 0 < degree) :
    DeMorgan.cubicalBetti K 4 budget degree ≤
      (16 : Nat).choose (degree + 1) * (DeMorgan.complexityShell 4 budget).card := by
  simpa only [show (2 : Nat) ^ 4 = 16 by decide] using
    DeMorgan.cubicalBetti_le_choose_mul_shell K (n := 4) (by decide) budget degree positive

/-- The finite faces and the geometric cubical sublevel describe the same set of points. -/
example (vertices : Set (Fin 3 → Bool)) (point : Fin 3 → Real) :
    point ∈ cubical vertices ↔ ∃ face : Face 3, face.Allowed vertices ∧ point ∈ face.realization :=
  Face.mem_cubical_iff_exists_face vertices point

end AlgebraicTests.CubicalBetti
