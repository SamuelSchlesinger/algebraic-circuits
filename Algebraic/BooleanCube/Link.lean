import Algebraic.BooleanCube.Star
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Links as abstract simplicial complexes

This module connects the cubical link to Mathlib's abstract simplicial
complexes, and develops exact face birth times and minimal missing faces.
The empty face is retained by `link` and omitted by Mathlib's convention.
-/

namespace Algebraic.BooleanCube

variable {ι : Type*} [DecidableEq ι]

/-- A cubical vertex link as a Mathlib abstract simplicial complex, omitting the empty face. -/
def linkComplex (vertices : Set (ι → Bool)) (base : ι → Bool) :
    PreAbstractSimplicialComplex ι where
  faces := {directions | directions.Nonempty ∧ directions ∈ link vertices base}
  isRelLowerSet_faces := fun {_} member =>
    ⟨member.1, fun _ included nonempty => ⟨nonempty, link_downward included member.2⟩⟩

/-- The Mathlib link has exactly the nonempty cubical direction faces. -/
@[simp] theorem mem_linkComplex_iff (vertices : Set (ι → Bool)) (base : ι → Bool)
    (directions : Finset ι) :
    directions ∈ linkComplex vertices base ↔ directions.Nonempty ∧ directions ∈ link vertices base :=
  Iff.rfl

/-- Increasing a circuit budget gives an inclusion of Mathlib link complexes. -/
theorem linkComplex_mono {left right : Set (ι → Bool)} (included : left ⊆ right)
    (base : ι → Bool) : linkComplex left base ≤ linkComplex right base :=
  fun _ member => ⟨member.1, link_mono included base member.2⟩

/-- Every missing face contains a minimal missing face. -/
theorem exists_minimalMissing_subset (vertices : Set (ι → Bool)) (base : ι → Bool)
    (directions : Finset ι) (missing : directions ∉ link vertices base) :
    ∃ subset ⊆ directions, MinimalMissing vertices base subset := by
  classical
  induction directions using Finset.strongInductionOn with
  | _ directions ih =>
    by_cases proper : ∀ subset ⊂ directions, subset ∈ link vertices base
    · exact ⟨directions, Finset.Subset.refl _, missing, proper⟩
    · push Not at proper
      obtain ⟨subset, smaller, absent⟩ := proper
      obtain ⟨part, included, minimal⟩ := ih subset smaller absent
      exact ⟨part, included.trans smaller.subset, minimal⟩

/-- A minimal missing face is born exactly when its unique hard corner becomes admitted. -/
theorem faceBirth_eq_of_minimalMissing (cost : (ι → Bool) → Nat) (base : ι → Bool)
    {budget : Nat} {directions : Finset ι}
    (missing : MinimalMissing {vertex | cost vertex ≤ budget} base directions) :
    faceBirth cost base directions = cost (corner base directions) := by
  obtain ⟨hard, proper⟩ := (minimalMissing_sublevel_iff cost base budget directions).mp missing
  apply Nat.le_antisymm ?_ (cost_corner_le_faceBirth cost base (Finset.Subset.refl _))
  apply Finset.sup_le
  intro subset member
  by_cases equal : subset = directions
  · simp [equal]
  · exact (proper subset (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp member, equal⟩)).trans (Nat.le_of_lt hard)

/-- Minimal missing faces form an antichain under inclusion. -/
theorem minimalMissing_eq_of_subset {vertices : Set (ι → Bool)} {base : ι → Bool}
    {left right : Finset ι} (hl : MinimalMissing vertices base left)
    (hr : MinimalMissing vertices base right) (included : left ⊆ right) : left = right := by
  by_contra different
  exact hl.1 (hr.2 left (Finset.ssubset_iff_subset_ne.mpr ⟨included, different⟩))

/-- An edge is born at the larger of its two endpoint costs. -/
theorem faceBirth_singleton (cost : (ι → Bool) → Nat) (base : ι → Bool) (i : ι) :
    faceBirth cost base {i} = max (cost base) (cost (corner base {i})) := by
  have singleton : ({i} : Finset ι).powerset = {∅, {i}} := by
    ext subset
    simp [Finset.subset_singleton_iff]
  simp [faceBirth, singleton]

/-- A square is born at the largest of its four corner costs. -/
theorem faceBirth_pair (cost : (ι → Bool) → Nat) (base : ι → Bool) (i j : ι) :
    faceBirth cost base {i, j} =
      max (max (cost base) (cost (corner base {i})))
        (max (cost (corner base {j})) (cost (corner base {i, j}))) := by
  have singleton : ({j} : Finset ι).powerset = {∅, {j}} := by
    ext subset
    simp [Finset.subset_singleton_iff]
  simp [faceBirth, Finset.powerset_insert, singleton, max_left_comm, max_assoc]

/-- Adding one flip changes only the selected coordinate of a corner. -/
theorem corner_insert (base : ι → Bool) (directions : Finset ι) (i : ι) :
    corner base (insert i directions) = Function.update (corner base directions) i (!(base i)) := by
  funext j
  by_cases same : j = i <;> simp [corner, same]

/-- A point-update bound also controls how quickly an incident face can grow. -/
theorem faceBirth_insert_le (cost : (ι → Bool) → Nat) (base : ι → Bool) (change : Nat)
    (step : ∀ vertex i value, cost (Function.update vertex i value) ≤ cost vertex + change)
    (directions : Finset ι) (i : ι) :
    faceBirth cost base (insert i directions) ≤ faceBirth cost base directions + change := by
  apply Finset.sup_le
  intro subset member
  have included := Finset.mem_powerset.mp member
  by_cases present : i ∈ subset
  · have smaller : subset.erase i ⊆ directions := by
      intro j hj
      obtain ⟨different, inside⟩ := Finset.mem_erase.mp hj
      exact (Finset.mem_insert.mp (included inside)).resolve_left different
    have updateBound := step (corner base (subset.erase i)) i (!(base i))
    rw [← corner_insert, Finset.insert_erase present] at updateBound
    exact updateBound.trans (Nat.add_le_add_right (cost_corner_le_faceBirth cost base smaller) change)
  · have smaller : subset ⊆ directions := by
      intro j hj
      rcases Finset.mem_insert.mp (included hj) with equal | inside
      · exact False.elim (present (equal ▸ hj))
      · exact inside
    exact (cost_corner_le_faceBirth cost base smaller).trans (Nat.le_add_right _ _)

/-- Uniform update costs guarantee a full simplex skeleton in every vertex link. -/
theorem faceBirth_le_card (cost : (ι → Bool) → Nat) (base : ι → Bool) (change : Nat)
    (step : ∀ vertex i value, cost (Function.update vertex i value) ≤ cost vertex + change)
    (directions : Finset ι) :
    faceBirth cost base directions ≤ cost base + change * directions.card := by
  induction directions using Finset.induction_on with
  | empty => simp
  | @insert i directions absent ih =>
    have next := faceBirth_insert_le cost base change step directions i
    rw [Finset.card_insert_of_notMem absent, Nat.mul_add] at *
    omega

end Algebraic.BooleanCube
