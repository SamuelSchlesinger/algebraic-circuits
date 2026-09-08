import Algebraic.Basis.DeMorgan.Star

/-!
# Birth times and hard exception patterns around constants

Birth time measures the largest complexity of any exception pattern inside
a support. It is monotone, has a uniform insertion bound, and differs by at
most one gate between the two constant centers. Nonadjacent pairs are born
exactly at the complexity of their two-exception corner.
-/

namespace Algebraic.DeMorgan

/-- The circuit budget needed to realize every exception pattern on a chosen input set. -/
noncomputable def constantFaceBirth (n : Nat) (value : Bool) (directions : Finset (Fin n → Bool)) : Nat :=
  BooleanCube.faceBirth complexity (fun _ => value) directions

/-- A support forms a face around the constant precisely when its full exception budget is available. -/
theorem mem_constantLink_iff_birth_le (n budget : Nat) (value : Bool)
    (directions : Finset (Fin n → Bool)) :
    directions ∈ constantLink n budget value ↔ constantFaceBirth n value directions ≤ budget :=
  BooleanCube.mem_link_sublevel_iff _ _ _ _

/-- Every exception pattern is bounded by its enclosing face's birth time. -/
theorem complexity_corner_le_constantFaceBirth (value : Bool)
    {subset directions : Finset (Fin n → Bool)} (included : subset ⊆ directions) :
    complexity (BooleanCube.corner (fun _ => value) subset) ≤ constantFaceBirth n value directions :=
  BooleanCube.cost_corner_le_faceBirth _ _ included

/-- Adding allowed exception locations can only increase the required budget. -/
theorem constantFaceBirth_mono (value : Bool) {left right : Finset (Fin n → Bool)}
    (included : left ⊆ right) : constantFaceBirth n value left ≤ constantFaceBirth n value right :=
  BooleanCube.faceBirth_mono _ _ included

/-- Adding one exception location raises the full-face budget by at most `2*n`. -/
theorem constantFaceBirth_insert_le (value : Bool) (directions : Finset (Fin n → Bool))
    (point : Fin n → Bool) :
    constantFaceBirth n value (insert point directions) ≤ constantFaceBirth n value directions + 2 * n :=
  BooleanCube.faceBirth_insert_le complexity _ (2 * n) complexity_update_le directions point

/-- Sparse exception families give a guaranteed simplex skeleton in each constant link. -/
theorem constantFaceBirth_le_card (value : Bool) (directions : Finset (Fin n → Bool)) :
    constantFaceBirth n value directions ≤ 1 + 2 * n * directions.card :=
  (BooleanCube.faceBirth_le_card complexity (fun _ => value) (2 * n) complexity_update_le directions).trans
    (Nat.add_le_add_right (complexity_constant_le n value) _)

/-- Every support of at most `r` inputs forms a face by budget `1+2*n*r`. -/
theorem mem_constantLink_of_card_le (value : Bool) {directions : Finset (Fin n → Bool)}
    {r : Nat} (small : directions.card ≤ r) : directions ∈ constantLink n (1 + 2 * n * r) value := by
  apply (mem_constantLink_iff_birth_le _ _ _ _).mpr
  exact (constantFaceBirth_le_card value directions).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ small) _)

/-- Complementing the center changes any face's birth time by at most one gate in one direction. -/
theorem constantFaceBirth_complement_le (value : Bool) (directions : Finset (Fin n → Bool)) :
    constantFaceBirth n (!value) directions ≤ constantFaceBirth n value directions + 1 := by
  apply Finset.sup_le
  intro subset member
  have identity : BooleanCube.corner (fun _ => !value) subset =
      fun input => !(BooleanCube.corner (fun _ => value) subset input) := by
    funext input
    by_cases present : input ∈ subset <;> simp [BooleanCube.corner, present]
  rw [identity]
  exact (complexity_not_le _).trans (Nat.add_le_add_right
    (complexity_corner_le_constantFaceBirth value (Finset.mem_powerset.mp member)) 1)

/-- The two constant-link filtrations are interleaved by a one-gate budget shift. -/
theorem constantLink_subset_complement (n budget : Nat) (value : Bool) :
    constantLink n budget value ⊆ constantLink n (budget + 1) (!value) := by
  intro directions member
  apply (mem_constantLink_iff_birth_le _ _ _ _).mpr
  exact (constantFaceBirth_complement_le value directions).trans
    (Nat.add_le_add_right ((mem_constantLink_iff_birth_le _ _ _ _).mp member) 1)

/-- The full truth-table face appears precisely at worst-case circuit complexity. -/
theorem constantFaceBirth_univ (n : Nat) (value : Bool) :
    constantFaceBirth n value Finset.univ = maximumComplexity n :=
  BooleanCube.faceBirth_univ _ _

/-- Every missing face contains an irredundant hard exception pattern. -/
theorem exists_minimal_hard_support (n budget : Nat) (value : Bool)
    (directions : Finset (Fin n → Bool)) (missing : directions ∉ constantLink n budget value) :
    ∃ subset ⊆ directions,
      budget < complexity (BooleanCube.corner (fun _ => value) subset) ∧
        ∀ part ⊂ subset, complexity (BooleanCube.corner (fun _ => value) part) ≤ budget := by
  obtain ⟨subset, included, minimal⟩ := BooleanCube.exists_minimalMissing_subset _ _ directions missing
  exact ⟨subset, included, (BooleanCube.minimalMissing_sublevel_iff _ _ _ _).mp minimal⟩

/-- A nonadjacent pair is born exactly when its two-exception function becomes cheap. -/
theorem constantFaceBirth_pair_eq (positive : 0 < n) (value : Bool)
    (left right : Fin n → Bool) (far : 1 < hammingDist left right) :
    constantFaceBirth n value {left, right} = complexity (pairIndicator left right (!value)) := by
  have different : left ≠ right := by intro equal; simp [equal] at far
  have notAdjacent : ¬BooleanCube.graph.Adj left right := by
    change hammingDist left right ≠ 1
    omega
  have minimal := (pair_minimalMissing_iff positive value left right different).mpr notAdjacent
  have equal := BooleanCube.faceBirth_eq_of_minimalMissing complexity (fun _ => value) minimal
  have identity : BooleanCube.corner (fun _ => value) {left, right} = pairIndicator left right (!value) := by
    funext input
    simp [BooleanCube.corner, pairIndicator]
  exact equal.trans (congrArg complexity identity)

/-- The lower half of the input cube supplies a large face around zero at a smaller-width budget. -/
theorem input_halfcube_mem_zero_link (n : Nat) :
    (Finset.univ.filter (fun input : Fin (n + 1) → Bool => input 0 = true)) ∈
      constantLink (n + 1) (maximumComplexity n + 1) false := by
  have member := (input_mem_both_constant_stars n).1
  change BooleanCube.directionsTo (fun _ => false) (fun input : Fin (n + 1) → Bool => input 0) ∈
    constantLink (n + 1) (maximumComplexity n + 1) false at member
  simpa [BooleanCube.directionsTo] using member

/-- The complementary input halfcube supplies the corresponding large face around one. -/
theorem input_halfcube_mem_one_link (n : Nat) :
    (Finset.univ.filter (fun input : Fin (n + 1) → Bool => input 0 = false)) ∈
      constantLink (n + 1) (maximumComplexity n + 1) true := by
  have member := (input_mem_both_constant_stars n).2
  change BooleanCube.directionsTo (fun _ => true) (fun input : Fin (n + 1) → Bool => input 0) ∈
    constantLink (n + 1) (maximumComplexity n + 1) true at member
  simpa [BooleanCube.directionsTo] using member

end Algebraic.DeMorgan
