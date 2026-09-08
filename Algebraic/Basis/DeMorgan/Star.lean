import Algebraic.Basis.DeMorgan.PairIndicator
import Algebraic.BooleanCube.Link
import Algebraic.BooleanCube.StarRealization

/-!
# The exact constant links at the input-width budget

For positive input width `n`, the cubical link of either constant at budget
`n` is exactly the graph of the `n`-dimensional input cube. All singleton
directions are present, pairs are present exactly at adjacent inputs, and
there are no larger faces. The result counts all native De Morgan gates.
-/

namespace Algebraic.DeMorgan

/-- The cubical link of a constant truth table in a native circuit-complexity sublevel. -/
def constantLink (n budget : Nat) (value : Bool) : Set (Finset (Fin n → Bool)) :=
  BooleanCube.link {function | complexity function ≤ budget} (fun _ => value)

/-- The constant link as a Mathlib abstract simplicial complex. -/
def constantLinkComplex (n budget : Nat) (value : Bool) :
    PreAbstractSimplicialComplex (Fin n → Bool) :=
  BooleanCube.linkComplex {function | complexity function ≤ budget} (fun _ => value)

/-- The graph formed by the one-dimensional simplices of a constant link. -/
def constantLinkGraph (n budget : Nat) (value : Bool) : SimpleGraph (Fin n → Bool) where
  Adj left right := left ≠ right ∧ {left, right} ∈ constantLink n budget value
  symm := ⟨by intro left right member; simpa [ne_comm, Finset.pair_comm] using member⟩
  loopless := ⟨by intro vertex member; exact member.1 rfl⟩

/-- Each constant's geometric star is contractible as soon as its one-gate center is admitted. -/
theorem constantStar_contractible (n : Nat) (value : Bool) (admitted : 1 ≤ budget) :
    ContractibleSpace (BooleanCube.closedStar
      {function : ScalarFunction Bool n | complexity function ≤ budget} (fun _ => value)) :=
  BooleanCube.closedStar_contractible _ _ ((complexity_constant_le n value).trans admitted)

private theorem corner_constant_singleton (value : Bool) (point : Fin n → Bool) :
    BooleanCube.corner (fun _ => value) {point} =
      fun input => if input = point then !value else value := by
  funext input
  simp [BooleanCube.corner]

private theorem corner_constant_pair (value : Bool) (left right : Fin n → Bool) :
    BooleanCube.corner (fun _ => value) {left, right} = pairIndicator left right (!value) := by
  funext input
  simp [BooleanCube.corner, pairIndicator]

/-- Every direction away from either constant exists at budget `n`. -/
theorem singleton_mem_constantLink (positive : 0 < n) (value : Bool) (point : Fin n → Bool) :
    {point} ∈ constantLink n n value := by
  apply (BooleanCube.mem_link_sublevel_iff _ _ _ _).mpr
  rw [BooleanCube.faceBirth_singleton, corner_constant_singleton]
  have constant := complexity_constant_le n value
  have changed := complexity_point_indicator_le positive point (!value)
  simp only [Bool.not_not] at changed
  exact max_le (by omega) changed

/-- Distinct directions span a square at budget `n` exactly when the corresponding inputs are adjacent. -/
theorem pair_mem_constantLink_iff (positive : 0 < n) (value : Bool)
    (left right : Fin n → Bool) (different : left ≠ right) :
    {left, right} ∈ constantLink n n value ↔ BooleanCube.graph.Adj left right := by
  constructor
  · intro member
    have bounded := member {left, right} (Finset.Subset.refl _)
    rw [corner_constant_pair] at bounded
    exact (complexity_pairIndicator_le_iff positive left right (!value) different).mp bounded
  · intro adjacent
    apply (BooleanCube.mem_link_sublevel_iff _ _ _ _).mpr
    rw [BooleanCube.faceBirth_pair, corner_constant_pair]
    have leftBound := (BooleanCube.mem_link_sublevel_iff _ _ _ _).mp
      (singleton_mem_constantLink positive value left)
    rw [BooleanCube.faceBirth_singleton] at leftBound
    have rightBound := BooleanCube.cost_corner_le_faceBirth complexity (fun _ => value)
      (Finset.Subset.refl ({right} : Finset (Fin n → Bool)))
    have rightBirth := (BooleanCube.mem_link_sublevel_iff _ _ _ _).mp
      (singleton_mem_constantLink positive value right)
    exact max_le leftBound (max_le (rightBound.trans rightBirth)
      (complexity_pairIndicator_le_of_adjacent positive left right (!value) adjacent))

/-- At budget `n`, each constant link is exactly the input-cube graph. -/
theorem constantLinkGraph_eq_cube (positive : 0 < n) (value : Bool) :
    constantLinkGraph n n value = BooleanCube.graph := by
  ext left right
  change (left ≠ right ∧ {left, right} ∈ constantLink n n value) ↔ _
  constructor
  · rintro ⟨different, member⟩
    exact (pair_mem_constantLink_iff positive value left right different).mp member
  · intro adjacent
    have different : left ≠ right := by
      intro equal
      subst right
      exact BooleanCube.graph.irrefl adjacent
    exact ⟨different, (pair_mem_constantLink_iff positive value left right different).mpr adjacent⟩

/-- Every direction face at budget `n` has at most two coordinates. -/
theorem card_le_two_of_mem_constantLink (positive : 0 < n) (value : Bool)
    {directions : Finset (Fin n → Bool)} (member : directions ∈ constantLink n n value) :
    directions.card ≤ 2 := by
  apply BooleanCube.card_le_two_of_pairwise_adjacent
  intro left hl right hr different
  apply (pair_mem_constantLink_iff positive value left right different).mp
  have included : ({left, right} : Finset (Fin n → Bool)) ⊆ directions := by
    intro point present
    rcases Finset.mem_insert.mp present with rfl | present
    · exact hl
    · have equal := Finset.mem_singleton.mp present
      simpa [equal] using hr
  exact BooleanCube.link_downward included member

/-- The complete constant link consists of the empty face, single directions, and adjacent pairs. -/
theorem mem_constantLink_iff (positive : 0 < n) (value : Bool) (directions : Finset (Fin n → Bool)) :
    directions ∈ constantLink n n value ↔
      directions = ∅ ∨ (∃ point, directions = {point}) ∨
        ∃ left right, BooleanCube.graph.Adj left right ∧ directions = {left, right} := by
  constructor
  · intro member
    have bound := card_le_two_of_mem_constantLink positive value member
    by_cases empty : directions.card = 0
    · exact Or.inl (Finset.card_eq_zero.mp empty)
    by_cases one : directions.card = 1
    · exact Or.inr (Or.inl (Finset.card_eq_one.mp one))
    obtain ⟨left, right, different, equal⟩ := Finset.card_eq_two.mp (show directions.card = 2 by omega)
    exact Or.inr (Or.inr ⟨left, right,
      (pair_mem_constantLink_iff positive value left right different).mp (equal ▸ member), equal⟩)
  · rintro (rfl | ⟨point, rfl⟩ | ⟨left, right, adjacent, rfl⟩)
    · apply (BooleanCube.empty_mem_link_iff _ _).mpr
      exact (complexity_constant_le n value).trans positive
    · exact singleton_mem_constantLink positive value point
    · have different : left ≠ right := by
        intro equal
        subst right
        exact BooleanCube.graph.irrefl adjacent
      exact (pair_mem_constantLink_iff positive value left right different).mpr adjacent

/-- Any three distinct input directions form a missing face at the input-width budget. -/
theorem not_mem_constantLink_of_two_lt_card (positive : 0 < n) (value : Bool)
    {directions : Finset (Fin n → Bool)} (large : 2 < directions.card) :
    directions ∉ constantLink n n value := by
  intro member
  have bound := card_le_two_of_mem_constantLink positive value member
  omega

/-- A pair of nonadjacent exceptions is a minimal missing face at budget `n`. -/
theorem pair_minimalMissing_iff (positive : 0 < n) (value : Bool)
    (left right : Fin n → Bool) (different : left ≠ right) :
    BooleanCube.MinimalMissing {f | complexity f ≤ n} (fun _ => value) {left, right} ↔
      ¬BooleanCube.graph.Adj left right := by
  constructor
  · intro missing adjacent
    exact missing.1 ((pair_mem_constantLink_iff positive value left right different).mpr adjacent)
  · intro notAdjacent
    refine ⟨fun member => notAdjacent ((pair_mem_constantLink_iff positive value left right different).mp member), ?_⟩
    intro subset smaller
    have small : subset.card ≤ 1 := by
      have strict := Finset.card_lt_card smaller
      have pairCard : ({left, right} : Finset (Fin n → Bool)).card = 2 := by simp [different]
      omega
    by_cases empty : subset.card = 0
    · rw [Finset.card_eq_zero.mp empty]
      exact (BooleanCube.empty_mem_link_iff _ _).mpr ((complexity_constant_le n value).trans positive)
    · obtain ⟨point, rfl⟩ := Finset.card_eq_one.mp (show subset.card = 1 by omega)
      exact singleton_mem_constantLink positive value point

end Algebraic.DeMorgan
