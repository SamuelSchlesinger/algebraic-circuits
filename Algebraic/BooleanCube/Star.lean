import Algebraic.BooleanCube.FaceRealization
import Algebraic.BooleanCube.Boundary

/-!+# Cubical stars, links, and face birth times

The link at a Boolean vertex records sets of coordinates that may vary
independently while every other coordinate remains fixed at that vertex.
Its face birth time is the maximum cost of all corners, not just the
opposite corner. These definitions apply to arbitrary costs on a finite cube.
-/

namespace Algebraic.BooleanCube

variable {ι : Type*} [DecidableEq ι]

/-- The corner obtained by flipping precisely the selected coordinates. -/
def corner (base : ι → Bool) (directions : Finset ι) : ι → Bool :=
  fun i => if i ∈ directions then !(base i) else base i

/-- No flips leave the base vertex unchanged. -/
@[simp] theorem corner_empty (base : ι → Bool) : corner base ∅ = base := by
  funext i
  simp [corner]

/-- Distinct sets of flipped coordinates give distinct corners. -/
theorem corner_injective (base : ι → Bool) : Function.Injective (corner base) := by
  intro left right equal
  apply Finset.ext
  intro i
  have h := congrFun equal i
  by_cases hl : i ∈ left <;> by_cases hr : i ∈ right <;>
    cases value : base i <;> simp_all [corner]

/-- The cubical link at `base`, including the empty direction set when the base is admitted. -/
def link (vertices : Set (ι → Bool)) (base : ι → Bool) : Set (Finset ι) :=
  {directions | ∀ subset ⊆ directions, corner base subset ∈ vertices}

/-- A link is closed under taking subsets of its direction sets. -/
theorem link_downward {vertices : Set (ι → Bool)} {base : ι → Bool}
    {left right : Finset ι} (included : left ⊆ right) (member : right ∈ link vertices base) :
    left ∈ link vertices base :=
  fun subset small => member subset (small.trans included)

/-- Enlarging the admitted vertex set enlarges every link. -/
theorem link_mono {left right : Set (ι → Bool)} (included : left ⊆ right)
    (base : ι → Bool) : link left base ⊆ link right base :=
  fun _ member subset small => included (member subset small)

/-- The empty face is admitted precisely when its base vertex is admitted. -/
@[simp] theorem empty_mem_link_iff (vertices : Set (ι → Bool)) (base : ι → Bool) :
    ∅ ∈ link vertices base ↔ base ∈ vertices := by
  constructor
  · intro member
    simpa using member ∅ (Finset.Subset.refl _)
  · intro member subset small
    simpa [Finset.subset_empty.mp small] using member

/-- The exact budget at which a face incident to the base appears. -/
def faceBirth (cost : (ι → Bool) → Nat) (base : ι → Bool) (directions : Finset ι) : Nat :=
  directions.powerset.sup (fun subset => cost (corner base subset))

/-- Every corner's cost is bounded by its face's birth time. -/
theorem cost_corner_le_faceBirth (cost : (ι → Bool) → Nat) (base : ι → Bool)
    {subset directions : Finset ι} (included : subset ⊆ directions) :
    cost (corner base subset) ≤ faceBirth cost base directions :=
  Finset.le_sup (f := fun part => cost (corner base part)) (Finset.mem_powerset.mpr included)

/-- A face is present exactly at and above its birth time. -/
theorem mem_link_sublevel_iff (cost : (ι → Bool) → Nat) (base : ι → Bool)
    (budget : Nat) (directions : Finset ι) :
    directions ∈ link {vertex | cost vertex ≤ budget} base ↔
      faceBirth cost base directions ≤ budget := by
  simp [link, faceBirth, Finset.sup_le_iff]

/-- Birth times are monotone in the set of directions. -/
theorem faceBirth_mono (cost : (ι → Bool) → Nat) (base : ι → Bool)
    {left right : Finset ι} (included : left ⊆ right) :
    faceBirth cost base left ≤ faceBirth cost base right := by
  apply Finset.sup_le
  intro subset member
  exact cost_corner_le_faceBirth cost base ((Finset.mem_powerset.mp member).trans included)

/-- The base is the only corner of the empty face. -/
@[simp] theorem faceBirth_empty (cost : (ι → Bool) → Nat) (base : ι → Bool) :
    faceBirth cost base ∅ = cost base := by
  simp [faceBirth]

/-- A minimal missing face is absent but all its proper faces are present. -/
def MinimalMissing (vertices : Set (ι → Bool)) (base : ι → Bool)
    (directions : Finset ι) : Prop :=
  directions ∉ link vertices base ∧
    ∀ subset ⊂ directions, subset ∈ link vertices base

/-- A minimal missing face has exactly one missing corner: the opposite corner. -/
theorem minimalMissing_iff (vertices : Set (ι → Bool)) (base : ι → Bool)
    (directions : Finset ι) :
    MinimalMissing vertices base directions ↔
      corner base directions ∉ vertices ∧
        ∀ subset ⊂ directions, corner base subset ∈ vertices := by
  constructor
  · rintro ⟨missing, proper⟩
    refine ⟨?_, fun subset small => proper subset small subset (Finset.Subset.refl _)⟩
    intro admitted
    apply missing
    intro subset small
    by_cases equal : subset = directions
    · simpa [equal] using admitted
    · exact proper subset (Finset.ssubset_iff_subset_ne.mpr ⟨small, equal⟩)
        subset (Finset.Subset.refl _)
  · rintro ⟨missing, proper⟩
    refine ⟨fun member => missing (member directions (Finset.Subset.refl _)), ?_⟩
    intro subset small part included
    exact proper part (Finset.ssubset_of_subset_of_ssubset included small)

/-- Minimal missing faces characterize irredundant hard exception patterns. -/
theorem minimalMissing_sublevel_iff (cost : (ι → Bool) → Nat) (base : ι → Bool)
    (budget : Nat) (directions : Finset ι) :
    MinimalMissing {vertex | cost vertex ≤ budget} base directions ↔
      budget < cost (corner base directions) ∧
        ∀ subset ⊂ directions, cost (corner base subset) ≤ budget := by
  simpa using minimalMissing_iff {vertex | cost vertex ≤ budget} base directions

section Finite

variable [Fintype ι]

/-- The unique directions taking one Boolean vertex to another. -/
def directionsTo (base vertex : ι → Bool) : Finset ι :=
  Finset.univ.filter (fun i => vertex i ≠ base i)

/-- Flipping the differing coordinates recovers the given vertex. -/
@[simp] theorem corner_directionsTo (base vertex : ι → Bool) :
    corner base (directionsTo base vertex) = vertex := by
  funext i
  cases hb : base i <;> cases hv : vertex i <;> simp [corner, directionsTo, hb, hv]

/-- Taking the directions of a corner recovers the original direction set. -/
@[simp] theorem directionsTo_corner (base : ι → Bool) (directions : Finset ι) :
    directionsTo base (corner base directions) = directions :=
  corner_injective base (corner_directionsTo base _)

omit [DecidableEq ι] in
/-- Containment of direction sets is containment in the Boolean interval from the base. -/
theorem directionsTo_subset_iff (base left right : ι → Bool) :
    directionsTo base left ⊆ directionsTo base right ↔
      ∀ i, left i = base i ∨ left i = right i := by
  constructor
  · intro included i
    by_cases same : left i = base i
    · exact Or.inl same
    · have h := included (by simpa [directionsTo] using same)
      have other : right i ≠ base i := by simpa [directionsTo] using h
      cases hb : base i <;> cases hl : left i <;> cases hr : right i <;> simp_all
  · intro between i member
    have different : left i ≠ base i := by simpa [directionsTo] using member
    have equal := (between i).resolve_left different
    simpa [directionsTo, ← equal] using different

/-- A vertex belongs to the closed star when the entire face from the base is admitted. -/
def starVertices (vertices : Set (ι → Bool)) (base : ι → Bool) : Set (ι → Bool) :=
  {vertex | directionsTo base vertex ∈ link vertices base}

/-- Star membership requires every vertex between the base and the given vertex. -/
theorem mem_starVertices_iff (vertices : Set (ι → Bool)) (base vertex : ι → Bool) :
    vertex ∈ starVertices vertices base ↔
      ∀ other, (∀ i, other i = base i ∨ other i = vertex i) → other ∈ vertices := by
  constructor
  · intro member other between
    simpa using member (directionsTo base other)
      ((directionsTo_subset_iff base other vertex).mpr between)
  · intro between subset included
    apply between (corner base subset)
    apply (directionsTo_subset_iff base _ vertex).mp
    simpa using included

/-- The star grows monotonically with the set of admitted vertices. -/
theorem starVertices_mono {left right : Set (ι → Bool)} (included : left ⊆ right)
    (base : ι → Bool) : starVertices left base ⊆ starVertices right base :=
  fun _ member => link_mono included base member

/-- Star membership is closed under moving toward the base. -/
theorem starVertices_between {vertices : Set (ι → Bool)} {base vertex other : ι → Bool}
    (member : vertex ∈ starVertices vertices base)
    (between : ∀ i, other i = base i ∨ other i = vertex i) :
    other ∈ starVertices vertices base :=
  link_downward ((directionsTo_subset_iff base other vertex).mpr between) member

/-- The opposite corner belongs to a star exactly when its direction set belongs to the link. -/
@[simp] theorem corner_mem_starVertices_iff (vertices : Set (ι → Bool))
    (base : ι → Bool) (directions : Finset ι) :
    corner base directions ∈ starVertices vertices base ↔ directions ∈ link vertices base := by
  simp [starVertices]

/-- Every star vertex belongs to the underlying cubical complex. -/
theorem starVertices_subset (vertices : Set (ι → Bool)) (base : ι → Bool) :
    starVertices vertices base ⊆ vertices := by
  intro vertex member
  simpa using member (directionsTo base vertex) (Finset.Subset.refl _)

/-- The geometric closed star, with every admitted cube filled. -/
def closedStar (vertices : Set (ι → Bool)) (base : ι → Bool) : Set (ι → Real) :=
  cubical (starVertices vertices base)

/-- Boolean membership in the geometric star is exactly combinatorial star membership. -/
theorem realVertex_mem_closedStar_iff (vertices : Set (ι → Bool)) (base vertex : ι → Bool) :
    realVertex vertex ∈ closedStar vertices base ↔ vertex ∈ starVertices vertices base :=
  realVertex_mem_cubical_iff _ _

/-- Geometric star intersection is witnessed by a common Boolean vertex. -/
theorem closedStar_inter_nonempty_iff (vertices : Set (ι → Bool)) (left right : ι → Bool) :
    (closedStar vertices left ∩ closedStar vertices right).Nonempty ↔
      (starVertices vertices left ∩ starVertices vertices right).Nonempty := by
  classical
  constructor
  · rintro ⟨point, hl, hr⟩
    let vertex : ι → Bool := fun i => decide (point i = 1)
    have compatible : Compatible point vertex := by
      intro i
      constructor
      · intro zero
        simp [vertex, zero]
      · intro one
        simp [vertex, one]
    exact ⟨vertex, hl.2 vertex compatible, hr.2 vertex compatible⟩
  · rintro ⟨vertex, hl, hr⟩
    exact ⟨realVertex vertex, (realVertex_mem_closedStar_iff _ _ _).mpr hl,
      (realVertex_mem_closedStar_iff _ _ _).mpr hr⟩

/-- Every face is born by the largest vertex cost. -/
theorem faceBirth_le_maximumCost (cost : (ι → Bool) → Nat) (base : ι → Bool)
    (directions : Finset ι) : faceBirth cost base directions ≤ maximumCost cost := by
  apply Finset.sup_le
  intro subset _
  exact cost_le_maximumCost cost _

/-- The full face at any base is born precisely at maximum complexity. -/
theorem faceBirth_univ (cost : (ι → Bool) → Nat) (base : ι → Bool) :
    faceBirth cost base Finset.univ = maximumCost cost := by
  apply Nat.le_antisymm (faceBirth_le_maximumCost cost base _)
  apply Finset.sup_le
  intro vertex _
  simpa using cost_corner_le_faceBirth cost base
    (Finset.subset_univ (directionsTo base vertex))

private theorem exists_star_intersection (cost : (ι → Bool) → Nat) (left right : ι → Bool) :
    ∃ budget, (starVertices {vertex | cost vertex ≤ budget} left ∩
      starVertices {vertex | cost vertex ≤ budget} right).Nonempty := by
  refine ⟨maximumCost cost, left, ?_, ?_⟩ <;>
    intro subset _ <;> exact cost_le_maximumCost cost _

/-- The first budget where two closed cubical stars meet. -/
noncomputable def firstMeeting (cost : (ι → Bool) → Nat) (left right : ι → Bool) : Nat := by
  classical
  exact Nat.find (exists_star_intersection cost left right)

/-- The first meeting budget is attained by a common Boolean vertex. -/
theorem firstMeeting_spec (cost : (ι → Bool) → Nat) (left right : ι → Bool) :
    (starVertices {vertex | cost vertex ≤ firstMeeting cost left right} left ∩
      starVertices {vertex | cost vertex ≤ firstMeeting cost left right} right).Nonempty := by
  classical
  exact Nat.find_spec (exists_star_intersection cost left right)

/-- A budget is at or above first contact exactly when the two stars meet. -/
theorem firstMeeting_le_iff (cost : (ι → Bool) → Nat) (left right : ι → Bool) (budget : Nat) :
    firstMeeting cost left right ≤ budget ↔
      (starVertices {vertex | cost vertex ≤ budget} left ∩
        starVertices {vertex | cost vertex ≤ budget} right).Nonempty := by
  classical
  constructor
  · intro bound
    obtain ⟨vertex, hl, hr⟩ := firstMeeting_spec cost left right
    exact ⟨vertex, starVertices_mono (fun _ h => h.trans bound) left hl,
      starVertices_mono (fun _ h => h.trans bound) right hr⟩
  · exact Nat.find_min' (exists_star_intersection cost left right)

/-- The first meeting definition agrees with geometric intersection. -/
theorem firstMeeting_le_iff_geometric (cost : (ι → Bool) → Nat)
    (left right : ι → Bool) (budget : Nat) :
    firstMeeting cost left right ≤ budget ↔
      (closedStar {vertex | cost vertex ≤ budget} left ∩
        closedStar {vertex | cost vertex ≤ budget} right).Nonempty := by
  rw [closedStar_inter_nonempty_iff, firstMeeting_le_iff]

end Finite

namespace Face

/-- The unique face incident to a given base with the specified free coordinates. -/
def atVertex (base : Fin n → Bool) (directions : Finset (Fin n)) : Face n :=
  fun i => if i ∈ directions then none else some (base i)

/-- An incident face has exactly the specified free coordinates. -/
@[simp] theorem free_atVertex (base : Fin n → Bool) (directions : Finset (Fin n)) :
    (atVertex base directions).free = directions := by
  ext i
  simp [free, atVertex]

/-- The dimension of an incident face is its number of directions. -/
@[simp] theorem dimension_atVertex (base : Fin n → Bool) (directions : Finset (Fin n)) :
    (atVertex base directions).dimension = directions.card := by
  simp [dimension]

/-- Containment in an incident face means differing from the base only in its free coordinates. -/
theorem contains_atVertex_iff (base : Fin n → Bool) (directions : Finset (Fin n))
    (vertex : Fin n → Bool) :
    (atVertex base directions).Contains vertex ↔ directionsTo base vertex ⊆ directions := by
  constructor
  · intro contained i member
    by_contra absent
    have equal : base i = vertex i := by simpa [atVertex, absent] using contained i
    simp [directionsTo, equal] at member
  · intro included i
    by_cases present : i ∈ directions
    · simp [atVertex, present]
    · have same : vertex i = base i := by
        by_contra different
        exact present (included (by simpa [directionsTo] using different))
      simp [atVertex, present, same]

/-- The link agrees with admission of the corresponding incident cube face. -/
theorem allowed_atVertex_iff (vertices : Set (Fin n → Bool))
    (base : Fin n → Bool) (directions : Finset (Fin n)) :
    (atVertex base directions).Allowed vertices ↔ directions ∈ link vertices base := by
  constructor
  · intro allowed subset included
    apply allowed
    rw [contains_atVertex_iff, directionsTo_corner]
    exact included
  · intro member vertex contained
    simpa using member (directionsTo base vertex) ((contains_atVertex_iff _ _ _).mp contained)

end Face

end Algebraic.BooleanCube
