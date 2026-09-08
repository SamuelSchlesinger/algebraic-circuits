import Algebraic.BooleanCube.Star
import Mathlib.Analysis.Convex.Contractible

/-!
# Geometric realization of cubical stars

The combinatorial star realizes exactly the union of admitted faces
incident to the base. It is star convex and, when its base is admitted,
contractible by Mathlib's straight-line homotopy theorem.
-/

namespace Algebraic.BooleanCube

/-- A closed star is exactly the union of the admitted cube faces incident to its base. -/
theorem mem_closedStar_iff_exists_directions (vertices : Set (Fin n → Bool))
    (base : Fin n → Bool) (point : Fin n → Real) :
    point ∈ closedStar vertices base ↔ ∃ directions,
      directions ∈ link vertices base ∧ point ∈ (Face.atVertex base directions).realization := by
  classical
  constructor
  · intro member
    let directions : Finset (Fin n) := Finset.univ.filter (fun i => point i ≠ realVertex base i)
    have selected (i : Fin n) : i ∈ directions ↔ point i ≠ realVertex base i := by
      simp only [directions, Finset.mem_filter, Finset.mem_univ, true_and]
    have compatible : Compatible point (corner base directions) := by
      intro i
      constructor <;> intro value <;>
        cases hb : base i <;> simp only [corner, selected, realVertex, value, hb] <;> norm_num
    have admitted := member.2 _ compatible
    refine ⟨directions, (corner_mem_starVertices_iff _ _ _).mp admitted, member.1, ?_⟩
    intro i bit fixed
    have absent : i ∉ directions := by
      intro present
      simp [Face.atVertex, present] at fixed
    have equal : point i = realVertex base i := by simpa [directions] using absent
    have bitEqual : base i = bit := by simpa [Face.atVertex, absent] using fixed
    simpa [realVertex, bitEqual] using equal
  · rintro ⟨directions, admitted, member⟩
    apply Face.realization_subset_cubical (vertices := starVertices vertices base) ?_ member
    intro vertex contained
    exact link_downward ((Face.contains_atVertex_iff _ _ _).mp contained) admitted

private theorem closedStar_starConvex_fin (vertices : Set (Fin n → Bool)) (base : Fin n → Bool) :
    StarConvex Real (realVertex base) (closedStar vertices base) := by
  intro point member a b ha hb sum
  obtain ⟨directions, admitted, bounds, fixed⟩ :=
    (mem_closedStar_iff_exists_directions vertices base point).mp member
  apply (mem_closedStar_iff_exists_directions vertices base _).mpr
  refine ⟨directions, admitted, ?_, ?_⟩
  · intro i
    have lower := (bounds i).1
    have upper := (bounds i).2
    change 0 ≤ a * realVertex base i + b * point i ∧
      a * realVertex base i + b * point i ≤ 1
    cases value : base i <;> simp only [realVertex, value, Bool.false_eq_true, ↓reduceIte,
      mul_zero, mul_one, zero_add] <;>
      constructor <;> nlinarith
  · intro i bit h
    have equal := fixed i bit h
    have absent : i ∉ directions := by
      intro present
      simp [Face.atVertex, present] at h
    have bitEqual : base i = bit := by simpa [Face.atVertex, absent] using h
    change a * realVertex base i + b * point i = _
    rw [equal]
    cases bit <;> simp [realVertex, bitEqual, sum]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Boolean star membership is unchanged by an equivalence of coordinate types. -/
theorem mem_starVertices_reindex_iff (equiv : ι ≃ κ) (vertices : Set (κ → Bool))
    (base : κ → Bool) (vertex : ι → Bool) :
    vertex ∈ starVertices {other | other ∘ equiv.symm ∈ vertices} (base ∘ equiv) ↔
      vertex ∘ equiv.symm ∈ starVertices vertices base := by
  rw [mem_starVertices_iff, mem_starVertices_iff]
  constructor
  · intro allowed other between
    have result := allowed (other ∘ equiv) (fun i => by simpa using between (equiv i))
    simpa [Function.comp_def] using result
  · intro allowed other between
    apply allowed (other ∘ equiv.symm)
    intro i
    simpa using between (equiv.symm i)

/-- Realized star membership is unchanged by an equivalence of coordinate types. -/
theorem mem_closedStar_reindex_iff (equiv : ι ≃ κ) (vertices : Set (κ → Bool))
    (base : κ → Bool) (point : κ → Real) :
    point ∘ equiv ∈ closedStar {other | other ∘ equiv.symm ∈ vertices} (base ∘ equiv) ↔
      point ∈ closedStar vertices base := by
  constructor
  · intro member
    constructor
    · intro i
      simpa using member.1 (equiv.symm i)
    · intro vertex compatible
      have lifted := member.2 (vertex ∘ equiv) (fun i => compatible (equiv i))
      have translated := (mem_starVertices_reindex_iff equiv vertices base (vertex ∘ equiv)).mp lifted
      simpa [Function.comp_def] using translated
  · intro member
    constructor
    · intro i
      exact member.1 (equiv i)
    · intro vertex compatible
      apply (mem_starVertices_reindex_iff equiv vertices base vertex).mpr
      apply member.2
      intro i
      simpa [Function.comp_def] using compatible (equiv.symm i)

/-- The union of incident admitted cubes is star convex for any finite coordinate type. -/
theorem closedStar_starConvex (vertices : Set (ι → Bool)) (base : ι → Bool) :
    StarConvex Real (realVertex base) (closedStar vertices base) := by
  intro point member a b ha hb sum
  let equiv := (Fintype.equivFin ι).symm
  have lifted := (mem_closedStar_reindex_iff equiv vertices base point).mpr member
  have convex := closedStar_starConvex_fin {other | other ∘ equiv.symm ∈ vertices} (base ∘ equiv)
  exact (mem_closedStar_reindex_iff equiv vertices base _).mp (convex lifted ha hb sum)

/-- Every nonempty cubical star is contractible, via Mathlib's star-convexity theorem. -/
theorem closedStar_contractible (vertices : Set (ι → Bool)) (base : ι → Bool)
    (admitted : base ∈ vertices) : ContractibleSpace (closedStar vertices base) := by
  apply (closedStar_starConvex vertices base).contractibleSpace
  refine ⟨realVertex base, (realVertex_mem_closedStar_iff _ _ _).mpr ?_⟩
  apply (mem_starVertices_iff _ _ _).mpr
  intro other between
  have equal : other = base := by
    funext i
    exact (between i).elim id id
  simpa [equal] using admitted

end Algebraic.BooleanCube
