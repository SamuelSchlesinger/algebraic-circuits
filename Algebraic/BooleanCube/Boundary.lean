import Algebraic.BooleanCube
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators

/-!
# Sublevel boundaries and discrete coarea

Every unoriented cube edge is represented once, by its endpoint whose
changing coordinate is false and the index of that coordinate. The coarea
identity counts the levels crossed by each edge. All sums are finite.
-/

namespace Algebraic.BooleanCube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Canonically oriented cube edges, with the changing coordinate initially false. -/
def edges : Finset ((ι → Bool) × ι) :=
  Finset.univ.filter (fun edge => edge.1 edge.2 = false)

/-- The true endpoint of a canonically oriented cube edge. -/
def edgeEnd (edge : (ι → Bool) × ι) : ι → Bool :=
  Function.update edge.1 edge.2 true

/-- Each canonical edge changes exactly one coordinate. -/
theorem hammingDist_edgeEnd {edge : (ι → Bool) × ι} (member : edge ∈ edges) :
    hammingDist edge.1 (edgeEnd edge) = 1 := by
  classical
  have initial : edge.1 edge.2 = false := (Finset.mem_filter.mp member).2
  have different : Finset.univ.filter (fun i => edge.1 i ≠ edgeEnd edge i) = {edge.2} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases equal : i = edge.2 <;> simp [edgeEnd, equal, initial]
  simp only [hammingDist, different, Finset.card_singleton]

/-- The `d`-cube has `d * 2^(d-1)` unoriented edges, including dimension zero. -/
theorem card_edges : (edges (ι := ι)).card = Fintype.card ι * 2 ^ (Fintype.card ι - 1) := by
  classical
  have fiber (i : ι) : (Finset.univ.filter (fun f : ι → Bool => f i = false)).card =
      2 ^ (Fintype.card ι - 1) := by
    simpa only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_bool] using
      Fintype.card_filter_piFinset_const_eq_of_mem
      (ι := ι) (Finset.univ : Finset Bool) i (Finset.mem_univ false)
  simp only [edges, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : ι, (Finset.univ.filter (fun f : ι → Bool => f i = false)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = _ := by simp [fiber]

/-- A finite cost function has a largest value. -/
def maximumCost (cost : (ι → Bool) → Nat) : Nat := Finset.univ.sup cost

/-- The canonical maximum is an upper bound at every vertex. -/
theorem cost_le_maximumCost (cost : (ι → Bool) → Nat) (vertex : ι → Bool) :
    cost vertex ≤ maximumCost cost := Finset.le_sup (Finset.mem_univ vertex)

/-- An edge crosses a sublevel threshold when the endpoint costs straddle it. -/
def edgeBoundary (cost : (ι → Bool) → Nat) (threshold : Nat) :
    Finset ((ι → Bool) × ι) :=
  edges.filter (fun edge => min (cost edge.1) (cost (edgeEnd edge)) ≤ threshold ∧
    threshold < max (cost edge.1) (cost (edgeEnd edge)))

/-- The boundary definition is exactly disagreement of sublevel membership. -/
theorem mem_edgeBoundary_iff (cost : (ι → Bool) → Nat) (threshold : Nat)
    (edge : (ι → Bool) × ι) :
    edge ∈ edgeBoundary cost threshold ↔ edge ∈ edges ∧
      ¬(cost edge.1 ≤ threshold ↔ cost (edgeEnd edge) ≤ threshold) := by
  simp only [edgeBoundary, Finset.mem_filter]
  apply and_congr_right
  intro _
  by_cases left : cost edge.1 ≤ threshold <;>
    by_cases right : cost (edgeEnd edge) ≤ threshold <;> simp_all
  omega

/-- Summing boundary sizes counts each edge once per unit change of cost. -/
theorem sum_edgeBoundary_eq (cost : (ι → Bool) → Nat) (bound : Nat)
    (bounded : ∀ vector, cost vector ≤ bound) :
    ∑ threshold ∈ Finset.range bound, (edgeBoundary cost threshold).card =
      ∑ edge ∈ edges, Nat.dist (cost edge.1) (cost (edgeEnd edge)) := by
  classical
  have levels (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) :
      (Finset.range bound).filter (fun threshold =>
        min a b ≤ threshold ∧ threshold < max a b) = Finset.Ico (min a b) (max a b) := by
    ext threshold
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  simp only [edgeBoundary, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones,
    levels _ _ (bounded _) (bounded _), Nat.card_Ico]
  unfold Nat.dist
  omega

/-- A uniform edge-change bound bounds the sum of all sublevel perimeters. -/
theorem sum_edgeBoundary_le (cost : (ι → Bool) → Nat) (bound change : Nat)
    (bounded : ∀ vector, cost vector ≤ bound)
    (step : ∀ edge ∈ edges,
      Nat.dist (cost edge.1) (cost (edgeEnd edge)) ≤ change) :
    ∑ threshold ∈ Finset.range bound, (edgeBoundary cost threshold).card ≤
      (edges (ι := ι)).card * change := by
  rw [sum_edgeBoundary_eq cost bound bounded]
  calc
    _ ≤ ∑ _edge ∈ edges (ι := ι), change := Finset.sum_le_sum step
    _ = _ := by simp

/-- Every boundary edge lies within the edge-change bound of its threshold. -/
theorem edgeBoundary_band (cost : (ι → Bool) → Nat) (threshold change : Nat)
    {edge : (ι → Bool) × ι} (member : edge ∈ edgeBoundary cost threshold)
    (step : Nat.dist (cost edge.1) (cost (edgeEnd edge)) ≤ change) :
    threshold < min (cost edge.1) (cost (edgeEnd edge)) + change ∧
      max (cost edge.1) (cost (edgeEnd edge)) ≤ threshold + change := by
  have crossing := (Finset.mem_filter.mp member).2
  unfold Nat.dist at step
  omega

end Algebraic.BooleanCube
