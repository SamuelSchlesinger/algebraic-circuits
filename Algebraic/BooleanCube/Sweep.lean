import Algebraic.BooleanCube
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ordered sweeps and budgeted paths on a Boolean cube

Coordinates have distinct natural-number ranks. Replacing a prefix of
coordinates produces a shortest Hamming walk after repetitions are removed.
Every vertex of the resulting walk is one of the prefix replacements, so
any uniform bound on their cost is preserved.
-/

namespace Algebraic.BooleanCube

variable {ι : Type*}

/-- The graph whose edges change exactly one Boolean coordinate. -/
def graph [Fintype ι] : SimpleGraph (ι → Bool) where
  Adj left right := hammingDist left right = 1
  symm := ⟨by intro left right h; simpa only [hammingDist_comm] using h⟩
  loopless := ⟨by intro vector; simp⟩

/-- Replace coordinates of rank below `threshold` by their values in `finish`. -/
def patch (rank : ι → Nat) (start finish : ι → Bool) (threshold : Nat) : ι → Bool :=
  fun i => if rank i < threshold then finish i else start i

/-- Erase a prefix of truth-table coordinates. -/
def erase (rank : ι → Nat) (threshold : Nat) (vector : ι → Bool) : ι → Bool :=
  patch rank vector (fun _ => false) threshold

@[simp] theorem patch_zero (rank : ι → Nat) (start finish : ι → Bool) :
    patch rank start finish 0 = start := by funext i; simp [patch]

/-- Once the sweep passes every rank, all coordinates have been replaced. -/
theorem patch_eq_finish (rank : ι → Nat) (start finish : ι → Bool) (length : Nat)
    (bounded : ∀ i, rank i < length) : patch rank start finish length = finish := by
  funext i
  simp [patch, bounded i]

variable [Fintype ι]

/-- A prefix replacement step changes at most one coordinate. -/
theorem patch_step_le (rank : ι → Nat) (injective : Function.Injective rank)
    (start finish : ι → Bool) (threshold : Nat) :
    hammingDist (patch rank start finish threshold)
      (patch rank start finish (threshold + 1)) ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply injective
  have at_rank (k : ι) (different : patch rank start finish threshold k ≠
      patch rank start finish (threshold + 1) k) : rank k = threshold := by
    dsimp [patch] at different
    split_ifs at different <;> simp_all <;> omega
  exact (at_rank i (Finset.mem_filter.mp hi).2).trans
    (at_rank j (Finset.mem_filter.mp hj).2).symm

/-- Hamming distance adds when the middle vector preserves endpoint agreements. -/
theorem hammingDist_eq_add_of_agree (left middle right : ι → Bool)
    (agree : ∀ i, left i = right i → middle i = left i) :
    hammingDist left right = hammingDist left middle + hammingDist middle right := by
  classical
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := agree i
  cases hl : left i <;> cases hm : middle i <;> cases hr : right i <;> simp_all

/-- Successive prefix replacements make progress along a Hamming geodesic. -/
theorem patch_distance_step (rank : ι → Nat) (start finish : ι → Bool) (threshold : Nat) :
    hammingDist start (patch rank start finish (threshold + 1)) =
      hammingDist start (patch rank start finish threshold) +
        hammingDist (patch rank start finish threshold)
          (patch rank start finish (threshold + 1)) := by
  apply hammingDist_eq_add_of_agree
  intro i equal
  by_cases before : rank i < threshold
  · have next : rank i < threshold + 1 := by omega
    simpa [patch, before, next] using equal.symm
  · simp [patch, before]

/-- All vertices of a walk respect a common cost budget. -/
def Within (cost : (ι → Bool) → Nat) (budget : Nat) {left right : ι → Bool}
    (walk : graph.Walk left right) : Prop :=
  ∀ vector ∈ walk.support, cost vector ≤ budget

/-- Concatenating walks preserves their budget. -/
theorem Within.append {cost : (ι → Bool) → Nat} {budget : Nat}
    {left middle right : ι → Bool} {first : graph.Walk left middle}
    {second : graph.Walk middle right} (hf : Within cost budget first)
    (hs : Within cost budget second) : Within cost budget (first.append second) := by
  intro vector member
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp member with h | h
  · exact hf vector h
  · exact hs vector h

/-- Reversing a walk preserves its budget. -/
theorem Within.reverse {cost : (ι → Bool) → Nat} {budget : Nat}
    {left right : ι → Bool} {walk : graph.Walk left right}
    (bounded : Within cost budget walk) : Within cost budget walk.reverse := by
  simpa only [Within, SimpleGraph.Walk.support_reverse, List.mem_reverse] using bounded

/-- No cube walk is shorter than the Hamming distance between its endpoints. -/
theorem hammingDist_le_length {left right : ι → Bool} (walk : graph.Walk left right) :
    hammingDist left right ≤ walk.length := by
  induction walk with
  | nil => simp
  | @cons left middle right adjacent tail ih =>
      have triangle := hammingDist_triangle left middle right
      have adjacentDistance : hammingDist left middle = 1 := adjacent
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- A walk attaining Hamming distance has no repeated vertices. -/
theorem isPath_of_length_eq_hammingDist {left right : ι → Bool}
    (walk : graph.Walk left right) (length : walk.length = hammingDist left right) :
    walk.IsPath := by
  classical
  have equal : walk.bypass = walk :=
    walk.length_le_bypass_length_iff.mp
      (length ▸ hammingDist_le_length walk.bypass)
  rw [← equal]
  exact walk.bypass_isPath

/-- Convert a sequence allowing stationary steps into an actual shortest walk.
Every nonstationary step increases the distance from the start. -/
theorem exists_walk_of_sequence (sequence : Nat → ι → Bool)
    (cost : (ι → Bool) → Nat) (budget length : Nat)
    (bounded : ∀ t ≤ length, cost (sequence t) ≤ budget)
    (step : ∀ t < length, hammingDist (sequence t) (sequence (t + 1)) ≤ 1)
    (progress : ∀ t < length,
      hammingDist (sequence 0) (sequence (t + 1)) =
        hammingDist (sequence 0) (sequence t) +
          hammingDist (sequence t) (sequence (t + 1))) :
    ∃ walk : graph.Walk (sequence 0) (sequence length),
      Within cost budget walk ∧ walk.length = hammingDist (sequence 0) (sequence length) := by
  induction length with
  | zero =>
      refine ⟨.nil, ?_, by simp⟩
      intro vector member
      simpa using (show cost vector ≤ budget from by
        have equal : vector = sequence 0 := by simpa using member
        simpa [equal] using bounded 0 (by omega))
  | succ length ih =>
      obtain ⟨walk, within, distance⟩ := ih
        (fun t ht => bounded t (by omega)) (fun t ht => step t (by omega))
        (fun t ht => progress t (by omega))
      have next := step length (by omega)
      by_cases equal : sequence length = sequence (length + 1)
      · rw [← equal]
        exact ⟨walk, within, distance⟩
      · have adjacent : graph.Adj (sequence length) (sequence (length + 1)) := by
          have positive := (hammingDist_pos).mpr equal
          change hammingDist _ _ = 1
          omega
        let last : graph.Walk (sequence length) (sequence (length + 1)) := .cons adjacent .nil
        refine ⟨walk.append last, within.append ?_, ?_⟩
        · intro vector member
          simp only [last, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact bounded length (by omega)
          · exact bounded (length + 1) (by omega)
        · have advance := progress length (by omega)
          have adjacentDistance : hammingDist (sequence length) (sequence (length + 1)) = 1 :=
            adjacent
          simp only [SimpleGraph.Walk.length_append, last, SimpleGraph.Walk.length_cons,
            SimpleGraph.Walk.length_nil]
          omega

/-- Any cost bound on a prefix sweep yields a shortest walk at that budget. -/
theorem exists_patch_walk (rank : ι → Nat) (injective : Function.Injective rank)
    (length : Nat) (ranksBounded : ∀ i, rank i < length)
    (start finish : ι → Bool) (cost : (ι → Bool) → Nat) (budget : Nat)
    (bounded : ∀ t ≤ length, cost (patch rank start finish t) ≤ budget) :
    ∃ walk : graph.Walk start finish,
      Within cost budget walk ∧ walk.length = hammingDist start finish := by
  have result := exists_walk_of_sequence (patch rank start finish) cost budget length bounded
    (fun t _ => patch_step_le rank injective start finish t)
    (fun t _ => by simpa using patch_distance_step rank start finish t)
  rw [patch_zero, patch_eq_finish rank start finish length ranksBounded] at result
  exact result

end Algebraic.BooleanCube
