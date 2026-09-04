import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Descending-chain rank envelopes

This module isolates a combinatorial recurrence suggested by coefficient-matrix
rank arguments for unrestricted noncommutative arithmetic circuits.  After
product gates are put in topological order, recursively expanding a rank term
can only move to an earlier product gate.  At the same time, the left or right
degree coordinate decreases strictly.  Forgetting which split realizes a
given remaining total degree gives the recurrence

`R (s + 1) t <= R s t + 1 + 2 * sum_{u < t} R s u`.

Here `s` is the number of available product gates and `t` is the remaining
degree budget after reserving one positive degree on each side of the
coefficient-matrix split.  The factor two records the two possible directions
of a degree decrease.  The main theorem bounds every profile satisfying this
recurrence by

`s * 2 ^ t * multichoose s t`.

For `s > 0`, this is

`s * 2 ^ t * choose (s + t - 1) t`.

Thus acyclicity replaces arbitrary recursive gate choices by a stars-and-bars
count of descending gate chains.  At total degree `d`, substitute `t = d - 2`.

The circuit-to-recurrence reduction is not asserted in this module.  In
particular, the result below is a machine-checked combinatorial lemma, not yet
a formalization of a noncommutative circuit lower bound.  The motivating local
product-rank inequality is Equation (2) of:

* R. Raz, *Polynomial Lower Bounds for Arithmetic Circuits over
  Non-Commutative Rings* (2026), https://arxiv.org/abs/2604.22006.
-/

namespace Algebraic
namespace LowerBound
namespace Noncommutative
namespace DescendingChain

open Finset

/-- The proposed universal envelope for a two-direction descending rank
recurrence.  `Nat.multichoose gates budget` counts weakly increasing choices
of `budget` cuts among `gates` positions. -/
def envelope (gates budget : Nat) : Nat :=
  gates * 2 ^ budget * Nat.multichoose gates budget

@[simp] theorem envelope_zero_gates (budget : Nat) :
    envelope 0 budget = 0 := by
  simp [envelope]

@[simp] theorem envelope_zero_budget (gates : Nat) :
    envelope gates 0 = gates := by
  simp [envelope]

/-- Stars-and-bars form of the descending-chain envelope. -/
theorem envelope_eq_choose {gates : Nat} (_positive : 0 < gates)
    (budget : Nat) :
    envelope gates budget =
      gates * 2 ^ budget * Nat.choose (gates + budget - 1) budget := by
  simp only [envelope, Nat.multichoose_eq]

/-- Twice the total envelope below `budget + 1` fits into the part of the
next-gate envelope reserved for strict degree descents. -/
theorem two_mul_sum_envelope_le (gates budget : Nat) :
    2 * (∑ smaller ∈ range (budget + 1), envelope gates smaller) ≤
      gates * 2 ^ (budget + 1) * Nat.multichoose (gates + 1) budget := by
  by_cases gatesZero : gates = 0
  · simp [gatesZero]
  have gatesPositive : 0 < gates := Nat.pos_of_ne_zero gatesZero
  have powerBound : ∀ smaller ∈ range (budget + 1),
      2 ^ smaller ≤ 2 ^ budget := by
    intro smaller smallerMem
    exact Nat.pow_le_pow_right (by omega) (by simpa using smallerMem)
  calc
    2 * (∑ smaller ∈ range (budget + 1), envelope gates smaller)
        ≤ 2 * (∑ smaller ∈ range (budget + 1),
            gates * 2 ^ budget * Nat.multichoose gates smaller) := by
          gcongr with smaller smallerMem
          unfold envelope
          exact Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (powerBound smaller smallerMem))
    _ = gates * 2 ^ (budget + 1) *
          (∑ smaller ∈ range (budget + 1),
            Nat.multichoose gates smaller) := by
          rw [← Finset.mul_sum]
          ring
    _ = gates * 2 ^ (budget + 1) *
          Nat.choose (budget + gates) gates := by
          rw [Nat.sum_range_multichoose]
    _ = gates * 2 ^ (budget + 1) *
          Nat.multichoose (gates + 1) budget := by
          rw [Nat.multichoose_eq]
          apply congrArg (fun value : Nat =>
            gates * 2 ^ (budget + 1) * value)
          calc
            Nat.choose (budget + gates) gates =
                Nat.choose (budget + gates) budget :=
              Nat.choose_symm_of_eq_add (by omega)
            _ = Nat.choose (gates + 1 + budget - 1) budget := by
              congr 1
              omega

/-- One more gate preserves the envelope under the two-direction recurrence. -/
theorem envelope_step (gates budget : Nat) :
    envelope gates budget + 1 +
        2 * (∑ smaller ∈ range budget, envelope gates smaller) ≤
      envelope (gates + 1) budget := by
  cases budget with
  | zero => simp
  | succ budget =>
      calc
        envelope gates (budget + 1) + 1 +
            2 * (∑ smaller ∈ range (budget + 1), envelope gates smaller)
            ≤ envelope gates (budget + 1) + 1 +
                gates * 2 ^ (budget + 1) *
                  Nat.multichoose (gates + 1) budget := by
              exact Nat.add_le_add_left
                (two_mul_sum_envelope_le gates budget) _
        _ ≤ envelope gates (budget + 1) +
              gates * 2 ^ (budget + 1) *
                Nat.multichoose (gates + 1) budget +
              2 ^ (budget + 1) *
                (Nat.multichoose gates (budget + 1) +
                  Nat.multichoose (gates + 1) budget) := by
              have multichoosePositive :
                  0 < Nat.multichoose (gates + 1) budget := by
                rw [Nat.multichoose_eq]
                exact Nat.choose_pos (by omega)
              have positiveRemainder : 0 <
                  2 ^ (budget + 1) *
                    (Nat.multichoose gates (budget + 1) +
                      Nat.multichoose (gates + 1) budget) :=
                Nat.mul_pos (by positivity)
                  (lt_of_lt_of_le multichoosePositive (by omega))
              omega
        _ = envelope (gates + 1) (budget + 1) := by
              unfold envelope
              rw [Nat.multichoose_succ_succ]
              ring

/-- A cumulative rank profile obeys the descending-chain recurrence. -/
structure Profile (rank : Nat → Nat → Nat) : Prop where
  /-- No product gates provide no rank. -/
  zero : ∀ budget, rank 0 budget = 0
  /-- Adding one product gate contributes one boundary-rank term and may
  recurse in either of the two strict degree directions. -/
  step : ∀ gates budget,
    rank (gates + 1) budget ≤
      rank gates budget + 1 +
        2 * (∑ smaller ∈ range budget, rank gates smaller)

/-- Every two-direction descending rank profile is bounded by the explicit
stars-and-bars envelope. -/
theorem Profile.rank_le_envelope
    {rank : Nat → Nat → Nat}
    (profile : Profile rank) :
    ∀ gates budget, rank gates budget ≤ envelope gates budget := by
  intro gates
  induction gates with
  | zero =>
      intro budget
      simp [profile.zero]
  | succ gates inductionHypothesis =>
      intro budget
      calc
        rank (gates + 1) budget ≤
            rank gates budget + 1 +
              2 * (∑ smaller ∈ range budget, rank gates smaller) :=
          profile.step gates budget
        _ ≤ envelope gates budget + 1 +
              2 * (∑ smaller ∈ range budget, envelope gates smaller) := by
          gcongr with smaller smallerMem
          · exact inductionHypothesis budget
          · exact inductionHypothesis smaller
        _ ≤ envelope (gates + 1) budget := envelope_step gates budget

/-- Output-facing form: any target rank dominated by a descending profile is
bounded by the same explicit envelope. -/
theorem Profile.targetRank_le_envelope
    {rank : Nat → Nat → Nat}
    (profile : Profile rank)
    {targetRank gates budget : Nat}
    (target_le : targetRank ≤ rank gates budget) :
    targetRank ≤ envelope gates budget :=
  target_le.trans (profile.rank_le_envelope gates budget)

/-- Total rank contributed by the product gates preceding `gates`. -/
def totalRank (gateRank : Nat → Nat → Nat) (gates budget : Nat) : Nat :=
  ∑ gate ∈ range gates, gateRank gate budget

@[simp] theorem totalRank_zero
    (gateRank : Nat → Nat → Nat) (budget : Nat) :
    totalRank gateRank 0 budget = 0 := by
  simp [totalRank]

theorem totalRank_succ
    (gateRank : Nat → Nat → Nat) (gates budget : Nat) :
    totalRank gateRank (gates + 1) budget =
      totalRank gateRank gates budget + gateRank gates budget := by
  simp [totalRank, Finset.sum_range_succ]

/-- Gate-local form of the descending recurrence.  A gate starts one terminal
rank-one branch.  Every nonterminal branch moves to an earlier gate and to a
strictly smaller degree budget, in one of two directions. -/
structure GateRecurrence (gateRank : Nat → Nat → Nat) : Prop where
  step : ∀ gate budget,
    gateRank gate budget ≤
      1 + 2 * (∑ smaller ∈ range budget,
        totalRank gateRank gate smaller)

/-- Cumulative gate ranks satisfying the gate-local recurrence form a
`Profile`. -/
theorem GateRecurrence.profile
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank) :
    Profile (totalRank gateRank) where
  zero := totalRank_zero gateRank
  step gates budget := by
    rw [totalRank_succ]
    have gateBound := Nat.add_le_add_left
      (recurrence.step gates budget) (totalRank gateRank gates budget)
    omega

/-- The total rank of any gate sequence satisfying the local recurrence is at
most the descending-chain envelope. -/
theorem GateRecurrence.totalRank_le_envelope
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank)
    (gates budget : Nat) :
    totalRank gateRank gates budget ≤ envelope gates budget :=
  recurrence.profile.rank_le_envelope gates budget

/-- Stars-and-bars form of `GateRecurrence.totalRank_le_envelope`. -/
theorem GateRecurrence.totalRank_le_choose
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank)
    {gates : Nat}
    (positive : 0 < gates)
    (budget : Nat) :
    totalRank gateRank gates budget ≤
      gates * 2 ^ budget * Nat.choose (gates + budget - 1) budget := by
  rw [← envelope_eq_choose positive]
  exact recurrence.totalRank_le_envelope gates budget

/-- Output-facing gate-sequence bound. -/
theorem GateRecurrence.targetRank_le_choose
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank)
    {targetRank gates budget : Nat}
    (positive : 0 < gates)
    (target_le : targetRank ≤ totalRank gateRank gates budget) :
    targetRank ≤
      gates * 2 ^ budget * Nat.choose (gates + budget - 1) budget :=
  target_le.trans (recurrence.totalRank_le_choose positive budget)

/-- Degree-indexed form.  A positive coefficient-matrix split of total degree
`degree` has `degree - 2` remaining unit descents after one unit is reserved on
each side. -/
theorem GateRecurrence.targetRank_le_degree_choose
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank)
    {targetRank gates degree : Nat}
    (positive : 0 < gates)
    (degreeAtLeastTwo : 2 ≤ degree)
    (target_le :
      targetRank ≤ totalRank gateRank gates (degree - 2)) :
    targetRank ≤
      gates * 2 ^ (degree - 2) *
        Nat.choose (gates + degree - 3) (degree - 2) := by
  have bound := recurrence.targetRank_le_choose positive target_le
  have indexEquality : gates + (degree - 2) - 1 =
      gates + degree - 3 := by
    omega
  simpa [indexEquality] using bound

/-- At degree two there is no recursive degree budget: each product gate can
contribute at most one unit of rank. -/
theorem GateRecurrence.targetRank_le_gates_of_degree_two
    {gateRank : Nat → Nat → Nat}
    (recurrence : GateRecurrence gateRank)
    {targetRank gates : Nat}
    (target_le : targetRank ≤ totalRank gateRank gates 0) :
    targetRank ≤ gates := by
  exact target_le.trans (by
    simpa using recurrence.totalRank_le_envelope gates 0)

end DescendingChain
end Noncommutative
end LowerBound
end Algebraic
