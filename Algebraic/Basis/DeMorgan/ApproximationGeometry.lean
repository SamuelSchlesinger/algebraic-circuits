import Algebraic.Basis.DeMorgan.StarIntersection
import Algebraic.BooleanCube.Distance

/-!
# Geometric circuit approximation

The Hamming distance to a native circuit sublevel is the minimum number of
truth-table errors among circuits within that budget. The normalized error
is an exact rational, and the counting bound controls all radius neighborhoods.
-/

namespace Algebraic.DeMorgan

/-- The finite family of functions with native circuit complexity at most the budget. -/
noncomputable def easyFunctions (n budget : Nat) : Finset (ScalarFunction Bool n) := by
  classical
  exact Finset.univ.filter (fun function => complexity function ≤ budget)

/-- Membership in the finite easy family is the original circuit size predicate. -/
@[simp] theorem mem_easyFunctions (function : ScalarFunction Bool n) (budget : Nat) :
    function ∈ easyFunctions n budget ↔ complexity function ≤ budget := by
  classical
  simp [easyFunctions]

/-- A budget admitting constants always has a nonempty easy family. -/
theorem easyFunctions_nonempty (n : Nat) (positive : 1 ≤ budget) : (easyFunctions n budget).Nonempty :=
  ⟨fun _ => false, (mem_easyFunctions _ _).mpr ((complexity_constant_le n false).trans positive)⟩

/-- The minimum unnormalized truth-table error attainable at a nonempty native circuit budget. -/
noncomputable def approximationDistance (function : ScalarFunction Bool n) (budget : Nat) (positive : 1 ≤ budget) : Nat :=
  BooleanCube.distanceTo (easyFunctions n budget) (easyFunctions_nonempty n positive) function

/-- Some circuit-computable function attains the exact approximation distance. -/
theorem exists_best_approximation (function : ScalarFunction Bool n) (budget : Nat) (positive : 1 ≤ budget) :
    ∃ approximant, complexity approximant ≤ budget ∧
      approximationDistance function budget positive = hammingDist function approximant := by
  obtain ⟨approximant, member, equal⟩ := BooleanCube.exists_nearest (easyFunctions n budget)
    (easyFunctions_nonempty n positive) function
  exact ⟨approximant, (mem_easyFunctions _ _).mp member, equal⟩

/-- A distance bound is equivalent to the existence of a circuit approximation with that many errors. -/
theorem approximationDistance_le_iff (function : ScalarFunction Bool n) (budget : Nat)
    (positive : 1 ≤ budget) (radius : Nat) :
    approximationDistance function budget positive ≤ radius ↔
      ∃ approximant, complexity approximant ≤ budget ∧ hammingDist function approximant ≤ radius := by
  simpa only [approximationDistance, mem_easyFunctions] using BooleanCube.distanceTo_le_iff (easyFunctions n budget)
    (easyFunctions_nonempty n positive) function radius

/-- Exact computation is the zero-error case of approximation. -/
@[simp] theorem approximationDistance_eq_zero (function : ScalarFunction Bool n) (budget : Nat)
    (positive : 1 ≤ budget) :
    approximationDistance function budget positive = 0 ↔ complexity function ≤ budget := by
  simpa only [approximationDistance, mem_easyFunctions] using BooleanCube.distanceTo_eq_zero (easyFunctions n budget)
    (easyFunctions_nonempty n positive) function

/-- Circuit Lipschitzness gives a lower bound on distance from a low-complexity sublevel. -/
theorem complexity_le_budget_add_distance (function : ScalarFunction Bool n) (budget : Nat)
    (positive : 1 ≤ budget) :
    complexity function ≤ budget + 2 * n * approximationDistance function budget positive := by
  obtain ⟨approximant, cheap, nearest⟩ := exists_best_approximation function budget positive
  have bound := complexity_le_add_hammingDist approximant function
  rw [hammingDist_comm approximant function, ← nearest] at bound
  omega

/-- Approximation distance changes by at most the Hamming distance between target functions. -/
theorem approximationDistance_dist_le (left right : ScalarFunction Bool n) (budget : Nat)
    (positive : 1 ≤ budget) :
    Nat.dist (approximationDistance left budget positive) (approximationDistance right budget positive) ≤
      hammingDist left right :=
  BooleanCube.distanceTo_dist_le _ _ _ _

/-- Increasing the available circuit size can only improve the best approximation. -/
theorem approximationDistance_antitone (function : ScalarFunction Bool n) (small large : Nat)
    (smallPositive : 1 ≤ small) (largePositive : 1 ≤ large) (included : small ≤ large) :
    approximationDistance function large largePositive ≤ approximationDistance function small smallPositive := by
  obtain ⟨approximant, cheap, equal⟩ := exists_best_approximation function small smallPositive
  apply (approximationDistance_le_iff function large largePositive _).mpr
  exact ⟨approximant, cheap.trans included, equal.ge⟩

/-- The exact minimum error fraction under the uniform input distribution. -/
noncomputable def approximationError (function : ScalarFunction Bool n) (budget : Nat) (positive : 1 ≤ budget) : ℚ :=
  (approximationDistance function budget positive : ℚ) / (2 ^ n : ℚ)

/-- Normalized geometric distance is precisely the best uniform-input circuit approximation error. -/
theorem approximationError_le_iff (function : ScalarFunction Bool n) (budget : Nat)
    (positive : 1 ≤ budget) (error : ℚ) :
    approximationError function budget positive ≤ error ↔
      ∃ approximant, complexity approximant ≤ budget ∧
        (hammingDist function approximant : ℚ) / (2 ^ n : ℚ) ≤ error := by
  constructor
  · intro bounded
    obtain ⟨approximant, cheap, equal⟩ := exists_best_approximation function budget positive
    refine ⟨approximant, cheap, ?_⟩
    simpa only [approximationError, equal] using bounded
  · rintro ⟨approximant, cheap, bounded⟩
    have distance := (approximationDistance_le_iff function budget positive _).mpr ⟨approximant, cheap, le_rfl⟩
    exact (div_le_div_of_nonneg_right (by exact_mod_cast distance) (by positivity : (0 : ℚ) ≤ 2 ^ n)).trans bounded

/-- The counting-only bound on all functions approximable within a given number of errors. -/
theorem card_easy_neighborhood_le (n budget radius : Nat) :
    (BooleanCube.neighborhood (easyFunctions n budget) radius).card ≤
      (easyFunctions n budget).card * ∑ k ∈ Finset.range (radius + 1), (2 ^ n).choose k := by
  simpa using BooleanCube.card_neighborhood_le (easyFunctions n budget) radius

/-- A strict neighborhood counting bound guarantees a function far from every circuit in the budget. -/
theorem exists_function_far_from_easy (n budget radius : Nat) (positive : 1 ≤ budget)
    (small : (easyFunctions n budget).card *
      (∑ k ∈ Finset.range (radius + 1), (2 ^ n).choose k) < 2 ^ (2 ^ n)) :
    ∃ function : ScalarFunction Bool n, radius < approximationDistance function budget positive := by
  have smaller : (BooleanCube.neighborhood (easyFunctions n budget) radius).card <
      (Finset.univ : Finset (ScalarFunction Bool n)).card := by
    simpa using (card_easy_neighborhood_le n budget radius).trans_lt small
  obtain ⟨function, _, outside⟩ := Finset.exists_mem_notMem_of_card_lt_card smaller
  refine ⟨function, ?_⟩
  by_contra near
  apply outside
  apply (BooleanCube.mem_neighborhood_iff _ (easyFunctions_nonempty n positive) function radius).mpr
  change approximationDistance function budget positive ≤ radius
  omega

end Algebraic.DeMorgan
