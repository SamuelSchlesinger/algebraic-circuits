import Algebraic.Basis.DeMorgan.Geometry
import Algebraic.BooleanCube.RelativeRank
import Mathlib.Data.Fintype.EquivFin

/-!
# Cubical Betti numbers force functions in a circuit-complexity shell

Truth-table coordinates are ordered by the concrete threshold-circuit rank.
Over any field, each positive-degree cubical Betti number at budget `s` is
at most `choose (2^n) (k+1)` times the number of functions with complexity
strictly above `s` and at most `s+n`.
-/

namespace Algebraic.DeMorgan

/-- The numerical index of an input assignment in truth-table order. -/
def inputIndex (n : Nat) (input : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨inputRank input, inputRank_lt input⟩

/-- The concrete assignment order enumerates all truth-table coordinates. -/
theorem inputIndex_bijective (n : Nat) : Function.Bijective (inputIndex n) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro left right equal
  exact inputRank_injective (congrArg Fin.val equal)

/-- Input assignments and their ordered truth-table indices are equivalent. -/
noncomputable def inputIndexEquiv (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  Equiv.ofBijective (inputIndex n) (inputIndex_bijective n)

/-- Reindex an ordered Boolean vector as a Boolean function on input assignments. -/
noncomputable def truthTableEquiv (n : Nat) : (Fin (2 ^ n) → Bool) ≃ ScalarFunction Bool n where
  toFun vector input := vector (inputIndex n input)
  invFun function index := function ((inputIndexEquiv n).symm index)
  left_inv vector := by
    funext index
    exact congrArg vector ((inputIndexEquiv n).apply_symm_apply index)
  right_inv function := by
    funext input
    exact congrArg function ((inputIndexEquiv n).symm_apply_apply input)

/-- Circuit complexity on the ordered vector coordinates used by cubical chains. -/
noncomputable def orderedComplexity (n : Nat) (vector : Fin (2 ^ n) → Bool) : Nat :=
  complexity (truthTableEquiv n vector)

/-- Prefix erasure commutes with the truth-table coordinate identification. -/
theorem truthTableEquiv_erase (n threshold : Nat) (vector : Fin (2 ^ n) → Bool) :
    truthTableEquiv n (BooleanCube.erase Fin.val threshold vector) =
      BooleanCube.erase inputRank threshold (truthTableEquiv n vector) := by
  funext input
  rfl

/-- Ordered truth-table erasure has the same additive circuit-cost bound. -/
theorem orderedComplexity_erase_le (positive : 0 < n) (threshold : Nat)
    (vector : Fin (2 ^ n) → Bool) :
    orderedComplexity n (BooleanCube.erase Fin.val threshold vector) ≤ orderedComplexity n vector + n := by
  unfold orderedComplexity
  rw [truthTableEquiv_erase]
  exact complexity_erase_le positive _ _

/-- The finite shell of functions entering between budgets `s` and `s+n`. -/
noncomputable def complexityShell (n budget : Nat) : Finset (ScalarFunction Bool n) := by
  classical
  exact Finset.univ.filter (fun function => budget < complexity function ∧ complexity function ≤ budget + n)

/-- The shell includes its upper budget and excludes its lower budget. -/
@[simp] theorem mem_complexityShell (n budget : Nat) (function : ScalarFunction Bool n) :
    function ∈ complexityShell n budget ↔ budget < complexity function ∧ complexity function ≤ budget + n := by
  classical
  simp [complexityShell]

/-- Cubical homology dimension of the circuit-complexity sublevel. -/
noncomputable def cubicalBetti (K : Type*) [Field K] (n budget degree : Nat) : Nat :=
  BooleanCube.CubicalHomology.betti K {vector | orderedComplexity n vector ≤ budget} degree

private theorem newVertices_card_eq_shell (n budget : Nat) :
    (BooleanCube.Face.newVertices {vector | orderedComplexity n vector ≤ budget}
      {vector | orderedComplexity n vector ≤ budget + n}).card = (complexityShell n budget).card := by
  classical
  let vertices := BooleanCube.Face.newVertices {vector | orderedComplexity n vector ≤ budget}
    {vector | orderedComplexity n vector ≤ budget + n}
  have equal : vertices.map (truthTableEquiv n).toEmbedding = complexityShell n budget := by
    ext function
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, mem_complexityShell]
    constructor
    · rintro ⟨vector, member, rfl⟩
      have h := (BooleanCube.Face.mem_newVertices _ _ _).mp member
      exact ⟨by simpa [orderedComplexity] using h.2, h.1⟩
    · intro member
      refine ⟨(truthTableEquiv n).symm function, ?_, (truthTableEquiv n).apply_symm_apply function⟩
      apply (BooleanCube.Face.mem_newVertices _ _ _).mpr
      simpa [orderedComplexity] using And.intro member.2 (Nat.not_le.mpr member.1)
  simpa only [Finset.card_map] using congrArg Finset.card equal

/-- Positive-dimensional topology forces functions in the next `n` complexity levels. -/
theorem cubicalBetti_le_choose_mul_shell (K : Type*) [Field K] (positive : 0 < n)
    (budget degree : Nat) (degreePositive : 0 < degree) :
    cubicalBetti K n budget degree ≤
      (2 ^ n).choose (degree + 1) * (complexityShell n budget).card := by
  have bound := BooleanCube.CubicalHomology.betti_le_choose_mul_card_new_vertices K
    {vector | orderedComplexity n vector ≤ budget}
    {vector | orderedComplexity n vector ≤ budget + n} degree degreePositive
    (fun _ h => h.trans (Nat.le_add_right _ _))
    (fun threshold vector h => (orderedComplexity_erase_le positive threshold vector).trans
      (Nat.add_le_add_right h n))
  rwa [newVertices_card_eq_shell] at bound

end Algebraic.DeMorgan
