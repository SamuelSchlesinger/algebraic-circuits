import Algebraic.BooleanCube.GraphCycles

/-!
# Input edges as direction pairs

Canonical oriented cube edges are in bijection with the unordered adjacent
pairs of input vertices. This makes link-face counts independent of an
orientation choice.
-/

namespace Algebraic.BooleanCube

/-- Forget the orientation of a canonical input edge. -/
def edgeDirections (edge : GraphCycles.Edge n) : Finset (Fin n → Bool) :=
  {edge.val.1, edgeEnd edge.val}

/-- Canonical input edges have distinct endpoints. -/
theorem edgeEnd_ne (edge : GraphCycles.Edge n) : edge.val.1 ≠ edgeEnd edge.val := by
  intro equal
  have adjacent := hammingDist_edgeEnd edge.property
  simp [equal] at adjacent

/-- Forgetting the orientation keeps exactly two input directions. -/
@[simp] theorem card_edgeDirections (edge : GraphCycles.Edge n) : (edgeDirections edge).card = 2 := by
  simp [edgeDirections, edgeEnd_ne edge]

/-- The false-to-true orientation can be recovered from the unordered endpoint pair. -/
theorem edgeDirections_injective (n : Nat) : Function.Injective (@edgeDirections n) := by
  intro left right equal
  have pairs : ({left.val.1, edgeEnd left.val} : Set (Fin n → Bool)) =
      {right.val.1, edgeEnd right.val} := by
    simpa only [edgeDirections, Finset.coe_pair] using
      congrArg (fun directions : Finset (Fin n → Bool) => (directions : Set (Fin n → Bool))) equal
  have leftFalse : left.val.1 left.val.2 = false := (Finset.mem_filter.mp left.property).2
  have rightFalse : right.val.1 right.val.2 = false := (Finset.mem_filter.mp right.property).2
  rcases Set.pair_eq_pair_iff.mp pairs with ⟨initial, terminal⟩ | ⟨initial, terminal⟩
  · have index : left.val.2 = right.val.2 := by
      by_contra different
      have atIndex := congrFun terminal left.val.2
      simp [edgeEnd, different, ← initial, leftFalse] at atIndex
    exact Subtype.ext (Prod.ext initial index)
  · have index : left.val.2 = right.val.2 := by
      by_contra different
      have atInitial := congrFun initial left.val.2
      have atTerminal := congrFun terminal left.val.2
      simp [edgeEnd, different, leftFalse] at atInitial atTerminal
      simp_all
    have impossible := congrFun initial left.val.2
    rw [edgeEnd, index, Function.update_self] at impossible
    rw [← index, leftFalse] at impossible
    cases impossible

/-- Every adjacent input pair has a canonical orientation. -/
theorem exists_edgeDirections_eq {left right : Fin n → Bool} (adjacent : graph.Adj left right) :
    ∃ edge : GraphCycles.Edge n, edgeDirections edge = {left, right} := by
  obtain ⟨i, rfl⟩ := (adjacent_iff_flip left right).mp adjacent
  cases value : left i
  · refine ⟨⟨(left, i), by simp [edges, value]⟩, ?_⟩
    simp [edgeDirections, edgeEnd, flip, value]
  · refine ⟨⟨(flip left i, i), by simp [edges, flip, value]⟩, ?_⟩
    have endpoint : edgeEnd (flip left i, i) = left := by
      funext j
      by_cases same : j = i <;> simp [edgeEnd, flip, same, value]
    simp [edgeDirections, endpoint, Finset.pair_comm]

end Algebraic.BooleanCube
