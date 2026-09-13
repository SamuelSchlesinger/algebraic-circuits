import Algebraic.BooleanCube.Star
import Algebraic.Basis.DeMorgan.Geometry

/-!
# First contact of the constant stars

The first common point of the constant-zero and constant-one closed stars
controls worst-case native gate complexity: `M(n) <= 2*tau(n)+2`.
A coordinate projection gives the converse bound `tau(n+1) <= M(n)+1`.
All gates, including constants and negations, are counted; output wires are free.
-/

namespace Algebraic.DeMorgan

/-- Negating the output of a shared circuit adds exactly one gate. -/
theorem complexity_not_le (function : ScalarFunction Bool n) :
    complexity (fun input => !(function input)) ≤ complexity function + 1 := by
  let operation : Expression 1 := .not (.input 0)
  let result := operation.circuit.comp (minimumCircuit function).circuit
  have computes : result.ComputesWith interpretation (fun input _ => !(function input)) := by
    intro input
    funext output
    have equal : output = 0 := Subsingleton.elim _ _
    simp [result, Circuit.eval_comp, Expression.circuit_eval, operation, Expression.eval,
      (minimumCircuit function).computes input, equal]
  simpa [result, operation, complexity] using complexity_le result computes

/-- Rewiring input coordinates cannot increase native gate complexity. -/
theorem complexity_mapInputs_le (function : ScalarFunction Bool n) (map : Fin n → Fin m) :
    complexity (fun input => function (input ∘ map)) ≤ complexity function := by
  apply complexity_le ((minimumCircuit function).circuit.mapInputs map)
  intro input
  rw [Circuit.eval_mapInputs]
  exact (minimumCircuit function).computes _

/-- A designated input is a free output, requiring no gates. -/
@[simp] theorem complexity_input (index : Fin n) : complexity (fun input => input index) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact complexity_expression_le (.input index)

/-- Worst-case native gate complexity at a fixed input width. -/
noncomputable def maximumComplexity (n : Nat) : Nat :=
  BooleanCube.maximumCost (@complexity n)

/-- Every Boolean function is bounded by worst-case complexity. -/
theorem complexity_le_maximumComplexity (function : ScalarFunction Bool n) :
    complexity function ≤ maximumComplexity n :=
  BooleanCube.cost_le_maximumCost complexity function

/-- First contact of the two constant closed stars in the circuit filtration. -/
noncomputable def constantStarMeeting (n : Nat) : Nat :=
  BooleanCube.firstMeeting (@complexity n) (fun _ => false) (fun _ => true)

/-- A common star vertex lets every Boolean function be assembled from two budgeted functions. -/
theorem complexity_le_of_constant_star_intersection (budget : Nat)
    {vertex : ScalarFunction Bool n}
    (zero : vertex ∈ BooleanCube.starVertices {f | complexity f ≤ budget} (fun _ => false))
    (one : vertex ∈ BooleanCube.starVertices {f | complexity f ≤ budget} (fun _ => true))
    (function : ScalarFunction Bool n) : complexity function ≤ 2 * budget + 2 := by
  let lower : ScalarFunction Bool n := fun input => function input && vertex input
  let upper : ScalarFunction Bool n := fun input => vertex input || !(function input)
  have lowerBound : complexity lower ≤ budget := by
    apply (BooleanCube.mem_starVertices_iff _ _ _).mp zero lower
    intro input
    cases hf : function input <;> cases hv : vertex input <;> simp [lower, hf, hv]
  have upperBound : complexity upper ≤ budget := by
    apply (BooleanCube.mem_starVertices_iff _ _ _).mp one upper
    intro input
    cases hf : function input <;> cases hv : vertex input <;> simp [upper, hf, hv]
  have identity : (fun input => lower input || !(upper input)) = function := by
    funext input
    cases hf : function input <;> cases hv : vertex input <;> simp [lower, upper, hf, hv]
  have joined := complexity_or_le lower (fun input => !(upper input))
  have negated := complexity_not_le upper
  rw [identity] at joined
  omega

/-- Meeting of the constant stars forces a universal circuit upper bound. -/
theorem maximumComplexity_le_of_constant_star_intersection (budget : Nat)
    (meet : (BooleanCube.closedStar {f : ScalarFunction Bool n | complexity f ≤ budget}
      (fun _ => false) ∩ BooleanCube.closedStar {f | complexity f ≤ budget}
        (fun _ => true)).Nonempty) : maximumComplexity n ≤ 2 * budget + 2 := by
  obtain ⟨vertex, zero, one⟩ := (BooleanCube.closedStar_inter_nonempty_iff _ _ _).mp meet
  apply Finset.sup_le
  intro function _
  exact complexity_le_of_constant_star_intersection budget zero one function

/-- Twice the first contact budget, plus two gates, bounds every circuit complexity. -/
theorem maximumComplexity_le_twice_constantStarMeeting (n : Nat) :
    maximumComplexity n ≤ 2 * constantStarMeeting n + 2 := by
  obtain ⟨vertex, zero, one⟩ := BooleanCube.firstMeeting_spec (@complexity n)
    (fun _ => false) (fun _ => true)
  apply Finset.sup_le
  intro function _
  exact complexity_le_of_constant_star_intersection _ zero one function

/-- Every function supported where the first input is true is a masked smaller function. -/
theorem complexity_le_of_below_input {function : ScalarFunction Bool (n + 1)}
    (below : ∀ input, function input = false ∨ function input = input 0) :
    complexity function ≤ maximumComplexity n + 1 := by
  let residual : ScalarFunction Bool n := fun input => function (Fin.cons true input)
  have identity : (fun input => input 0 && residual (Fin.tail input)) = function := by
    funext input
    rcases below input with zero | same
    · cases head : input 0
      · simp [zero]
      · have restored : Fin.cons true (Fin.tail input) = input := by
          rw [← head, Fin.cons_self_tail]
        simp [residual, restored, zero]
    · cases head : input 0
      · simp [head, same]
      · have restored : Fin.cons true (Fin.tail input) = input := by
          rw [← head, Fin.cons_self_tail]
        simp [head, residual, restored, same]
  have smaller := complexity_mapInputs_le residual Fin.succ
  have joined := complexity_and_le (fun input : Fin (n + 1) → Bool => input 0)
    (fun input => residual (Fin.tail input))
  rw [identity, complexity_input] at joined
  have bound := complexity_le_maximumComplexity residual
  change complexity (fun input => residual (Fin.tail input)) ≤ complexity residual at smaller
  omega

/-- Every function above the first input is a disjunction with a smaller function. -/
theorem complexity_le_of_above_input {function : ScalarFunction Bool (n + 1)}
    (above : ∀ input, function input = true ∨ function input = input 0) :
    complexity function ≤ maximumComplexity n + 1 := by
  let residual : ScalarFunction Bool n := fun input => function (Fin.cons false input)
  have identity : (fun input => input 0 || residual (Fin.tail input)) = function := by
    funext input
    rcases above input with one | same
    · cases head : input 0
      · have restored : Fin.cons false (Fin.tail input) = input := by
          rw [← head, Fin.cons_self_tail]
        simp [residual, restored, one]
      · simp [one]
    · cases head : input 0
      · have restored : Fin.cons false (Fin.tail input) = input := by
          rw [← head, Fin.cons_self_tail]
        simp [head, residual, restored, same]
      · simp [head, same]
  have smaller := complexity_mapInputs_le residual Fin.succ
  have joined := complexity_or_le (fun input : Fin (n + 1) → Bool => input 0)
    (fun input => residual (Fin.tail input))
  rw [identity, complexity_input] at joined
  have bound := complexity_le_maximumComplexity residual
  change complexity (fun input => residual (Fin.tail input)) ≤ complexity residual at smaller
  omega

/-- The first input is a common vertex of the two stars at the smaller-width maximum plus one. -/
theorem input_mem_both_constant_stars (n : Nat) :
    (fun input : Fin (n + 1) → Bool => input 0) ∈
      BooleanCube.starVertices {f | complexity f ≤ maximumComplexity n + 1} (fun _ => false) ∩
      BooleanCube.starVertices {f | complexity f ≤ maximumComplexity n + 1} (fun _ => true) := by
  constructor
  · apply (BooleanCube.mem_starVertices_iff _ _ _).mpr
    intro function below
    exact complexity_le_of_below_input below
  · apply (BooleanCube.mem_starVertices_iff _ _ _).mpr
    intro function above
    exact complexity_le_of_above_input above

/-- First contact is bounded above by the smaller-width worst-case complexity plus one gate. -/
theorem constantStarMeeting_succ_le (n : Nat) :
    constantStarMeeting (n + 1) ≤ maximumComplexity n + 1 := by
  apply (BooleanCube.firstMeeting_le_iff _ _ _ _).mpr
  exact ⟨_, input_mem_both_constant_stars n⟩

end Algebraic.DeMorgan
