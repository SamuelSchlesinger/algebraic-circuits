import Algebraic.Basis.DeMorgan.Threshold
import Algebraic.BooleanCube.Sweep
import Algebraic.BooleanCube.Boundary

/-!
# Circuit complexity along truth-table paths

Ordered prefix erasure costs at most `n` gates. This joins all functions
already within budget `s` inside budget `s + n`. Passing through the
pointwise conjunction instead gives a shortest Hamming path at budget
`C(f) + C(g) + n + 1`. The cost counts all internal De Morgan gates.
-/

namespace Algebraic.DeMorgan

/-- A compiled expression upper-bounds the complexity of its semantics. -/
theorem complexity_expression_le (expression : Expression n) :
    complexity expression.eval ≤ expression.gateCount := by
  apply complexity_le expression.circuit
  intro input
  funext output
  have equal : output = 0 := Subsingleton.elim _ _
  simp [equal]

private theorem complexity_binary_le (left right : ScalarFunction Bool n) (useOr : Bool) :
    complexity (fun input => if useOr then left input || right input
      else left input && right input) ≤ complexity left + complexity right + 1 := by
  let operation : Expression 2 :=
    if useOr then .or (.input 0) (.input 1) else .and (.input 0) (.input 1)
  let result := operation.circuit.comp
    ((minimumCircuit left).circuit.parallel (minimumCircuit right).circuit)
  have computes : result.ComputesWith interpretation
      (fun input _ => if useOr then left input || right input else left input && right input) := by
    intro input
    funext output
    have outputZero : output = 0 := Subsingleton.elim _ _
    rw [outputZero]
    dsimp only [result]
    rw [Circuit.eval_comp, Expression.circuit_eval, Circuit.eval_parallel]
    have l : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (0 : Fin 2) = left input :=
      congrFun ((minimumCircuit left).computes input) 0
    have r : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (1 : Fin 2) = right input :=
      congrFun ((minimumCircuit right).computes input) 0
    cases useOr <;> simp [operation, Expression.eval, l, r]
  have bound := complexity_le result computes
  cases useOr <;> simpa [result, operation, complexity, Expression.gateCount] using bound

/-- Conjunction uses each source circuit once and adds one gate. -/
theorem complexity_and_le (left right : ScalarFunction Bool n) :
    complexity (fun input => left input && right input) ≤
      complexity left + complexity right + 1 := by
  simpa using complexity_binary_le left right false

/-- Disjunction uses each source circuit once and adds one gate. -/
theorem complexity_or_le (left right : ScalarFunction Bool n) :
    complexity (fun input => left input || right input) ≤
      complexity left + complexity right + 1 := by
  simpa using complexity_binary_le left right true

/-- Erasing any numerical prefix of a truth table costs at most `n` extra gates. -/
theorem complexity_erase_le (positive : 0 < n) (function : ScalarFunction Bool n)
    (threshold : Nat) :
    complexity (BooleanCube.erase inputRank threshold function) ≤ complexity function + n := by
  by_cases zero : threshold = 0
  · simp [zero, BooleanCube.erase]
  by_cases beyond : 2 ^ n ≤ threshold
  · have erased : BooleanCube.erase inputRank threshold function = fun _ => false := by
      funext input
      have h := inputRank_lt input
      simp [BooleanCube.erase, BooleanCube.patch, show inputRank input < threshold by omega]
    rw [erased]
    have := complexity_constant_le n false
    omega
  · let test := thresholdExpression n threshold
    have testBound := thresholdExpression_gateCount_le (n := n) threshold (by omega) (by omega)
    have testComplexity := complexity_expression_le test
    have mask : BooleanCube.erase inputRank threshold function =
        fun input => function input && test.eval input := by
      funext input
      dsimp only [test]
      rw [thresholdExpression_eval]
      by_cases before : inputRank input < threshold
      · simp [BooleanCube.erase, BooleanCube.patch, before, not_le.mpr before]
      · simp [BooleanCube.erase, BooleanCube.patch, before, Nat.le_of_not_gt before]
    rw [mask]
    have joined := complexity_and_le function test.eval
    dsimp only [test] at testComplexity joined ⊢
    omega

/-- Every function has a budgeted shortest path to the zero truth table. -/
theorem exists_erase_path (positive : 0 < n) (function : ScalarFunction Bool n) :
    ∃ walk : BooleanCube.graph.Walk function (fun _ => false),
      walk.IsPath ∧ BooleanCube.Within complexity (complexity function + n) walk ∧
        walk.length = hammingDist function (fun _ => false) := by
  obtain ⟨walk, bounded, length⟩ := BooleanCube.exists_patch_walk inputRank inputRank_injective
    (2 ^ n) inputRank_lt function (fun _ => false) complexity (complexity function + n)
    (fun threshold _ => complexity_erase_le positive function threshold)
  exact ⟨walk, BooleanCube.isPath_of_length_eq_hammingDist walk length, bounded, length⟩

/-- Any two functions connect with at most `n` gates beyond their larger complexity. -/
theorem exists_connecting_walk (positive : 0 < n) (left right : ScalarFunction Bool n) :
    ∃ walk : BooleanCube.graph.Walk left right,
      BooleanCube.Within complexity (max (complexity left) (complexity right) + n) walk := by
  obtain ⟨first, _, firstBound, _⟩ := exists_erase_path positive left
  obtain ⟨second, _, secondBound, _⟩ := exists_erase_path positive right
  refine ⟨first.append second.reverse, BooleanCube.Within.append ?_ ?_⟩
  · intro vector member
    exact (firstBound vector member).trans (Nat.add_le_add_right (le_max_left _ _) n)
  · apply BooleanCube.Within.reverse
    intro vector member
    exact (secondBound vector member).trans (Nat.add_le_add_right (le_max_right _ _) n)

/-- Remove loops from the erasure walk without increasing its circuit budget. -/
theorem exists_connecting_path (positive : 0 < n) (left right : ScalarFunction Bool n) :
    ∃ path : BooleanCube.graph.Walk left right,
      path.IsPath ∧
        BooleanCube.Within complexity (max (complexity left) (complexity right) + n) path := by
  classical
  obtain ⟨walk, bounded⟩ := exists_connecting_walk positive left right
  refine ⟨walk.bypass, walk.bypass_isPath, ?_⟩
  intro vector member
  exact bounded vector (walk.support_bypass_sublist_support.subset member)

/-- Every two vertices already at budget `s` join by a simple path at budget `s+n`. -/
theorem exists_connecting_path_of_complexity_le (positive : 0 < n)
    (left right : ScalarFunction Bool n) (budget : Nat)
    (leftBound : complexity left ≤ budget) (rightBound : complexity right ≤ budget) :
    ∃ path : BooleanCube.graph.Walk left right,
      path.IsPath ∧ BooleanCube.Within complexity (budget + n) path := by
  obtain ⟨path, simple, bounded⟩ := exists_connecting_path positive left right
  refine ⟨path, simple, ?_⟩
  intro vector member
  have := bounded vector member
  omega

private theorem complexity_patch_meet_le (positive : 0 < n)
    (left right : ScalarFunction Bool n) (threshold : Nat) :
    complexity (BooleanCube.patch inputRank left (fun input => left input && right input)
      threshold) ≤ complexity left + complexity right + n + 1 := by
  by_cases zero : threshold = 0
  · simp only [zero, BooleanCube.patch_zero]
    omega
  by_cases beyond : 2 ^ n ≤ threshold
  · have patched : BooleanCube.patch inputRank left
        (fun input => left input && right input) threshold =
        fun input => left input && right input := by
      funext input
      have h := inputRank_lt input
      simp [BooleanCube.patch, show inputRank input < threshold by omega]
    rw [patched]
    have := complexity_and_le left right
    omega
  · let test := thresholdExpression n threshold
    have testBound := thresholdExpression_gateCount_le (n := n) threshold (by omega) (by omega)
    have testComplexity := complexity_expression_le test
    have disjunction := complexity_or_le right test.eval
    have conjunction := complexity_and_le left (fun input => right input || test.eval input)
    have patched : BooleanCube.patch inputRank left
        (fun input => left input && right input) threshold =
        fun input => left input && (right input || test.eval input) := by
      funext input
      dsimp only [test]
      rw [thresholdExpression_eval]
      by_cases before : inputRank input < threshold
      · simp [BooleanCube.patch, before, not_le.mpr before]
      · simp [BooleanCube.patch, before, Nat.le_of_not_gt before]
    rw [patched]
    dsimp only [test] at testComplexity disjunction conjunction ⊢
    omega

/-- Any pair has a shortest Hamming path at the sum of its circuit costs plus `n + 1`. -/
theorem exists_geodesic (positive : 0 < n) (left right : ScalarFunction Bool n) :
    ∃ walk : BooleanCube.graph.Walk left right,
      walk.IsPath ∧
        BooleanCube.Within complexity (complexity left + complexity right + n + 1) walk ∧
          walk.length = hammingDist left right := by
  let middle : ScalarFunction Bool n := fun input => left input && right input
  obtain ⟨first, firstBound, firstLength⟩ := BooleanCube.exists_patch_walk inputRank
    inputRank_injective (2 ^ n) inputRank_lt left middle complexity
    (complexity left + complexity right + n + 1)
    (fun threshold _ => complexity_patch_meet_le positive left right threshold)
  have otherBound : ∀ threshold, complexity (BooleanCube.patch inputRank right middle threshold) ≤
      complexity left + complexity right + n + 1 := by
    intro threshold
    simpa [middle, Bool.and_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      complexity_patch_meet_le positive right left threshold
  obtain ⟨second, secondBound, secondLength⟩ := BooleanCube.exists_patch_walk inputRank
    inputRank_injective (2 ^ n) inputRank_lt right middle complexity
    (complexity left + complexity right + n + 1) (fun threshold _ => otherBound threshold)
  let walk := first.append second.reverse
  have length : walk.length = hammingDist left right := by
    have metric := BooleanCube.hammingDist_eq_add_of_agree left middle right (by
      intro input equal
      simp [middle, equal])
    simp only [walk, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      firstLength, secondLength]
    rw [hammingDist_comm right middle]
    exact metric.symm
  exact ⟨walk, BooleanCube.isPath_of_length_eq_hammingDist walk length,
    firstBound.append secondBound.reverse, length⟩

/-- A common size budget yields a shortest path after increasing it to `2*s+n+1`. -/
theorem exists_geodesic_of_complexity_le (positive : 0 < n)
    (left right : ScalarFunction Bool n) (budget : Nat)
    (leftBound : complexity left ≤ budget) (rightBound : complexity right ≤ budget) :
    ∃ walk : BooleanCube.graph.Walk left right,
      walk.IsPath ∧ BooleanCube.Within complexity (2 * budget + n + 1) walk ∧
        walk.length = hammingDist left right := by
  obtain ⟨walk, path, bounded, length⟩ := exists_geodesic positive left right
  refine ⟨walk, path, ?_, length⟩
  intro vector member
  have := bounded vector member
  omega

end Algebraic.DeMorgan
