import Algebraic.LowerBound.AC0.NormalForm
import Mathlib.Data.List.FinRange

/-!
# Boolean decision trees

Decision trees query named input coordinates and branch on their Boolean
values. The false branch is stored first. Depth is the largest number of query
nodes on a root-to-leaf path.

The semantic restriction operation removes queries fixed by a partial
assignment and retains live queries. Its correctness and depth monotonicity are
proved structurally. Decision-tree depth bounds are existential propositions;
this module does not compute or search for optimal trees.
-/

namespace Algebraic
namespace AC0

/-- A Boolean decision tree on `n` named input variables. -/
inductive DecisionTree (n : Nat)
  | leaf (value : Bool)
  | query
      (index : Fin n)
      (onFalse : DecisionTree n)
      (onTrue : DecisionTree n)
  deriving DecidableEq

namespace DecisionTree

/-- Evaluate a decision tree on a complete input. -/
def eval : DecisionTree n -> (Fin n -> Bool) -> Bool
  | .leaf value, _ => value
  | .query index onFalse onTrue, input =>
      if input index then onTrue.eval input else onFalse.eval input

@[simp] theorem eval_leaf
    (value : Bool)
    (input : Fin n -> Bool) :
    (leaf value : DecisionTree n).eval input = value := rfl

@[simp] theorem eval_query
    (index : Fin n)
    (onFalse onTrue : DecisionTree n)
    (input : Fin n -> Bool) :
    (query index onFalse onTrue).eval input =
      if input index then onTrue.eval input else onFalse.eval input := rfl

/-- Maximum number of queries on a root-to-leaf path. -/
def depth : DecisionTree n -> Nat
  | .leaf _ => 0
  | .query _ onFalse onTrue =>
      Nat.succ (max onFalse.depth onTrue.depth)

@[simp] theorem depth_leaf (value : Bool) :
    (leaf value : DecisionTree n).depth = 0 := rfl

@[simp] theorem depth_query
    (index : Fin n)
    (onFalse onTrue : DecisionTree n) :
    (query index onFalse onTrue).depth =
      Nat.succ (max onFalse.depth onTrue.depth) := rfl

/-- Number of leaves in a decision tree. -/
def leafCount : DecisionTree n -> Nat
  | .leaf _ => 1
  | .query _ onFalse onTrue => onFalse.leafCount + onTrue.leafCount

@[simp] theorem leafCount_leaf (value : Bool) :
    (leaf value : DecisionTree n).leafCount = 1 := rfl

@[simp] theorem leafCount_query
    (index : Fin n)
    (onFalse onTrue : DecisionTree n) :
    (query index onFalse onTrue).leafCount =
      onFalse.leafCount + onTrue.leafCount := rfl

/-- A tree computes a scalar Boolean function pointwise. -/
def Computes
    (tree : DecisionTree n)
    (function : ScalarFunction Bool n) : Prop :=
  forall input, tree.eval input = function input

/-- Negate every leaf of a decision tree. -/
def negate : DecisionTree n -> DecisionTree n
  | .leaf value => .leaf (!value)
  | .query index onFalse onTrue =>
      .query index onFalse.negate onTrue.negate

@[simp] theorem eval_negate
    (tree : DecisionTree n)
    (input : Fin n -> Bool) :
    tree.negate.eval input = !(tree.eval input) := by
  induction tree with
  | leaf value => rfl
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      cases inputValue : input index <;>
        simp [negate, eval, inputValue, falseHypothesis, trueHypothesis]

@[simp] theorem depth_negate (tree : DecisionTree n) :
    tree.negate.depth = tree.depth := by
  induction tree with
  | leaf value => rfl
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      simp [negate, depth, falseHypothesis, trueHypothesis]

/-- Negating a computing tree computes the pointwise complement. -/
theorem Computes.negate
    {tree : DecisionTree n}
    {function : ScalarFunction Bool n}
    (computes : tree.Computes function) :
    tree.negate.Computes fun input => !(function input) := by
  intro input
  rw [eval_negate, computes]

/-- Restrict a decision tree, selecting a branch at fixed queries and retaining
queries of live variables. Repeated queries are all simplified. -/
def restrict
    (rho : PartialAssignment n) : DecisionTree n -> DecisionTree n
  | .leaf value => .leaf value
  | .query index onFalse onTrue =>
      match rho index with
      | none => .query index (onFalse.restrict rho) (onTrue.restrict rho)
      | some false => onFalse.restrict rho
      | some true => onTrue.restrict rho

/-- Tree restriction agrees exactly with semantic input restriction. -/
@[simp] theorem eval_restrict
    (tree : DecisionTree n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (tree.restrict rho).eval input = tree.eval (rho.apply input) := by
  induction tree with
  | leaf value => rfl
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      cases fixed : rho index with
      | none =>
          cases inputValue : input index <;>
            simp [restrict, eval, fixed, inputValue,
              PartialAssignment.apply, falseHypothesis, trueHypothesis]
      | some value =>
          cases value <;>
            simp [restrict, eval, fixed, PartialAssignment.apply,
              falseHypothesis, trueHypothesis]

/-- Restriction cannot increase decision-tree depth. -/
theorem depth_restrict_le
    (tree : DecisionTree n)
    (rho : PartialAssignment n) :
    (tree.restrict rho).depth ≤ tree.depth := by
  induction tree with
  | leaf value => simp [restrict, depth]
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      cases fixed : rho index with
      | none =>
          simp only [restrict, fixed, depth]
          omega
      | some value =>
          cases value <;>
            simp only [restrict, fixed, depth] <;>
            omega

/-- Sequential semantic restrictions compose structurally on decision trees. -/
theorem restrict_refine
    (tree : DecisionTree n)
    (rho sigma : PartialAssignment n) :
    (tree.restrict rho).restrict sigma =
      tree.restrict (rho.refine sigma) := by
  induction tree with
  | leaf value => rfl
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      cases first : rho index with
      | none =>
          cases second : sigma index with
          | none =>
              simp [restrict, PartialAssignment.refine, first, second,
                falseHypothesis, trueHypothesis]
          | some value =>
              cases value <;>
                simp [restrict, PartialAssignment.refine, first, second,
                  falseHypothesis, trueHypothesis]
      | some value =>
          cases value <;>
            simp [restrict, PartialAssignment.refine, first,
              falseHypothesis, trueHypothesis]

/-- Restricting a computing tree computes the restricted scalar function. -/
theorem Computes.restrict
    {tree : DecisionTree n}
    {function : ScalarFunction Bool n}
    (computes : tree.Computes function)
    (rho : PartialAssignment n) :
    (tree.restrict rho).Computes (function.restrict rho) := by
  intro input
  rw [eval_restrict, ScalarFunction.restrict_apply, computes]

/-- Build the full Shannon decision tree over an ordered list of coordinates.
At the empty list the remaining function is evaluated on the all-false input;
the correctness theorem below states the dependency condition under which that
choice is immaterial. -/
def build :
    (indices : List (Fin n)) ->
    ScalarFunction Bool n -> DecisionTree n
  | [], function => .leaf (function fun _ => false)
  | index :: indices, function =>
      .query index
        (build indices
          (function.restrict (PartialAssignment.fix index false)))
        (build indices
          (function.restrict (PartialAssignment.fix index true)))

/-- The Shannon tree over a list of coordinates has depth at most the length
of that list. -/
theorem depth_build_le_length
    (indices : List (Fin n))
    (function : ScalarFunction Bool n) :
    (build indices function).depth ≤ indices.length := by
  induction indices generalizing function with
  | nil => simp [build]
  | cons index indices inductionHypothesis =>
      have falseBound := inductionHypothesis
        (function.restrict (PartialAssignment.fix index false))
      have trueBound := inductionHypothesis
        (function.restrict (PartialAssignment.fix index true))
      simp only [build, depth, List.length_cons]
      omega

private theorem restrict_fix_dependsOnlyOn_tail
    (function : ScalarFunction Bool n)
    (index : Fin n)
    (indices : List (Fin n))
    (value : Bool)
    (indexAbsent : index ∉ indices)
    (depends : DependsOnlyOn function (index :: indices).toFinset) :
    DependsOnlyOn
      (function.restrict (PartialAssignment.fix index value))
      indices.toFinset := by
  intro left right agree
  apply depends
  intro current present
  simp only [List.mem_toFinset, List.mem_cons] at present
  rcases present with equal | inTail
  · subst current
    simp [PartialAssignment.apply, PartialAssignment.fix]
  · have different : current ≠ index := by
      intro equal
      subst current
      exact indexAbsent inTail
    have live : PartialAssignment.fix index value current = none :=
      PartialAssignment.fix_other index current value different
    rw [PartialAssignment.apply_of_live _ left live,
      PartialAssignment.apply_of_live _ right live]
    exact agree current (by simpa using inTail)

/-- The Shannon tree computes any function that depends only on its duplicate-
free query list. -/
theorem build_computes_of_dependsOnlyOn
    (indices : List (Fin n))
    (function : ScalarFunction Bool n)
    (nodup : indices.Nodup)
    (depends : DependsOnlyOn function indices.toFinset) :
    (build indices function).Computes function := by
  induction indices generalizing function with
  | nil =>
      intro input
      simp only [build, eval_leaf]
      apply depends
      intro index present
      simp at present
  | cons index indices inductionHypothesis =>
      have indexAbsent : index ∉ indices := (List.nodup_cons.mp nodup).1
      have tailNodup : indices.Nodup := (List.nodup_cons.mp nodup).2
      have falseDepends := restrict_fix_dependsOnlyOn_tail
        function index indices false indexAbsent depends
      have trueDepends := restrict_fix_dependsOnlyOn_tail
        function index indices true indexAbsent depends
      have falseComputes := inductionHypothesis
        (function.restrict (PartialAssignment.fix index false))
        tailNodup falseDepends
      have trueComputes := inductionHypothesis
        (function.restrict (PartialAssignment.fix index true))
        tailNodup trueDepends
      intro input
      cases inputValue : input index with
      | false =>
          simp only [build, eval_query, inputValue, Bool.false_eq_true,
            if_false]
          rw [falseComputes input, ScalarFunction.restrict_apply,
            PartialAssignment.apply_fix_eq_self input index false inputValue]
      | true =>
          simp only [build, eval_query, inputValue, if_true]
          rw [trueComputes input, ScalarFunction.restrict_apply,
            PartialAssignment.apply_fix_eq_self input index true inputValue]

/-- A function has decision-tree depth at most `bound` when some computing tree
has depth at most that bound. No minimization procedure is part of this
definition. -/
def DepthAtMost
    (function : ScalarFunction Bool n)
    (bound : Nat) : Prop :=
  Exists fun tree : DecisionTree n =>
    tree.Computes function ∧ tree.depth ≤ bound

/-- Every decision tree computing the function has depth at least `bound`. -/
def DepthAtLeast
    (function : ScalarFunction Bool n)
    (bound : Nat) : Prop :=
  forall tree : DecisionTree n,
    tree.Computes function -> bound ≤ tree.depth

/-- Every `n`-variable Boolean function has a decision tree of depth at most
`n`. This is a structural Shannon expansion, not an optimal-tree search. -/
theorem depthAtMost_inputCount
    (function : ScalarFunction Bool n) :
    DepthAtMost function n := by
  have depends : DependsOnlyOn function (List.finRange n).toFinset := by
    rw [List.toFinset_finRange]
    intro left right agree
    apply congrArg function
    funext index
    exact agree index (Finset.mem_univ index)
  refine ⟨build (List.finRange n) function,
    build_computes_of_dependsOnlyOn
      (List.finRange n) function (List.nodup_finRange n) depends, ?_⟩
  simpa using depth_build_le_length (List.finRange n) function

/-- A larger allowance preserves an upper decision-tree depth bound. -/
theorem DepthAtMost.mono
    {function : ScalarFunction Bool n}
    {smaller larger : Nat}
    (bounded : DepthAtMost function smaller)
    (le : smaller ≤ larger) :
    DepthAtMost function larger := by
  obtain ⟨tree, computes, depthBound⟩ := bounded
  exact ⟨tree, computes, depthBound.trans le⟩

/-- Restriction preserves any upper bound on decision-tree depth. -/
theorem DepthAtMost.restrict
    {function : ScalarFunction Bool n}
    {bound : Nat}
    (bounded : DepthAtMost function bound)
    (rho : PartialAssignment n) :
    DepthAtMost (function.restrict rho) bound := by
  obtain ⟨tree, computes, depthBound⟩ := bounded
  exact ⟨tree.restrict rho, computes.restrict rho,
    (depth_restrict_le tree rho).trans depthBound⟩

/-- Depth at least `bound + 1` is exactly failure to have depth at most
`bound`. -/
theorem depthAtLeast_succ_iff_not_depthAtMost
    (function : ScalarFunction Bool n)
    (bound : Nat) :
    DepthAtLeast function (bound + 1) ↔ ¬DepthAtMost function bound := by
  constructor
  · intro lower upper
    obtain ⟨tree, computes, depthBound⟩ := upper
    have := lower tree computes
    omega
  · intro noUpper tree computes
    by_contra tooShallow
    apply noUpper
    refine ⟨tree, computes, ?_⟩
    omega

/-- A function has depth zero exactly when it is constant. -/
theorem depthAtMost_zero_iff_constant
    (function : ScalarFunction Bool n) :
    DepthAtMost function 0 ↔
      Exists fun value => forall input, function input = value := by
  constructor
  · rintro ⟨tree, computes, depthBound⟩
    cases tree with
    | leaf value =>
        exact ⟨value, fun input => (computes input).symm⟩
    | query index onFalse onTrue =>
        simp at depthBound
  · rintro ⟨value, constant⟩
    refine ⟨.leaf value, ?_, by simp⟩
    intro input
    exact (constant input).symm

end DecisionTree

end AC0
end Algebraic
