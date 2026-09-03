import Algebraic.LowerBound.AC0.DecisionTree

/-!
# Canonical decision trees for DNF formulas

This module formalizes the dynamic canonical decision tree used in the
decision-tree form of Hastad's switching lemma. At each partial assignment it
restricts the whole DNF, selects the first surviving term, and queries every
remaining variable of that term in input-coordinate order. A satisfying
branch returns `true`; every other branch repeats the construction after the
new assignments have simplified the entire formula.

The recursion is structural in the number of live variables. It is not an
optimal-tree search. The distinguished tree makes the eventual switching
event concrete and decidable while its correctness gives an ordinary
existential decision-tree depth bound as a corollary.
-/

namespace Algebraic
namespace AC0

namespace LiteralSet

/-- The support of a literal set in the canonical input-coordinate order. -/
def orderedSupport (set : LiteralSet n) : List (Fin n) :=
  (List.finRange n).filter fun index => index ∈ set.support

@[simp] theorem mem_orderedSupport
    (set : LiteralSet n)
    (index : Fin n) :
    index ∈ set.orderedSupport ↔ index ∈ set.support := by
  simp [orderedSupport]

/-- Canonical support lists contain no repeated coordinate. -/
theorem nodup_orderedSupport (set : LiteralSet n) :
    set.orderedSupport.Nodup := by
  exact (List.nodup_finRange n).filter _

end LiteralSet

namespace DNF

/-- Every term returned by DNF restriction uses only variables left live by
the restriction. -/
theorem support_subset_live_of_mem_restrict
    (formula : DNF n)
    (rho : PartialAssignment n)
    {term : Term n}
    (present : term ∈ (formula.restrict rho).terms) :
    term.support ⊆ rho.liveVariables := by
  obtain ⟨source, _, restricted⟩ := List.mem_filterMap.1 present
  by_cases conflict : source.ConflictsWith rho
  · simp [Term.restrict, conflict] at restricted
  · rw [Term.restrict, if_neg conflict] at restricted
    injection restricted with equal
    subst term
    exact LiteralSet.support_residual_subset_live source rho

private def queryRemainingBelow
    (indices : List (Fin n))
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n) : DecisionTree n :=
  match indices with
  | [] => recurse rho below
  | index :: rest =>
      .query index
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index false)) bound
          ((PartialAssignment.liveCount_refine_le_left rho
            (PartialAssignment.fix index false)).trans_lt below)
          recurse)
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index true)) bound
          ((PartialAssignment.liveCount_refine_le_left rho
            (PartialAssignment.fix index true)).trans_lt below)
          recurse)

private theorem queryRemainingBelow_computes
    (formula : DNF n)
    (indices : List (Fin n))
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n)
    (nodup : indices.Nodup)
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (recurseComputes : ∀ sigma below,
      (recurse sigma below).Computes
        fun input => formula.eval (sigma.apply input)) :
    (queryRemainingBelow indices rho bound below recurse).Computes
      fun input => formula.eval (rho.apply input) := by
  induction indices generalizing rho with
  | nil =>
      exact recurseComputes rho below
  | cons index rest inductionHypothesis =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have tailLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedTailLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, tailLive current currentPresent,
          PartialAssignment.fix, different]
      have falseComputes := inductionHypothesis
        (rho.refine (PartialAssignment.fix index false))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index false)).trans_lt below)
        restNodup (refinedTailLive false)
      have trueComputes := inductionHypothesis
        (rho.refine (PartialAssignment.fix index true))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index true)).trans_lt below)
        restNodup (refinedTailLive true)
      intro input
      cases inputValue : input index with
      | false =>
          simp only [queryRemainingBelow, DecisionTree.eval_query, inputValue,
            Bool.false_eq_true, if_false]
          rw [falseComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index false)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index false inputValue]
      | true =>
          simp only [queryRemainingBelow, DecisionTree.eval_query, inputValue,
            if_true]
          rw [trueComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index true)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index true inputValue]

private theorem depth_queryRemainingBelow_le_liveCount
    (indices : List (Fin n))
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n)
    (nodup : indices.Nodup)
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (recurseDepth : ∀ sigma below,
      (recurse sigma below).depth ≤ sigma.liveCount) :
    (queryRemainingBelow indices rho bound below recurse).depth ≤
      rho.liveCount := by
  induction indices generalizing rho with
  | nil =>
      simpa [queryRemainingBelow] using recurseDepth rho below
  | cons index rest inductionHypothesis =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseBound := inductionHypothesis
        (rho.refine (PartialAssignment.fix index false))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index false)).trans_lt below)
        restNodup (refinedRestLive false)
      have trueBound := inductionHypothesis
        (rho.refine (PartialAssignment.fix index true))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index true)).trans_lt below)
        restNodup (refinedRestLive true)
      have falseDecrease :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index false indexLive
      have trueDecrease :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index true indexLive
      simp only [queryRemainingBelow, DecisionTree.depth_query]
      omega

private def canonicalSupportStep
    (_formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none) :
    DecisionTree n :=
  match indices with
  | [] => .leaf true
  | index :: rest =>
      have indexLive : rho index = none := allLive index (by simp)
      .query index
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index false)) rho.liveCount
          (PartialAssignment.liveCount_refine_fix_lt_of_live
            rho index false indexLive)
          recurse)
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index true)) rho.liveCount
          (PartialAssignment.liveCount_refine_fix_lt_of_live
            rho index true indexLive)
          recurse)

private def canonicalTermsStep
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (terms : List (Term n))
    (supportLive : ∀ term, term ∈ terms →
      term.support ⊆ rho.liveVariables) : DecisionTree n :=
  match terms with
  | [] => .leaf false
  | term :: _ =>
      canonicalSupportStep formula rho recurse term.orderedSupport fun index
          present => by
        rw [← PartialAssignment.mem_liveVariables]
        apply supportLive term (by simp)
        exact (LiteralSet.mem_orderedSupport term index).1 present

private def canonicalDecisionTreeStep
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n) : DecisionTree n :=
  canonicalTermsStep formula rho recurse (formula.restrict rho).terms
    fun _ present => support_subset_live_of_mem_restrict formula rho present

private theorem depth_canonicalSupportStep_le_liveCount
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (nodup : indices.Nodup)
    (recurseDepth : ∀ sigma below,
      (recurse sigma below).depth ≤ sigma.liveCount) :
    (canonicalSupportStep formula rho recurse indices allLive).depth ≤
      rho.liveCount := by
  cases indices with
  | nil => simp [canonicalSupportStep]
  | cons index rest =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index false indexLive
      have trueBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index true indexLive
      have falseBound := depth_queryRemainingBelow_le_liveCount
        rest (rho.refine (PartialAssignment.fix index false)) rho.liveCount
        falseBelow recurse restNodup (refinedRestLive false) recurseDepth
      have trueBound := depth_queryRemainingBelow_le_liveCount
        rest (rho.refine (PartialAssignment.fix index true)) rho.liveCount
        trueBelow recurse restNodup (refinedRestLive true) recurseDepth
      simp only [canonicalSupportStep, DecisionTree.depth_query]
      omega

private theorem depth_canonicalTermsStep_le_liveCount
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (terms : List (Term n))
    (supportLive : ∀ term, term ∈ terms →
      term.support ⊆ rho.liveVariables)
    (recurseDepth : ∀ sigma below,
      (recurse sigma below).depth ≤ sigma.liveCount) :
    (canonicalTermsStep formula rho recurse terms supportLive).depth ≤
      rho.liveCount := by
  cases terms with
  | nil => simp [canonicalTermsStep]
  | cons term rest =>
      have allLive : ∀ index, index ∈ term.orderedSupport →
          rho index = none := by
        intro index present
        rw [← PartialAssignment.mem_liveVariables]
        apply supportLive term (by simp)
        exact (LiteralSet.mem_orderedSupport term index).1 present
      simpa only [canonicalTermsStep] using
        depth_canonicalSupportStep_le_liveCount formula rho recurse
          term.orderedSupport allLive
          (LiteralSet.nodup_orderedSupport term) recurseDepth

private theorem canonicalSupportStep_computes
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (nodup : indices.Nodup)
    (recurseComputes : ∀ sigma below,
      (recurse sigma below).Computes
        fun input => formula.eval (sigma.apply input))
    (emptyTrue : indices = [] → ∀ input,
      formula.eval (rho.apply input) = true) :
    (canonicalSupportStep formula rho recurse indices allLive).Computes
      fun input => formula.eval (rho.apply input) := by
  cases indices with
  | nil =>
      intro input
      simpa [canonicalSupportStep] using (emptyTrue rfl input).symm
  | cons index rest =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index false indexLive
      have trueBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index true indexLive
      have falseComputes := queryRemainingBelow_computes
        formula rest (rho.refine (PartialAssignment.fix index false))
        rho.liveCount falseBelow recurse restNodup
        (refinedRestLive false) recurseComputes
      have trueComputes := queryRemainingBelow_computes
        formula rest (rho.refine (PartialAssignment.fix index true))
        rho.liveCount trueBelow recurse restNodup
        (refinedRestLive true) recurseComputes
      intro input
      simp only [canonicalSupportStep, DecisionTree.eval_query]
      cases inputValue : input index with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [falseComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index false)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index false inputValue]
      | true =>
          simp only [if_true]
          rw [trueComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index true)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index true inputValue]

private theorem canonicalTermsStep_computes
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (terms : List (Term n))
    (supportLive : ∀ term, term ∈ terms →
      term.support ⊆ rho.liveVariables)
    (recurseComputes : ∀ sigma below,
      (recurse sigma below).Computes
        fun input => formula.eval (sigma.apply input))
    (semantics : ∀ input,
      ({ terms := terms } : DNF n).eval input =
        formula.eval (rho.apply input)) :
    (canonicalTermsStep formula rho recurse terms supportLive).Computes
      fun input => formula.eval (rho.apply input) := by
  cases terms with
  | nil =>
      intro input
      simp only [canonicalTermsStep, DecisionTree.eval_leaf]
      rw [← semantics input]
      rfl
  | cons term rest =>
      apply canonicalSupportStep_computes
      · exact LiteralSet.nodup_orderedSupport term
      · exact recurseComputes
      · intro supportEmpty input
        rw [← semantics input]
        have termTrue : Term.eval term input = true := by
          apply (Term.eval_eq_true term input).2
          intro index value required
          have supportPresent : index ∈ term.support :=
            (LiteralSet.mem_support term index).2 (by simp [required])
          have orderedPresent : index ∈ term.orderedSupport :=
            (LiteralSet.mem_orderedSupport term index).2 supportPresent
          rw [supportEmpty] at orderedPresent
          simp at orderedPresent
        simp [DNF.eval, termTrue]

/-- The canonical decision tree of `formula` below a partial assignment.

The whole formula is freshly restricted between queried terms. Hence later
term selection incorporates every assignment made along the current branch.
-/
def canonicalDecisionTree
    (formula : DNF n)
    (rho : PartialAssignment n) : DecisionTree n :=
  canonicalDecisionTreeStep formula rho fun sigma _ =>
    canonicalDecisionTree formula sigma
termination_by rho.liveCount

/-- The canonical tree computes exactly the DNF under the supplied partial
assignment. -/
theorem canonicalDecisionTree_computes
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.canonicalDecisionTree rho).Computes
      fun input => formula.eval (rho.apply input) := by
  induction rho using
      (invImage PartialAssignment.liveCount Nat.lt_wfRel).wf.induction with
  | h rho inductionHypothesis =>
      rw [canonicalDecisionTree.eq_def]
      unfold canonicalDecisionTreeStep
      apply canonicalTermsStep_computes
      · intro sigma below
        exact inductionHypothesis sigma below
      · exact restrict_sound formula rho

/-- The canonical tree never queries more coordinates than remain live. -/
theorem depth_canonicalDecisionTree_le_liveCount
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.canonicalDecisionTree rho).depth ≤ rho.liveCount := by
  induction rho using
      (invImage PartialAssignment.liveCount Nat.lt_wfRel).wf.induction with
  | h rho inductionHypothesis =>
      rw [canonicalDecisionTree.eq_def]
      unfold canonicalDecisionTreeStep
      apply depth_canonicalTermsStep_le_liveCount
      intro sigma below
      exact inductionHypothesis sigma below

/-- The numeric depth of the distinguished canonical tree. -/
def canonicalDepth
    (formula : DNF n)
    (rho : PartialAssignment n) : Nat :=
  (formula.canonicalDecisionTree rho).depth

/-- Canonical depth is bounded by the number of live variables. -/
theorem canonicalDepth_le_liveCount
    (formula : DNF n)
    (rho : PartialAssignment n) :
    formula.canonicalDepth rho ≤ rho.liveCount :=
  depth_canonicalDecisionTree_le_liveCount formula rho

/-- The concrete bad event counted by the canonical switching argument. -/
def CanonicalDepthAtLeast
    (formula : DNF n)
    (rho : PartialAssignment n)
    (threshold : Nat) : Prop :=
  threshold ≤ formula.canonicalDepth rho

instance canonicalDepthAtLeastDecidable
    (formula : DNF n)
    (rho : PartialAssignment n)
    (threshold : Nat) :
    Decidable (formula.CanonicalDepthAtLeast rho threshold) :=
  by
    unfold CanonicalDepthAtLeast canonicalDepth
    infer_instance

/-- The canonical tree also computes the syntactically restricted DNF. -/
theorem canonicalDecisionTree_computes_restrict
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.canonicalDecisionTree rho).Computes
      (formula.restrict rho).eval := by
  intro input
  calc
    (formula.canonicalDecisionTree rho).eval input =
        formula.eval (rho.apply input) :=
      formula.canonicalDecisionTree_computes rho input
    _ = (formula.restrict rho).eval input :=
      (restrict_sound formula rho input).symm

/-- The canonical tree witnesses an ordinary decision-tree upper bound for the
restricted DNF. -/
theorem depthAtMost_restrict_canonical
    (formula : DNF n)
    (rho : PartialAssignment n) :
    DecisionTree.DepthAtMost (formula.restrict rho).eval
      (formula.canonicalDepth rho) :=
  ⟨formula.canonicalDecisionTree rho,
    formula.canonicalDecisionTree_computes_restrict rho, le_rfl⟩

/-- If every tree for the restricted function has depth at least `threshold`,
then the canonical tree does too. This relates the concrete switching event to
the representation-independent lower-depth predicate. -/
theorem canonicalDepthAtLeast_of_depthAtLeast
    (formula : DNF n)
    (rho : PartialAssignment n)
    (threshold : Nat)
    (lower : DecisionTree.DepthAtLeast
      (formula.restrict rho).eval threshold) :
    formula.CanonicalDepthAtLeast rho threshold := by
  exact lower (formula.canonicalDecisionTree rho)
    (formula.canonicalDecisionTree_computes_restrict rho)

/-- At the empty restriction, the canonical tree computes the original DNF. -/
theorem canonicalDecisionTree_empty_computes
    (formula : DNF n) :
    (formula.canonicalDecisionTree PartialAssignment.empty).Computes
      formula.eval := by
  simpa using formula.canonicalDecisionTree_computes
    (PartialAssignment.empty : PartialAssignment n)

end DNF

end AC0
end Algebraic
