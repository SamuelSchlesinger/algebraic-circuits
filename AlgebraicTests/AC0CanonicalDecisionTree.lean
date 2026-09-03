import Algebraic.LowerBound.AC0.CanonicalDecisionTree

/-!
# AC0 canonical-decision-tree regression tests
-/

namespace AlgebraicTests.AC0CanonicalDecisionTree

open Algebraic
open Algebraic.AC0

def firstTerm : Term 3 :=
  ⟨fun index =>
    if index = 0 then some true
    else if index = 1 then some true
    else none⟩

def secondTerm : Term 3 :=
  ⟨fun index =>
    if index = 0 then some false
    else if index = 2 then some true
    else none⟩

def exampleDNF : DNF 3 :=
  ⟨[firstTerm, secondTerm]⟩

example :
    (exampleDNF.canonicalDecisionTree PartialAssignment.empty).Computes
      exampleDNF.eval :=
  exampleDNF.canonicalDecisionTree_empty_computes

example (rho : PartialAssignment 3) :
    exampleDNF.canonicalDepth rho ≤ rho.liveCount :=
  exampleDNF.canonicalDepth_le_liveCount rho

example (rho : PartialAssignment 3) :
    DecisionTree.DepthAtMost (exampleDNF.restrict rho).eval
      (exampleDNF.canonicalDepth rho) :=
  exampleDNF.depthAtMost_restrict_canonical rho

example (rho : PartialAssignment 3) (threshold : Nat) :
    Decidable (exampleDNF.CanonicalDepthAtLeast rho threshold) :=
  inferInstance

example
    (rho : PartialAssignment 3)
    (threshold : Nat)
    (lower : DecisionTree.DepthAtLeast
      (exampleDNF.restrict rho).eval threshold) :
    exampleDNF.CanonicalDepthAtLeast rho threshold :=
  exampleDNF.canonicalDepthAtLeast_of_depthAtLeast rho threshold lower

example
    (rho : PartialAssignment 3)
    (length : Nat)
    (deep : exampleDNF.CanonicalDepthAtLeast rho length) :
    Nonempty (DNF.CanonicalPath exampleDNF rho length) :=
  exampleDNF.exists_canonicalPath rho length deep

example
    {rho : PartialAssignment 3}
    {length : Nat}
    (path : DNF.CanonicalPath exampleDNF rho length) :
    (DecisionTree.PathStep.assignment path.steps).fixedCount = length ∧
      (DecisionTree.PathStep.assignment path.steps).fixedVariables ⊆
        rho.liveVariables :=
  ⟨path.assignment_fixedCount, path.assignment_fixesOnlyLive⟩

example
    {rho : PartialAssignment 3}
    {steps : List (DecisionTree.PathStep 3)}
    {endpoint : DecisionTree 3}
    (path : DecisionTree.Path
      (exampleDNF.canonicalDecisionTree rho) steps endpoint) :
    Nonempty (DNF.CanonicalTrace exampleDNF rho steps) :=
  exampleDNF.canonicalTrace_of_path rho path

end AlgebraicTests.AC0CanonicalDecisionTree
