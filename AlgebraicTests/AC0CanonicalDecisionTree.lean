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

end AlgebraicTests.AC0CanonicalDecisionTree
