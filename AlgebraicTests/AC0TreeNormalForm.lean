import Algebraic.LowerBound.AC0.TreeNormalForm

/-!
# Decision-tree normal-form regression tests
-/

namespace AlgebraicTests.AC0TreeNormalForm

open Algebraic
open Algebraic.AC0

example
    (tree : DecisionTree n)
    (input : Fin n -> Bool) :
    tree.toDNF.eval input = tree.eval input := by
  simp

example
    (tree : DecisionTree n) :
    tree.toDNF.WidthAtMost tree.depth :=
  DecisionTree.widthAtMost_toDNF tree

example
    (tree : DecisionTree n)
    (input : Fin n -> Bool) :
    tree.toCNF.eval input = tree.eval input := by
  simp

example
    (tree : DecisionTree n) :
    tree.toCNF.WidthAtMost tree.depth :=
  DecisionTree.widthAtMost_toCNF tree

example
    (function : ScalarFunction Bool n)
    (bound : Nat)
    (bounded : DecisionTree.DepthAtMost function bound) :
    Exists fun formula : DNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input = function input :=
  DecisionTree.exists_dnf_widthAtMost_of_depthAtMost bounded

example
    (function : ScalarFunction Bool n)
    (bound : Nat)
    (bounded : DecisionTree.DepthAtMost function bound) :
    Exists fun formula : CNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input = function input :=
  DecisionTree.exists_cnf_widthAtMost_of_depthAtMost bounded

/-- The sole accepting syntactic path asks the same variable to be both false
and true, so the structural conversion must discard it. -/
def contradictoryRepeatedQuery : DecisionTree 1 :=
  .query 0
    (.query 0 (.leaf false) (.leaf true))
    (.leaf false)

example : contradictoryRepeatedQuery.toDNF = DNF.bottom := by
  rfl

end AlgebraicTests.AC0TreeNormalForm
