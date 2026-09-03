import Algebraic.LowerBound.AC0.Layer

/-!
# Semantic AC0 layer regression tests
-/

namespace AlgebraicTests.AC0Layer

open Algebraic
open Algebraic.AC0
open scoped BigOperators

example
    (program : Program sigma n g)
    (operationCost : OperationCost sigma) :
    program.cost operationCost =
      ∑ gate : Fin g, operationCost (program.lines gate).op :=
  program.cost_eq_sum_lines operationCost

example (program : Program signature n g) :
    (AC0.Program.connectiveGates program).card =
      program.cost AC0.andOrCost :=
  AC0.Program.card_connectiveGates program

example
    (literal : Literal n)
    (input : Fin n -> Bool) :
    literal.decisionTree.eval input = literal.eval input := by
  simp

example (literal : Literal n) :
    literal.decisionTree.depth = 1 := by
  simp

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (rho : PartialAssignment n) :
    AC0.Program.ShallowUpTo program rho 0 1 :=
  AC0.Program.shallowUpTo_zero program normal rho

example
    (program : Program signature n g)
    (rho extension : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound) :
    AC0.Program.ShallowUpTo program (rho.refine extension) level bound :=
  shallow.restrict extension

example
    (program : Program signature n g)
    (gate : Fin g)
    (connective : (program.lines gate).op.connective ≠ none)
    (argument : Fin (AC0.arity (program.lines gate).op)) :
    AC0.Program.logicalWireDepths program
        ((program.lines gate).wires argument) <
      AC0.Program.logicalGateDepths program gate :=
  AC0.Program.argument_logicalWireDepth_lt_gateDepth
    program gate connective argument

end AlgebraicTests.AC0Layer
