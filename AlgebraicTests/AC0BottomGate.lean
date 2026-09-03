import Algebraic.LowerBound.AC0.BottomGate

/-!
# AC0 bottom-gate extraction regression tests
-/

namespace AlgebraicTests.AC0BottomGate

open Algebraic
open Algebraic.AC0

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (wire : Wire n g)
    (depthZero : AC0.Program.logicalWireDepths program wire = 0) :
    Exists fun literal : Literal n =>
      program.wireFunction interpretation wire = literal.eval :=
  AC0.Program.exists_literal_of_logicalWireDepth_zero
    program normal wire depthZero

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : AC0.Program.logicalGateDepths program gate = 1) :
    (AC0.Program.andGateFormula program normal gate operation
      depthOne).WidthAtMost fanIn :=
  AC0.Program.andGateFormula_widthAtMost
    program normal gate operation depthOne

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : AC0.Program.logicalGateDepths program gate = 1)
    (input : Fin n -> Bool) :
    (AC0.Program.andGateFormula program normal gate operation
      depthOne).eval input =
      program.gateFunction interpretation gate input :=
  AC0.Program.andGateFormula_eval
    program normal gate operation depthOne input

example
    (program : Program signature n g)
    (normal : AC0.Program.NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : AC0.Program.logicalGateDepths program gate = 1)
    (input : Fin n -> Bool) :
    (AC0.Program.orGateFormula program normal gate operation
      depthOne).eval input =
      program.gateFunction interpretation gate input :=
  AC0.Program.orGateFormula_eval
    program normal gate operation depthOne input

end AlgebraicTests.AC0BottomGate
