import Algebraic.Basis.AC0.Restriction

/-!
# AC0 partial-evaluation regression tests
-/

namespace AlgebraicTests.AC0Restriction

open Algebraic
open Algebraic.AC0

example
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool) :
    (simplifyConnective connective values).eval program input =
      connective.eval (fun argument =>
        (values argument).eval program input) :=
  simplifyConnective_eval connective values program input

example
    (connective : Connective)
    (values : Fin r -> ResidualValue n g) :
    (simplifyConnective connective values).cost <= 1 :=
  ConnectiveReduction.cost_le_one _

def forcedAndArguments : Fin 2 -> ResidualValue 1 0
  | 0 => .constant false
  | 1 => .wire (Wire.input 0)

example :
    simplifyConnective .and forcedAndArguments =
      .value (.constant false) := by
  simp [simplifyConnective, forcedAndArguments, Connective.absorbing]

def neutralOrArguments : Fin 2 -> ResidualValue 1 0
  | 0 => .constant false
  | 1 => .wire (Wire.input 0)

example : residualWires neutralOrArguments = [Wire.input 0] := by
  decide

end AlgebraicTests.AC0Restriction
