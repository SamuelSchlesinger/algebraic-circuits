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
  GateReduction.cost_le_one _

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

example
    (source : Program signature n g)
    (rho : PartialAssignment n)
    (input : Fin rho.liveCount -> Bool)
    (sourceWire : Wire n g) :
    ((restrictProgram rho source).values sourceWire).eval
        (restrictProgram rho source).result input =
      source.trace interpretation
        (rho.toLiveInputSubstitution.apply input) sourceWire :=
  (restrictProgram rho source).trace_eq input sourceWire

example
    (source : Circuit signature n g m)
    (rho : PartialAssignment n) :
    (restrictCircuit source rho).result.cost <=
      source.cost andOrCost :=
  (restrictCircuit source rho).cost_le

example
    (source : Circuit signature n g m)
    (rho : PartialAssignment n) :
    (restrictCircuit source rho).gateCount <= g :=
  (restrictCircuit source rho).gateCount_le

example
    (source : Circuit signature n g m)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (restrictCircuit source rho).result.eval (rho.projectLive input) =
      source.eval interpretation (rho.apply input) :=
  restrictCircuit_eval_projectLive source rho input

example
    (source : Circuit signature n g 1)
    (rho : PartialAssignment n) :
    (restrictOneOutputCircuit source rho).result.cost andOrCost <=
      source.cost andOrCost + 1 :=
  (restrictOneOutputCircuit source rho).cost_le

example
    (source : Circuit signature n g 1)
    (rho : PartialAssignment n) :
    (restrictOneOutputCircuit source rho).gateCount <= g + 1 :=
  (restrictOneOutputCircuit source rho).gateCount_le

example
    (source : Circuit signature n g 1)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (restrictOneOutputCircuit source rho).result.eval interpretation
        (rho.projectLive input) =
      source.eval interpretation (rho.apply input) :=
  restrictOneOutputCircuit_eval_projectLive source rho input

end AlgebraicTests.AC0Restriction
