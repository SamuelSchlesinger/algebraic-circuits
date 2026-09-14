import Algebraic.Program
import Cslib.Computability.Circuit.Basic

/-!
# Circuits from CSLib

The circuit type and its evaluation are supplied by CSLib. A circuit consists of
a shared straight-line program and designated output wires; its size counts only
internal gates. Local semantics, costs, and constructions extend this same type.
-/

namespace Algebraic

export Cslib.Circuits (Circuit)

namespace Circuit

export Cslib.Circuits.Circuit
  (id FanInAtMost instDecidableFanInAtMost size outputDepths depth eval eval_id map_eval
   computation trace)

end Circuit
end Algebraic
