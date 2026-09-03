import Algebraic.LowerBound.AC0.LayerFormula

/-!
# AC0 layer formula regression tests
-/

namespace AlgebraicTests.AC0LayerFormula

open Algebraic
open Algebraic.AC0

example
    (formulas : Fin count -> DNF n)
    (input : Fin n -> Bool) :
    (DNF.disjoinFamily formulas).eval input =
      interpretation (.or count) (fun index => (formulas index).eval input) :=
  DNF.eval_disjoinFamily formulas input

example
    (formulas : Fin count -> DNF n)
    (bound : Nat)
    (bounded : forall index, (formulas index).WidthAtMost bound) :
    (DNF.disjoinFamily formulas).WidthAtMost bound :=
  DNF.WidthAtMost.disjoinFamily bounded

example
    (formulas : Fin count -> CNF n)
    (input : Fin n -> Bool) :
    (CNF.conjoinFamily formulas).eval input =
      interpretation (.and count) (fun index => (formulas index).eval input) :=
  CNF.eval_conjoinFamily formulas input

example
    (formulas : Fin count -> CNF n)
    (bound : Nat)
    (bounded : forall index, (formulas index).WidthAtMost bound) :
    (CNF.conjoinFamily formulas).WidthAtMost bound :=
  CNF.WidthAtMost.conjoinFamily bounded

example
    (program : Program signature n g)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (gateDepth :
      AC0.Program.logicalGateDepths program gate <= level + 1) :
    Exists fun formula : DNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input =
          ScalarFunction.restrict
            (program.gateFunction interpretation gate) rho input :=
  shallow.exists_dnf_for_or_gate gate operation gateDepth

example
    (program : Program signature n g)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (shallow : AC0.Program.ShallowUpTo program rho level bound)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (gateDepth :
      AC0.Program.logicalGateDepths program gate <= level + 1) :
    Exists fun formula : CNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input =
          ScalarFunction.restrict
            (program.gateFunction interpretation gate) rho input :=
  shallow.exists_cnf_for_and_gate gate operation gateDepth

end AlgebraicTests.AC0LayerFormula
