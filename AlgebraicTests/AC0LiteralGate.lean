import Algebraic.LowerBound.AC0.LiteralGate

/-!
# Literal-input AC0 gate regression tests
-/

namespace AlgebraicTests.AC0LiteralGate

open Algebraic
open Algebraic.AC0

example
    (literals : Fin literalCount -> Literal n)
    (input : Fin n -> Bool) :
    (LiteralFamily.conjunction literals).eval input =
      interpretation (.and literalCount) (fun argument =>
        (literals argument).eval input) :=
  LiteralFamily.conjunction_eval literals input

example
    (literals : Fin literalCount -> Literal n) :
    (LiteralFamily.conjunction literals).WidthAtMost literalCount :=
  LiteralFamily.conjunction_widthAtMost literals

example
    (literals : Fin literalCount -> Literal n)
    (input : Fin n -> Bool) :
    (LiteralFamily.disjunction literals).eval input =
      interpretation (.or literalCount) (fun argument =>
        (literals argument).eval input) :=
  LiteralFamily.disjunction_eval literals input

example
    (literals : Fin literalCount -> Literal n) :
    (LiteralFamily.disjunction literals).WidthAtMost literalCount :=
  LiteralFamily.disjunction_widthAtMost literals

end AlgebraicTests.AC0LiteralGate
