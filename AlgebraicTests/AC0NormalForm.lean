import Algebraic.LowerBound.AC0.NormalForm
import Mathlib.Data.Fin.VecNotation

/-!
# AC0 normal-form regression tests
-/

namespace AlgebraicTests.AC0NormalForm

open Algebraic
open Algebraic.AC0

def twoLiteralTerm : Term 3 :=
  ⟨(PartialAssignment.fix (0 : Fin 3) true).refine
    (PartialAssignment.fix (2 : Fin 3) false)⟩

example :
    Term.eval twoLiteralTerm (![true, true, false] : Fin 3 -> Bool) = true := by
  decide

example :
    Term.eval twoLiteralTerm (![true, true, true] : Fin 3 -> Bool) = false := by
  decide

example :
    Term.restrict twoLiteralTerm
      (PartialAssignment.fix (0 : Fin 3) false) = none := by
  decide

def oneLiteralTerm : Term 3 :=
  LiteralSet.singleton ⟨1, true⟩

def sampleDNF : DNF 3 :=
  ⟨[twoLiteralTerm, oneLiteralTerm]⟩

example : sampleDNF.WidthAtMost 2 := by
  intro term present
  simp only [sampleDNF, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> decide

example
    (rho : PartialAssignment 3)
    (input : Fin 3 -> Bool) :
    (sampleDNF.restrict rho).eval input =
      sampleDNF.eval (rho.apply input) :=
  DNF.restrict_sound sampleDNF rho input

def twoLiteralClause : Clause 3 :=
  ⟨(PartialAssignment.fix (0 : Fin 3) true).refine
    (PartialAssignment.fix (1 : Fin 3) false)⟩

def oneLiteralClause : Clause 3 :=
  LiteralSet.singleton ⟨2, true⟩

def sampleCNF : CNF 3 :=
  ⟨[twoLiteralClause, oneLiteralClause]⟩

example : sampleCNF.WidthAtMost 2 := by
  intro clause present
  simp only [sampleCNF, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> decide

example :
    Clause.restrict twoLiteralClause
      (PartialAssignment.fix (0 : Fin 3) true) = none := by
  decide

example
    (rho : PartialAssignment 3)
    (input : Fin 3 -> Bool) :
    (sampleCNF.restrict rho).eval input =
      sampleCNF.eval (rho.apply input) :=
  CNF.restrict_sound sampleCNF rho input

end AlgebraicTests.AC0NormalForm
