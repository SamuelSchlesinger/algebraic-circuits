import Algebraic.CircuitFamily

/-!
# Nonuniform circuit-family API regressions

The empty-output family exercises the dependent gate-count index without
choosing a concrete basis.  These examples check exact size/depth accounting,
family semantics, and the polynomial/constant resource predicates.
-/

namespace AlgebraicTests.CircuitFamily

open Algebraic

/-- The gate-free family with no designated outputs. -/
def empty (sigma : Signature) : Circuit.Family sigma 0 where
  gateCount := fun _ => 0
  circuit := fun _ => {
    program := .empty
    outputs := Fin.elim0
  }

/-- The unique empty-output target family. -/
def emptyTarget (U : Type) : Target.Family U 0 :=
  fun _ _ => Fin.elim0

example (sigma : Signature) (n : Nat) :
    (empty sigma).size n = 0 := rfl

example (sigma : Signature) (n : Nat) :
    (empty sigma).depth n = 0 := rfl

example (sigma : Signature) :
    (empty sigma).HasPolynomialSize := by
  exact ⟨0, 0, fun _ => le_rfl⟩

example (sigma : Signature) :
    (empty sigma).HasConstantDepth := by
  exact ⟨0, fun _ => le_rfl⟩

example (sigma : Signature)
    (interpretation : Interpretation sigma U) :
    (empty sigma).Computes interpretation (emptyTarget U) := by
  intro n input
  funext output
  exact Fin.elim0 output

example (family : (n : Nat) -> ScalarFunction U n)
    (input : Fin n -> U) :
    Target.scalarFamily family n input 0 = family n input := rfl

end AlgebraicTests.CircuitFamily
