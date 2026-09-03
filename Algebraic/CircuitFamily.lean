import Algebraic.Cost
import Algebraic.Semantics
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Nonuniform circuit families

Circuit lower bounds are finite statements about one input width, while
complexity classes quantify over a sequence of circuits.  This module supplies
that missing bridge without fixing a gate basis.

A `Circuit.Family sigma m` chooses one `m`-output circuit for every input width.
Its gate count remains an explicit index, so `size` agrees definitionally with
the finite circuit model.  Polynomial size and constant depth are expressed by
exact natural-number bounds.  The factor `(n + 1) ^ degree` makes the definition
well behaved at input width zero and avoids burying finite-prefix adjustments
inside asymptotic notation.
-/

namespace Algebraic

namespace Target

/-- An `m`-output target at every input width. -/
abbrev Family (U : Type u) (m : Nat) :=
  (n : Nat) -> Target U n m

/-- Regard a family of scalar functions as a one-output target family. -/
def scalarFamily
    (family : (n : Nat) -> ScalarFunction U n) : Target.Family U 1 :=
  fun n input _ => family n input

@[simp] theorem scalarFamily_apply
    (family : (n : Nat) -> ScalarFunction U n)
    (input : Fin n -> U)
    (output : Fin 1) :
    Target.scalarFamily family n input output = family n input := rfl

end Target

namespace Circuit

namespace Resource

/-- A natural-valued resource is bounded by one fixed polynomial.

The coefficient and degree do not depend on the input width.  Using `n + 1`
gives an exact all-width statement equivalent to the usual eventual polynomial
bound for natural-valued resources. -/
def PolynomiallyBounded (resource : Nat -> Nat) : Prop :=
  Exists fun coefficient : Nat =>
    Exists fun degree : Nat =>
      forall n, resource n <= coefficient * (n + 1) ^ degree

/-- A natural-valued resource is bounded by one constant at every width. -/
def ConstantlyBounded (resource : Nat -> Nat) : Prop :=
  Exists fun bound : Nat => forall n, resource n <= bound

/-- A resource eventually strictly exceeds every fixed natural polynomial. -/
def EventuallyExceedsEveryPolynomial (resource : Nat -> Nat) : Prop :=
  forall coefficient degree,
    Filter.Eventually
      (fun n => coefficient * (n + 1) ^ degree < resource n)
      Filter.atTop

/-- A pointwise smaller resource inherits a polynomial upper bound. -/
theorem PolynomiallyBounded.of_le
    {smaller larger : Nat -> Nat}
    (bounded : PolynomiallyBounded larger)
    (comparison : forall n, smaller n <= larger n) :
    PolynomiallyBounded smaller := by
  obtain ⟨coefficient, degree, bound⟩ := bounded
  exact ⟨coefficient, degree, fun n => (comparison n).trans (bound n)⟩

/-- Every constant resource bound is a degree-zero polynomial bound. -/
theorem ConstantlyBounded.polynomiallyBounded
    {resource : Nat -> Nat}
    (bounded : ConstantlyBounded resource) :
    PolynomiallyBounded resource := by
  obtain ⟨bound, bounded⟩ := bounded
  refine ⟨bound, 0, ?_⟩
  intro n
  simpa using bounded n

/-- Eventual domination of every polynomial rules out a polynomial bound. -/
theorem EventuallyExceedsEveryPolynomial.not_polynomiallyBounded
    {resource : Nat -> Nat}
    (dominates : EventuallyExceedsEveryPolynomial resource) :
    Not (PolynomiallyBounded resource) := by
  rintro ⟨coefficient, degree, bounded⟩
  obtain ⟨cutoff, dominatesFrom⟩ :=
    Filter.eventually_atTop.1 (dominates coefficient degree)
  exact (Nat.not_lt_of_ge (bounded cutoff))
    (dominatesFrom cutoff (le_refl cutoff))

end Resource

/-- A nonuniform family chooses one finite circuit at each input width. -/
structure Family (sigma : Signature) (m : Nat) where
  /-- Number of internal gates at each input width. -/
  gateCount : Nat -> Nat
  /-- The circuit chosen nonuniformly at each input width. -/
  circuit : (n : Nat) -> Circuit sigma n (gateCount n) m

namespace Family

/-- Gate-count size of every member of a circuit family. -/
def size (family : Circuit.Family sigma m) (n : Nat) : Nat :=
  (family.circuit n).size

@[simp] theorem size_eq_gateCount
    (family : Circuit.Family sigma m)
    (n : Nat) :
    family.size n = family.gateCount n := rfl

/-- Designated-output depth of every member of a circuit family. -/
def depth (family : Circuit.Family sigma m) (n : Nat) : Nat :=
  (family.circuit n).depth

/-- Weighted gate cost of every member of a circuit family. -/
def cost
    (family : Circuit.Family sigma m)
    (operationCost : OperationCost sigma)
    (n : Nat) : Nat :=
  (family.circuit n).cost operationCost

/-- Pointwise exact computation of a target family. -/
def Computes
    (family : Circuit.Family sigma m)
    (interpretation : Interpretation sigma U)
    (target : Target.Family U m) : Prop :=
  forall n, (family.circuit n).Computes interpretation (target n)

/-- The family has a specified all-width size bound. -/
def HasSizeAtMost
    (family : Circuit.Family sigma m)
    (bound : Nat -> Nat) : Prop :=
  forall n, family.size n <= bound n

/-- The family has a specified all-width depth bound. -/
def HasDepthAtMost
    (family : Circuit.Family sigma m)
    (bound : Nat -> Nat) : Prop :=
  forall n, family.depth n <= bound n

/-- The family has polynomially bounded gate-count size. -/
def HasPolynomialSize (family : Circuit.Family sigma m) : Prop :=
  Resource.PolynomiallyBounded family.size

/-- The family has polynomially bounded weighted cost. -/
def HasPolynomialCost
    (family : Circuit.Family sigma m)
    (operationCost : OperationCost sigma) : Prop :=
  Resource.PolynomiallyBounded (family.cost operationCost)

/-- The family has one depth bound independent of the input width. -/
def HasConstantDepth (family : Circuit.Family sigma m) : Prop :=
  Resource.ConstantlyBounded family.depth

/-- A pointwise size budget yields polynomial size when the budget is
polynomially bounded. -/
theorem HasSizeAtMost.polynomialSize
    {family : Circuit.Family sigma m}
    {bound : Nat -> Nat}
    (bounded : family.HasSizeAtMost bound)
    (polynomial : Resource.PolynomiallyBounded bound) :
    family.HasPolynomialSize :=
  polynomial.of_le bounded

/-- A pointwise depth budget yields constant depth when the budget is
constantly bounded. -/
theorem HasDepthAtMost.constantDepth
    {family : Circuit.Family sigma m}
    {bound : Nat -> Nat}
    (bounded : family.HasDepthAtMost bound)
    (constant : Resource.ConstantlyBounded bound) :
    family.HasConstantDepth := by
  obtain ⟨depthBound, bound⟩ := constant
  exact ⟨depthBound, fun n => (bounded n).trans (bound n)⟩

end Family
end Circuit
end Algebraic
