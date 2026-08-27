import Algebraic.Cost

/-!
# Sum-of-terms circuit basis

This basis represents restricted arithmetic circuits whose charged gates
produce members of a prescribed dictionary and whose free gates add already
constructed values.  By choosing the term type appropriately, it models
diagonal depth-three circuits (sums of powers), sums of products, tensor-rank
decompositions, and related representation problems.

Coefficients can be included in the term parameter itself.  This keeps the
syntax independent of any scalar action on the semantic carrier.
-/

namespace Algebraic
namespace SumOfTerms

/-- Binary addition and a family of nullary dictionary terms. -/
inductive Op (T : Type u)
  | add
  | term (value : T)
  deriving DecidableEq

/-- Arity of sum-of-terms operations. -/
def arity : Op T → Nat
  | .add => 2
  | .term _ => 0

@[simp] theorem arity_add : arity (Op.add : Op T) = 2 := rfl

@[simp] theorem arity_term (term : T) : arity (.term term) = 0 := rfl

/-- Signature for free addition of charged dictionary terms. -/
abbrev signature (T : Type u) : Signature where
  Op := Op T
  Arity := arity

/-- Interpret a term by its dictionary value and addition by carrier addition. -/
def interpretation
    [Add V]
    (termValue : T → V) : Interpretation (signature T) V
  | .add, input => input (0 : Fin 2) + input (1 : Fin 2)
  | .term term, _ => termValue term

/-- Charge one for each dictionary term and make addition free. -/
def termCost : OperationCost (signature T)
  | .add => 0
  | .term _ => 1

@[simp] theorem termCost_add : termCost (T := T) .add = 0 := rfl

@[simp] theorem termCost_term (term : T) : termCost (.term term) = 1 := rfl

end SumOfTerms
end Algebraic
