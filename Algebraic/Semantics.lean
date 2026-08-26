import Algebraic.Circuit
import Mathlib.Data.Finset.Defs

/-!
# Circuit semantics

This file contains the small semantic vocabulary used by circuit lower bounds.
-/

namespace Algebraic

/-- Exact pointwise computation of a function by a circuit. -/
def Circuit.Computes
    (c : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (target : (Fin n → U) → Fin m → U) : Prop :=
  ∀ input, c.eval interpretation input = target input

/-- A function depends only on the input coordinates in `support`. -/
def DependsOnlyOn
    (function : (Fin n → U) → V)
    (support : Finset (Fin n)) : Prop :=
  ∀ left right,
    (∀ k ∈ support, left k = right k) →
    function left = function right

/-- Changing only coordinate `selected` can change the function value. -/
def EssentialAt
    (function : (Fin n → U) → V)
    (selected : Fin n) : Prop :=
  ∃ left right,
    (∀ k, k ≠ selected → left k = right k) ∧
    function left ≠ function right

/-- Every essential coordinate belongs to any support of the function. -/
theorem EssentialAt.mem_support
    {function : (Fin n → U) → V}
    {support : Finset (Fin n)}
    {selected : Fin n}
    (essential : EssentialAt function selected)
    (depends : DependsOnlyOn function support) :
    selected ∈ support := by
  obtain ⟨left, right, agree, different⟩ := essential
  by_contra absent
  apply different
  apply depends left right
  intro k present
  exact agree k fun equal => absent (equal ▸ present)

end Algebraic
