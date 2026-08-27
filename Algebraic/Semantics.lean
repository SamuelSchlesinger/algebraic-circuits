import Algebraic.Circuit
import Mathlib.Data.Finset.Defs

/-!
# Circuit semantics

This file contains the small semantic vocabulary used by circuit lower bounds.
-/

namespace Algebraic

/-- A single-output function on `n` inputs over `U`. -/
abbrev ScalarFunction (U : Type u) (n : Nat) := (Fin n → U) → U

/-- An `m`-output function on `n` inputs over `U`. -/
abbrev Target (U : Type u) (n m : Nat) := (Fin n → U) → Fin m → U

/-- The scalar function carried by one designated output wire. -/
def Circuit.outputFunction
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (output : Fin m) : ScalarFunction U n :=
  fun input => circuit.eval interpretation input output

@[simp] theorem Circuit.outputFunction_apply
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (output : Fin m)
    (input : Fin n → U) :
    circuit.outputFunction interpretation output input =
      circuit.eval interpretation input output := rfl

/-- Exact pointwise computation of a function by a circuit. -/
def Circuit.Computes
    (c : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (target : Target U n m) : Prop :=
  ∀ input, c.eval interpretation input = target input

/-- Pointwise computation gives equality of the computed and target functions. -/
theorem Circuit.Computes.eval_eq
    {circuit : Circuit σ n g m}
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (computes : circuit.Computes interpretation target) :
    circuit.eval interpretation = target :=
  funext computes

/-- A target is gate-hard at budget `G` when no circuit with at most `G`
internal gates computes it. -/
def Circuit.GateHard
    (interpretation : Interpretation σ U)
    (G : Nat)
    (target : Target U n m) : Prop :=
  ∀ g ≤ G, ∀ circuit : Circuit σ n g m,
    ¬circuit.Computes interpretation target

/-- A target is depth-hard at `depth` when every circuit computing it has
strictly greater depth. -/
def Circuit.DepthHard
    (interpretation : Interpretation σ U)
    (depth : Nat)
    (target : Target U n m) : Prop :=
  ∀ g, ∀ circuit : Circuit σ n g m,
    circuit.Computes interpretation target → depth < circuit.depth

/-- An interpretation is functionally complete if every finite-arity,
finite-output target has some circuit. -/
def Interpretation.FunctionallyComplete
    (interpretation : Interpretation σ U) : Prop :=
  ∀ n m, ∀ target : Target U n m,
    ∃ g, ∃ circuit : Circuit σ n g m,
      circuit.Computes interpretation target

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
