import Algebraic.ConditionalComplexity
import Algebraic.Complexity.RelativeCounting

/-!
# Counting with a fixed supplied family

For any fixed `given : U^n → U^k`, the number of targets with conditional
gate complexity at most `budget` is bounded by the number of circuit
descriptions on `n + k` inputs. The bound is independent of the complexity
of `given`. Dividing by the size of a nonempty target family gives a bound
on the probability that a uniformly sampled target is conditionally easy.

The supplied family is fixed before choosing the target. In particular,
these statements do not bound an adversarial choice `given = target`.
-/

open Algebraic
open scoped Classical

namespace Cslib.Circuits.Circuit

/-- All targets computable within a gate budget from a fixed supplied family. -/
noncomputable def conditionalFunctionsAtMost
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (m budget : Nat) : Finset (Target U n m) :=
  relativeFunctionsAtMost interpretation (fun input => Fin.append input (given input)) m budget

/-- Membership in the counted set is exactly a conditional complexity bound. -/
theorem mem_conditionalFunctionsAtMost_iff
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (target : Target U n m) (budget : Nat) :
    target ∈ conditionalFunctionsAtMost interpretation given m budget ↔
      conditionalGateComplexity interpretation target given ≤ budget :=
  mem_relativeFunctionsAtMost_iff interpretation
    (fun input => Fin.append input (given input)) target budget

/-- Fixed supplied functions create at most one target per circuit description. -/
theorem card_conditionalFunctionsAtMost_le
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (m budget : Nat) :
    (conditionalFunctionsAtMost interpretation given m budget).card ≤
      σ.orderedBudget (n + k) m budget :=
  card_relativeFunctionsAtMost_le interpretation
    (fun input => Fin.append input (given input)) m budget

/-- The factorial-improved semantic count also bounds conditional complexity. -/
theorem card_conditionalFunctionsAtMost_le_sharpBudget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (m budget : Nat) :
    (conditionalFunctionsAtMost interpretation given m budget).card ≤
      σ.sharpBudget (n + k) m budget :=
  card_relativeFunctionsAtMost_le_sharpBudget interpretation
    (fun input => Fin.append input (given input)) m budget

/-- Any target family larger than the circuit budget contains a function
that remains hard after supplying `given`. -/
theorem exists_conditional_hard_in_family
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (family : Finset (Target U n m)) (budget : Nat)
    (large : σ.orderedBudget (n + k) m budget < family.card) :
    ∃ target ∈ family, (budget : ℕ∞) <
      conditionalGateComplexity interpretation target given :=
  exists_relative_hard_in_family interpretation
    (fun input => Fin.append input (given input)) family budget large

/-- Factorial-improved counting yields a conditionally hard target. -/
theorem exists_conditional_hard_in_family_sharp
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (family : Finset (Target U n m)) (budget : Nat)
    (large : σ.sharpBudget (n + k) m budget < family.card) :
    ∃ target ∈ family, (budget : ℕ∞) < conditionalGateComplexity interpretation target given :=
  exists_relative_hard_in_family_sharp interpretation
    (fun input => Fin.append input (given input)) family budget large

/-- Counting over the entire truth-table space yields a conditionally hard target. -/
theorem exists_conditional_hard
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (m budget : Nat)
    (small : σ.orderedBudget (n + k) m budget < Nat.card U ^ (m * Nat.card U ^ n)) :
    ∃ target : Target U n m,
      (budget : ℕ∞) < conditionalGateComplexity interpretation target given := by
  classical
  obtain ⟨target, _, hard⟩ := exists_conditional_hard_in_family interpretation given
    (Finset.univ : Finset (Target U n m)) budget (by
      simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, card_target] using small)
  exact ⟨target, hard⟩

/-- A finite menu of supplied families costs only a multiplicative factor
in counting. A sufficiently large target family has a member hard for every
choice from the menu, even if that choice is made after seeing the target. -/
theorem exists_conditional_hard_for_all_given
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (menu : Finset (Target U n k))
    (family : Finset (Target U n m)) (budget : Nat)
    (large : menu.card * σ.orderedBudget (n + k) m budget < family.card) :
    ∃ target ∈ family, ∀ given ∈ menu,
      (budget : ℕ∞) < conditionalGateComplexity interpretation target given := by
  classical
  let graph := fun given : Target U n k => fun input => Fin.append input (given input)
  obtain ⟨target, member, hard⟩ := exists_relative_hard_for_all_sources interpretation
    (menu.image graph) family budget
    ((Nat.mul_le_mul_right _ Finset.card_image_le).trans_lt large)
  exact ⟨target, member, fun given inMenu => hard (graph given) (Finset.mem_image_of_mem graph inMenu)⟩

/-- Probability bound for a uniformly sampled member of a nonempty target
family, expressed as an exact rational cardinality ratio. The supplied family
is fixed independently of this sampling. -/
theorem conditional_easy_fraction_le
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (given : Target U n k)
    (family : Finset (Target U n m)) (budget : Nat) :
    ((family ∩ conditionalFunctionsAtMost interpretation given m budget).card : ℚ) /
        family.card ≤
      (σ.orderedBudget (n + k) m budget : ℚ) / family.card :=
  relative_easy_fraction_le interpretation
    (fun input => Fin.append input (given input)) family budget

end Cslib.Circuits.Circuit

namespace Algebraic.Circuit

export Cslib.Circuits.Circuit
  (conditionalFunctionsAtMost mem_conditionalFunctionsAtMost_iff
   card_conditionalFunctionsAtMost_le card_conditionalFunctionsAtMost_le_sharpBudget
   exists_conditional_hard_in_family exists_conditional_hard_in_family_sharp
   exists_conditional_hard exists_conditional_hard_for_all_given conditional_easy_fraction_le)

end Algebraic.Circuit
