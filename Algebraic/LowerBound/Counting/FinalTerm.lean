import Algebraic.LowerBound.Counting.Arity
import Algebraic.LowerBound.Counting.Sharp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Final-term envelope for sharp circuit counting

The exact sharp budget is a sum of factorial-divided terms. This file bounds
that sum by its final real-valued term, without yet invoking Stirling.
-/

namespace Algebraic

/-- Real-valued envelope obtained by replacing every summand of the sharp
budget by its final factorial-divided term. -/
noncomputable def Signature.finalTerm
    (σ : Signature) [Fintype σ.Op]
    (n m G : Nat) : Real :=
  (G + 1) *
    (σ.lineCount (n + G) : Real) ^ (G + m) /
      (G.factorial : Real)

/-- The tail of a factorial is bounded by replacing every factor by the final
index. -/
theorem Nat.factorial_le_factorial_mul_pow
    {g G : Nat}
    (bounded : g ≤ G) :
    G.factorial ≤ g.factorial * G ^ (G - g) := by
  induction G with
  | zero =>
      have : g = 0 := Nat.eq_zero_of_le_zero bounded
      subst g
      simp
  | succ G ih =>
      by_cases last : g = G + 1
      · subst g
        simp
      · have prior : g ≤ G := by omega
        calc
          (G + 1).factorial = (G + 1) * G.factorial := by
            rw [Nat.factorial_succ]
          _ ≤ (G + 1) * (g.factorial * G ^ (G - g)) :=
            Nat.mul_le_mul_left _ (ih prior)
          _ ≤ (G + 1) *
              (g.factorial * (G + 1) ^ (G - g)) := by
            gcongr
            exact Nat.le_succ G
          _ = g.factorial * (G + 1) ^ ((G + 1) - g) := by
            rw [show (G + 1) - g = (G - g) + 1 by omega, pow_succ]
            ac_rfl

/-- Real-valued global form of the factorial-improved count. It bounds every
summand by the final one whenever the final line count is at least `G`. -/
theorem Signature.sharpBudget_cast_le_finalTerm
    (σ : Signature) [Fintype σ.Op]
    {n m G : Nat}
    (enoughLines : G ≤ σ.lineCount (n + G)) :
    (σ.sharpBudget n m G : Real) ≤
      σ.finalTerm n m G := by
  unfold Signature.finalTerm
  let base := σ.lineCount (n + G)
  have termBound (g : Nat) (bounded : g ≤ G) :
      (σ.sharpCount n g m : Real) ≤
        (base : Real) ^ (G + m) / (G.factorial : Real) := by
    have lineBound : σ.lineCount (n + g) ≤ base := by
      apply Signature.lineCount_mono σ
      omega
    have factorialBound : G.factorial ≤ g.factorial * base ^ (G - g) :=
      (Nat.factorial_le_factorial_mul_pow bounded).trans <|
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left enoughLines _)
    calc
      (σ.sharpCount n g m : Real) ≤
          (σ.lineCount (n + g) ^ (g + m) : Nat) /
            (g.factorial : Real) := by
        exact Nat.cast_div_le
      _ ≤ (base : Real) ^ (g + m) / (g.factorial : Real) := by
        apply div_le_div_of_nonneg_right
        · rw [← Nat.cast_pow]
          exact_mod_cast Nat.pow_le_pow_left lineBound (g + m)
        · exact Nat.cast_nonneg _
      _ ≤ (base : Real) ^ (G + m) / (G.factorial : Real) := by
        rw [div_le_div_iff₀
          (by exact_mod_cast Nat.factorial_pos g : (0 : Real) < g.factorial)
          (by exact_mod_cast Nat.factorial_pos G : (0 : Real) < G.factorial)]
        have castFactorialBound :
            (G.factorial : Real) ≤
              (g.factorial : Real) * (base : Real) ^ (G - g) := by
          rw [← Nat.cast_pow, ← Nat.cast_mul]
          exact_mod_cast factorialBound
        calc
          (base : Real) ^ (g + m) * G.factorial ≤
              (base : Real) ^ (g + m) *
                (g.factorial * base ^ (G - g)) := by
            exact mul_le_mul_of_nonneg_left castFactorialBound
              (pow_nonneg (Nat.cast_nonneg base) _)
          _ = (base : Real) ^ (G + m) * g.factorial := by
            calc
              (base : Real) ^ (g + m) *
                    ((g.factorial : Real) * base ^ (G - g)) =
                  ((base : Real) ^ (g + m) * base ^ (G - g)) *
                    g.factorial := by ac_rfl
              _ = (base : Real) ^ ((g + m) + (G - g)) *
                    g.factorial := by
                exact congrArg (fun value : Real => value * g.factorial)
                  (pow_add (base : Real) (g + m) (G - g)).symm
              _ = (base : Real) ^ (G + m) * g.factorial := by
                congr 2
                omega
  unfold Signature.sharpBudget
  rw [Nat.cast_sum]
  calc
    (∑ g ∈ Finset.range (G + 1), (σ.sharpCount n g m : Real)) ≤
        ∑ _g ∈ Finset.range (G + 1),
          (base : Real) ^ (G + m) / (G.factorial : Real) := by
      exact Finset.sum_le_sum fun g present =>
        termBound g (Nat.le_of_lt_succ (Finset.mem_range.mp present))
    _ = (G + 1) * (base : Real) ^ (G + m) /
        (G.factorial : Real) := by
      simp
      ring

/-- Real-valued final-term bound on the number of functions computed with at
most `G` gates. -/
theorem Circuit.card_functionsAtMost_cast_le_finalTerm
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {n m G : Nat}
    (enoughLines : G ≤ σ.lineCount (n + G)) :
    ((Circuit.functionsAtMost interpretation n m G).card : Real) ≤
      σ.finalTerm n m G := by
  calc
    ((Circuit.functionsAtMost interpretation n m G).card : Real) ≤
        (σ.sharpBudget n m G : Real) := by
      exact_mod_cast Circuit.card_functionsAtMost_le_sharpBudget
        interpretation n m G
    _ ≤ _ := σ.sharpBudget_cast_le_finalTerm enoughLines

/-- A finite family exceeding the real-valued final-term envelope contains a
function requiring more than `G` gates. -/
theorem Circuit.exists_hard_in_family_of_finalTerm
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (enoughLines : G ≤ σ.lineCount (n + G))
    (large : σ.finalTerm n m G < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_in_family_sharp interpretation family
  have castBound : (σ.sharpBudget n m G : Real) < (family.card : Real) :=
    (σ.sharpBudget_cast_le_finalTerm enoughLines).trans_lt large
  exact_mod_cast castBound

/-- Full-function-space Shannon theorem using the real-valued final-term
envelope. -/
theorem Circuit.exists_hard_of_finalTerm
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (enoughLines : G ≤ σ.lineCount (n + G))
    (large : σ.finalTerm n m G < (Target.count U n m : Real)) :
    ∃ target : Target U n m,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_sharp interpretation
  have castBound : (σ.sharpBudget n m G : Real) <
      (Target.count U n m : Real) :=
    (σ.sharpBudget_cast_le_finalTerm enoughLines).trans_lt large
  exact_mod_cast castBound

end Algebraic
