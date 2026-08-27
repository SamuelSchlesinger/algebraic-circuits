import Algebraic.LowerBound.Counting.Arity
import Algebraic.LowerBound.Counting.Sharp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Coarse arity-only size bounds

These estimates trade the exact signature line count for a closed expression
using only the number of primitive operations and their maximum arity.
-/

namespace Algebraic

/-- A simple closed budget depending only on signature size and maximum arity. -/
def Signature.coarseBudget
    (σ : Signature) [Fintype σ.Op]
    (r n m G : Nat) : Nat :=
  (G + 1) *
    (1 + (n + G) + Fintype.card σ.Op *
      (n + G + 1) ^ r) ^ (G + m)

theorem Signature.sharpCount_le_coarseTerm
    (σ : Signature) [Fintype σ.Op]
    {r n m g G : Nat}
    (arity : σ.ArityAtMost r)
    (bounded : g ≤ G) :
    σ.sharpCount n g m ≤
      (1 + (n + G) + Fintype.card σ.Op *
        (n + G + 1) ^ r) ^ (G + m) := by
  let base := 1 + (n + G) +
    Fintype.card σ.Op * (n + G + 1) ^ r
  have lineBound : σ.lineCount (n + g) ≤ base := by
    calc
      σ.lineCount (n + g) ≤
          Fintype.card σ.Op * (n + g + 1) ^ r :=
        σ.lineCount_le_card_mul_pow arity (n + g)
      _ ≤ Fintype.card σ.Op * (n + G + 1) ^ r := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) r)
      _ ≤ base := by simp [base]
  have wireBound : n + g ≤ base := by
    simp only [base]
    omega
  have exponentBound : g + m ≤ G + m := Nat.add_le_add_right bounded m
  have basePositive : 1 ≤ base := by
    simp only [base]
    omega
  calc
    σ.sharpCount n g m ≤
        σ.lineCount (n + g) ^ g * (n + g) ^ m := by
      exact Nat.div_le_self _ _
    _ ≤ base ^ g * base ^ m :=
      Nat.mul_le_mul (Nat.pow_le_pow_left lineBound g)
        (Nat.pow_le_pow_left wireBound m)
    _ = base ^ (g + m) := (Nat.pow_add base g m).symm
    _ ≤ base ^ (G + m) := pow_le_pow_right' basePositive exponentBound

theorem Signature.sharpBudget_le_coarseBudget
    (σ : Signature) [Fintype σ.Op]
    {r n m G : Nat}
    (arity : σ.ArityAtMost r) :
    σ.sharpBudget n m G ≤ σ.coarseBudget r n m G := by
  unfold Signature.sharpBudget Signature.coarseBudget
  calc
    (∑ g ∈ Finset.range (G + 1), σ.sharpCount n g m) ≤
        ∑ _g ∈ Finset.range (G + 1),
          (1 + (n + G) + Fintype.card σ.Op *
            (n + G + 1) ^ r) ^ (G + m) := by
      exact Finset.sum_le_sum fun g present =>
        σ.sharpCount_le_coarseTerm arity
          (Nat.le_of_lt_succ (Finset.mem_range.mp present))
    _ = (G + 1) *
        (1 + (n + G) + Fintype.card σ.Op *
          (n + G + 1) ^ r) ^ (G + m) := by
      simp

theorem Circuit.card_functionsAtMost_le_coarseBudget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {r : Nat}
    (arity : σ.ArityAtMost r)
    (n m G : Nat) :
    (Circuit.functionsAtMost interpretation n m G).card ≤
      σ.coarseBudget r n m G :=
  (Circuit.card_functionsAtMost_le_sharpBudget interpretation n m G).trans
    (σ.sharpBudget_le_coarseBudget arity)

theorem Circuit.exists_hard_in_family_coarse
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    {r : Nat}
    (arity : σ.ArityAtMost r)
    (large : σ.coarseBudget r n m G < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target :=
  Circuit.exists_hard_in_family_sharp interpretation family <|
    (σ.sharpBudget_le_coarseBudget arity).trans_lt large

end Algebraic
