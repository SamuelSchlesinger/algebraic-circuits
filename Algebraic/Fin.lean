import Mathlib.Data.Fin.Basic

/-!
# Finite folds

Small order-theoretic facts about folds indexed by `Fin`.
-/

namespace Algebraic.Fin

/-- Every folded value is at most the maximum accumulated by `Fin.foldl`. -/
theorem le_foldl_max [LinearOrder α]
    (values : Fin n → α)
    (initial : α)
    (i : Fin n) :
    values i ≤ Fin.foldl n (fun result j => max result (values j)) initial := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.foldl_succ_last]
        exact le_max_right _ _
      · rw [Fin.foldl_succ_last]
        exact (ih (fun i => values i.castSucc) i).trans (le_max_left _ _)

end Algebraic.Fin
