import Algebraic.Parallel

/-!
# Iterating an endomorphism circuit

Sequentially compose a circuit with itself while retaining exact semantics and
cost.  This construction is useful for fixed-round arithmetic algorithms such
as exponentiation and inversion.
-/

namespace Algebraic

/-- Left-associated iteration, universe-polymorphic over `Sort`. -/
def Circuit.iterateFunction {A : Sort u} (function : A -> A) : Nat -> A -> A
  | 0 => _root_.id
  | steps + 1 => fun input => function (iterateFunction function steps input)

/-- Compose an endomorphism circuit with itself `steps` times. -/
def Circuit.iterate
    (circuit : Circuit σ n g n) :
    (steps : Nat) -> Circuit σ n (steps * g) n
  | 0 => (Circuit.id σ n).castCounts rfl (Nat.zero_mul g).symm rfl
  | steps + 1 =>
      (circuit.comp (circuit.iterate steps)).castCounts rfl
        (Nat.succ_mul steps g).symm rfl

/-- Iterated circuit evaluation is function iteration. -/
@[simp] theorem Circuit.eval_iterate
    (circuit : Circuit σ n g n)
    (steps : Nat)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U) :
    (circuit.iterate steps).eval interpretation input =
      Circuit.iterateFunction (circuit.eval interpretation) steps input := by
  induction steps with
  | zero =>
      simp [Circuit.iterate, Circuit.iterateFunction]
  | succ steps inductionHypothesis =>
      simp only [Circuit.iterate, Circuit.eval_castCounts, Fin.cast_refl,
        Function.comp_id, Circuit.eval_comp]
      rw [inductionHypothesis]
      rfl

/-- Iterating a circuit multiplies its weighted cost by the round count. -/
@[simp] theorem Circuit.cost_iterate
    (circuit : Circuit σ n g n)
    (steps : Nat)
    (operationCost : OperationCost σ) :
    (circuit.iterate steps).cost operationCost =
      steps * circuit.cost operationCost := by
  induction steps with
  | zero => simp [Circuit.iterate]
  | succ steps inductionHypothesis =>
      rw [Circuit.iterate, Circuit.cost_castCounts, Circuit.cost_comp,
        inductionHypothesis, Nat.succ_mul]

end Algebraic
