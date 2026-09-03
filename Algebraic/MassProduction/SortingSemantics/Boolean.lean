import Algebraic.MassProduction.SortingSemantics.Defs
import Mathlib.Data.Fintype.Pi

/-!
# Finite Boolean core of bitonic cleaning

The eight-value closure lemma is proved by kernel reduction.
-/

namespace Algebraic
namespace MassProduction
namespace Sorting
namespace Semantics

private instance instDecidableSequenceBitonicInternal {n : ℕ} [LinearOrder α]
    (sequence : Fin n → α) : Decidable (SequenceBitonic sequence) := by
  unfold SequenceBitonic
  infer_instance

/-- Pairwise minima of the two Boolean halves used by the finite cleaning
check. -/
def boolHalfMinInternal (sequence : Fin 8 → Bool) : Fin 4 → Bool :=
  fun i => min (sequence (Fin.castAdd 4 i)) (sequence (Fin.natAdd 4 i))

/-- Pairwise maxima of the two Boolean halves used by the finite cleaning
check. -/
def boolHalfMaxInternal (sequence : Fin 8 → Bool) : Fin 4 → Bool :=
  fun i => max (sequence (Fin.castAdd 4 i)) (sequence (Fin.natAdd 4 i))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem bool_bitonic_halves_internal
    (sequence : Fin 8 → Bool) (hsequence : SequenceBitonic sequence) :
    SequenceBitonic (boolHalfMinInternal sequence) ∧
      SequenceBitonic (boolHalfMaxInternal sequence) := by
  decide +revert

end Semantics
end Sorting
end MassProduction
end Algebraic
