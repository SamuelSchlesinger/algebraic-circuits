import Algebraic.LowerBound.AC0.Switching.CombinedAdvice
import Algebraic.LowerBound.AC0.Switching.CanonicalEncoding
import Mathlib.Data.Finset.Sort

/-!
# Decoder-facing combined switching advice

This module gives the counted block advice a canonical sequential
interpretation. Each stored position subset is replayed in increasing source
order. A continuing block closes after its last query, while the last block
never needs a closing marker because replay ends with the advice list.
-/

namespace Algebraic
namespace AC0
namespace Switching

/-- Expand one block into the elementary query format used by the canonical
replay decoder. -/
def BlockAdvice.toQueryList
    (block : BlockAdvice width length)
    (closesBlock : Bool) : List (QueryAdvice width) :=
  List.ofFn fun index : Fin length =>
    { position := block.positions.val.orderEmbOfFin block.positions.property index
      closesBlock := closesBlock && decide (index.val + 1 = length)
      difference := block.differences index }

/-- Expanding a block preserves its indexed length. -/
@[simp] theorem BlockAdvice.length_toQueryList
    (block : BlockAdvice width length)
    (closesBlock : Bool) :
    (block.toQueryList closesBlock).length = length := by
  simp [BlockAdvice.toQueryList]

private def CombinedAdvice.uncons
    (advice : CombinedAdvice width (pathLength + 1)) :
    (blockLengthMinusOne : Fin (Nat.min width (pathLength + 1))) ×
      if blockLengthMinusOne.val = pathLength then
        BlockAdvice width (blockLengthMinusOne.val + 1)
      else
        ContinuingBlockAdvice width (blockLengthMinusOne.val + 1) ×
          CombinedAdvice width
            (pathLength - blockLengthMinusOne.val) := by
  have unpacked := advice
  rw [show pathLength + 1 = Nat.succ pathLength by omega] at unpacked
  simpa only [CombinedAdvice] using unpacked

/-- Flatten combined advice into sequential query advice. Source positions are
sorted within each block; exactly the nonfinal block boundaries are marked. -/
def CombinedAdvice.toQueryList :
    (pathLength : Nat) → CombinedAdvice width pathLength →
      List (QueryAdvice width)
  | 0, _ => []
  | pathLength + 1, advice => by
      let unpacked := advice.uncons
      rcases unpacked with ⟨index, payload⟩
      by_cases final : index.val = pathLength
      · have block : BlockAdvice width (index.val + 1) := by
          simpa [final] using payload
        exact block.toQueryList false
      · have payload : ContinuingBlockAdvice width (index.val + 1) ×
            CombinedAdvice width (pathLength - index.val) := by
          simpa [final] using payload
        exact payload.1.val.toQueryList true ++
          CombinedAdvice.toQueryList (pathLength - index.val) payload.2

/-- Flattening combined advice produces exactly the indexed number of query
symbols. -/
@[simp] theorem CombinedAdvice.length_toQueryList
    (advice : CombinedAdvice width pathLength) :
    advice.toQueryList.length = pathLength := by
  induction pathLength using Nat.strong_induction_on with
  | h pathLength inductionHypothesis =>
      cases pathLength with
      | zero => simp [CombinedAdvice.toQueryList]
      | succ remaining =>
          rw [CombinedAdvice.toQueryList]
          generalize unpackedEq : advice.uncons = unpacked
          rcases unpacked with ⟨index, payload⟩
          by_cases final : index.val = remaining
          · simp only [final, ↓reduceDIte, BlockAdvice.length_toQueryList]
          · simp only [final, ↓reduceDIte, List.length_append,
              BlockAdvice.length_toQueryList]
            have indexLe : index.val ≤ remaining := by
              have belowTotal : index.val < remaining + 1 :=
                index.isLt.trans_le
                  (Nat.min_le_right width (remaining + 1))
              omega
            rw [inductionHypothesis]
            · omega
            · omega

private def QueryAdvice.withoutClose
    (advice : QueryAdvice width) : QueryAdvice width :=
  { advice with closesBlock := false }

/-- Erase the final query's block-closing marker. It is operationally
irrelevant because no advice remains after that query. -/
def clearLastClose : List (QueryAdvice width) → List (QueryAdvice width)
  | [] => []
  | [advice] => [advice.withoutClose]
  | advice :: next :: rest => advice :: clearLastClose (next :: rest)

/-- Erasing the last closing marker preserves list length. -/
@[simp] theorem length_clearLastClose
    (advice : List (QueryAdvice width)) :
    (clearLastClose advice).length = advice.length := by
  induction advice with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [clearLastClose, List.length_cons]
          simp only [List.length_cons] at inductionHypothesis
          omega

/-- Canonical replay is insensitive to the final query's closing marker. -/
theorem replayIndices_clearLastClose
    (formula : DNF n)
    (state : PartialAssignment n)
    (currentTerm : Option (Term n))
    (advice : List (QueryAdvice width)) :
    replayIndices formula state currentTerm (clearLastClose advice) =
      replayIndices formula state currentTerm advice := by
  induction advice generalizing state currentTerm with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [clearLastClose, replayIndices, QueryAdvice.withoutClose]
      | cons next rest =>
          simp only [clearLastClose, replayIndices]
          split <;> rename_i selected
          · rfl
          · split <;> rename_i decoded
            · rfl
            · change _ :: replayIndices formula _ _
                  (clearLastClose (next :: rest)) =
                _ :: replayIndices formula _ _ (next :: rest)
              exact congrArg (List.cons _) (inductionHypothesis _ _)

/-- Decode a refined restriction carrying combined block advice. -/
def decodeCombined
    (formula : DNF n)
    (encoded : PartialAssignment n × CombinedAdvice width pathLength) :
    PartialAssignment n :=
  encoded.1.clear
    (replayIndices formula encoded.1 none encoded.2.toQueryList).toFinset

end Switching
end AC0
end Algebraic
