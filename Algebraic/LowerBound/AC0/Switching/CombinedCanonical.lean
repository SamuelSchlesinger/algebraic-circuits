import Algebraic.LowerBound.AC0.Switching.Canonical
import Algebraic.LowerBound.AC0.Switching.CombinedCanonicalPacking

/-!
# The combined canonical DNF switching injection

This module replaces the elementary per-query advice alphabet in the
canonical switching injection by the counted source-term block encoding. The
explicit decoder proves injectivity on the bad event, and the general weighted
restriction engine yields the exact scaled bound with advice base
`((5t - 1) / 2)^s` for positive width `t`.
-/

namespace Algebraic
namespace AC0
namespace Switching

private def defaultBlock
    [NeZero width]
    (difference : Bool) : BlockAdvice width 1 :=
  { positions := ⟨{Fin.ofNat width 0}, by simp⟩
    differences := fun _ => difference }

private theorem defaultBlock_true_hasMismatch
    [NeZero width] :
    (defaultBlock (width := width) true).HasMismatch := by
  intro allZero
  have atZero := congrFun allZero (0 : Fin 1)
  simp [defaultBlock] at atZero

/-- A harmless total combined-advice value used outside the bad event. -/
def defaultCombinedAdvice
    [NeZero width] : (pathLength : Nat) → CombinedAdvice width pathLength
  | 0 => by
      simp only [CombinedAdvice]
      exact PUnit.unit
  | 1 =>
      CombinedAdvice.ofFinalBlock (defaultBlock false)
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne width))
  | pathLength + 2 => by
      have advice := CombinedAdvice.prependBlock (blockRemaining := 0)
        (tailLength := pathLength + 1)
        ⟨defaultBlock true, defaultBlock_true_hasMismatch⟩
        (defaultCombinedAdvice (pathLength + 1))
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne width)) (by omega)
      simpa only [Nat.zero_add, Nat.succ_eq_add_one] using advice

/-- Total combined restriction/advice encoding for the canonical-depth bad
event. -/
noncomputable def combinedCanonicalEncoding
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n) :
    PartialAssignment n × CombinedAdvice widthBound pathLength :=
  if deep : formula.CanonicalDepthAtLeast rho pathLength then
    let path := chosenPath formula rho pathLength deep
    let trace := chosenTrace formula rho pathLength deep
    (rho.refine
        (trace.satisfyingAssignment (widthBound := widthBound)),
      trace.combinedAdviceOfLength bounded path.length_steps)
  else
    (rho, defaultCombinedAdvice pathLength)

/-- On the bad event, combined encoding refines by the same canonical
satisfying extension as the elementary encoder. -/
theorem combinedCanonicalEncoding_fst_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (combinedCanonicalEncoding formula bounded pathLength rho).1 =
      rho.refine
        (canonicalExtension (widthBound := widthBound)
          formula pathLength rho) := by
  simp [combinedCanonicalEncoding, canonicalExtension, deep]

/-- The combined decoder recovers every bad-event restriction. -/
theorem decodeCombined_combinedCanonicalEncoding_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    decodeCombined formula
      (combinedCanonicalEncoding formula bounded pathLength rho) = rho := by
  simp only [combinedCanonicalEncoding, dif_pos deep]
  exact (chosenPath formula rho pathLength deep).decodeCombined_satisfyingEncoding
    (chosenTrace formula rho pathLength deep) bounded

/-- The combined encoder is injective on the canonical-depth bad event. -/
theorem combinedCanonicalEncoding_injectiveOn_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat) :
    ∀ left, formula.CanonicalDepthAtLeast left pathLength →
      ∀ right, formula.CanonicalDepthAtLeast right pathLength →
        combinedCanonicalEncoding formula bounded pathLength left =
          combinedCanonicalEncoding formula bounded pathLength right →
          left = right := by
  intro left leftDeep right rightDeep equal
  have decodedEqual := congrArg (decodeCombined formula) equal
  rw [decodeCombined_combinedCanonicalEncoding_of_deep
        formula bounded pathLength left leftDeep,
    decodeCombined_combinedCanonicalEncoding_of_deep
      formula bounded pathLength right rightDeep] at decodedEqual
  exact decodedEqual

/-- The combined-advice cardinality bound transferred to extended
nonnegative reals for probability estimates. -/
theorem card_combinedAdvice_cast_le_ennreal
    (width pathLength : Nat)
    (widthPositive : 0 < width) :
    (Fintype.card (CombinedAdvice width pathLength) : ENNReal) ≤
      ((((5 * width - 1 : Nat) : ENNReal) / 2) ^ pathLength) := by
  have realBound := card_combinedAdvice_cast_le width pathLength widthPositive
  have realNumerator :
      ((5 * width - 1 : Nat) : Real) = (5 : Real) * width - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 5 * width)]
    norm_num
  rw [← realNumerator] at realBound
  have nnrealBound :
      (Fintype.card (CombinedAdvice width pathLength) : NNReal) ≤
        ((((5 * width - 1 : Nat) : NNReal) / 2) ^ pathLength) := by
    exact_mod_cast realBound
  simpa using (ENNReal.coe_le_coe.mpr nnrealBound)

end Switching

namespace RandomRestriction

open scoped ENNReal

/-- Exact weighted switching inequality before inserting the combined-advice
cardinality estimate. -/
theorem probability_canonicalDepthAtLeast_combined_card_scaled_le
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ pathLength *
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      (Fintype.card (Switching.CombinedAdvice widthBound pathLength) :
          ENNReal) *
        (p : ENNReal) ^ pathLength := by
  let _ : DecidableEq (Switching.CombinedAdvice widthBound pathLength) :=
    Classical.decEq _
  exact probability_scaled_le_of_refinement_encoding
    n p atMostOne
    (fun rho => formula.CanonicalDepthAtLeast rho pathLength)
    (Switching.CombinedAdvice widthBound pathLength) pathLength
    (Switching.canonicalExtension (widthBound := widthBound)
      formula pathLength)
    (Switching.combinedCanonicalEncoding formula bounded pathLength)
    (Switching.combinedCanonicalEncoding_injectiveOn_deep
      formula bounded pathLength)
    (Switching.combinedCanonicalEncoding_fst_of_deep
      formula bounded pathLength)
    (Switching.canonicalExtension_fixesOnlyLive_of_deep
      (widthBound := widthBound) formula pathLength)
    (Switching.canonicalExtension_fixedCount_of_deep
      (widthBound := widthBound) formula pathLength)

/-- Exact positive-width scaled switching inequality with Beame's combined
advice base `((5t - 1) / 2)^s`. -/
theorem probability_canonicalDepthAtLeast_combined_scaled_le
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ pathLength *
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) ^ pathLength) *
        (p : ENNReal) ^ pathLength := by
  calc
    (fixedWeight p : ENNReal) ^ pathLength *
          probability n p atMostOne
            (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
        (Fintype.card
            (Switching.CombinedAdvice widthBound pathLength) : ENNReal) *
          (p : ENNReal) ^ pathLength :=
      probability_canonicalDepthAtLeast_combined_card_scaled_le
        formula bounded pathLength p atMostOne
    _ ≤ ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) ^
          pathLength) * (p : ENNReal) ^ pathLength :=
      mul_le_mul_left
        (Switching.card_combinedAdvice_cast_le_ennreal
          widthBound pathLength (NeZero.pos widthBound)) _

end RandomRestriction
end AC0
end Algebraic
