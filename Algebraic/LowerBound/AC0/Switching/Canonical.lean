import Algebraic.LowerBound.AC0.Switching.CanonicalEncoding

/-!
# The canonical DNF switching injection

This module packages the trace-level replay decoder into a single injection on
the canonical-depth bad event. For each bad restriction, classical choice
selects an exact-length path supplied by the structural depth theorem and the
typed source-term trace proved for that path. This is proof-level witness
selection, not enumeration or optimization.

The resulting encoder extends the bad restriction by the trace's satisfying
assignment and stores one bounded position and two bits per path query. The
explicit decoder is a left inverse, hence the encoder is injective on the bad
event.
-/

namespace Algebraic
namespace AC0
namespace Switching

/-- A chosen exact-length canonical path witnessing the bad event. -/
noncomputable def chosenPath
    (formula : DNF n)
    (rho : PartialAssignment n)
    (pathLength : Nat)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    DNF.CanonicalPath formula rho pathLength :=
  Classical.choice (formula.exists_canonicalPath rho pathLength deep)

/-- The chosen source-term block trace carried by `chosenPath`. -/
noncomputable def chosenTrace
    (formula : DNF n)
    (rho : PartialAssignment n)
    (pathLength : Nat)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    DNF.CanonicalTrace formula rho
      (chosenPath formula rho pathLength deep).steps :=
  Classical.choice (formula.canonicalTrace_of_path rho
    (chosenPath formula rho pathLength deep).follows)

/-- A harmless total advice value used outside the bad event. -/
def defaultAdvice
    [NeZero widthBound]
    (pathLength : Nat) : Advice widthBound pathLength :=
  fun _ => ⟨Fin.ofNat widthBound 0, false, false⟩

/-- Satisfying extension chosen for a bad restriction; the empty assignment is
used outside the event to keep the probability encoder total. -/
noncomputable def canonicalExtension
    {widthBound : Nat}
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n) : PartialAssignment n :=
  if deep : formula.CanonicalDepthAtLeast rho pathLength then
    (chosenTrace formula rho pathLength deep).satisfyingAssignment
      (widthBound := widthBound)
  else
    PartialAssignment.empty

/-- Total restriction/advice encoding used by the canonical switching
injection. -/
noncomputable def canonicalEncoding
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n) :
    PartialAssignment n × Advice widthBound pathLength :=
  if deep : formula.CanonicalDepthAtLeast rho pathLength then
    let path := chosenPath formula rho pathLength deep
    let trace := chosenTrace formula rho pathLength deep
    (rho.refine
        (trace.satisfyingAssignment (widthBound := widthBound)),
      trace.advice (widthBound := widthBound) path.length_steps)
  else
    (rho, defaultAdvice pathLength)

/-- On the bad event, the encoding output restriction is refinement by the
chosen satisfying extension. -/
theorem canonicalEncoding_fst_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (canonicalEncoding (widthBound := widthBound) formula pathLength rho).1 =
      rho.refine
        (canonicalExtension (widthBound := widthBound) formula pathLength rho) := by
  simp [canonicalEncoding, canonicalExtension, deep]

/-- The chosen extension fixes exactly the requested path length. -/
theorem canonicalExtension_fixedCount_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (canonicalExtension (widthBound := widthBound)
      formula pathLength rho).fixedCount = pathLength := by
  simp only [canonicalExtension, dif_pos deep]
  exact (chosenPath formula rho pathLength deep).satisfyingAssignment_fixedCount
    (chosenTrace formula rho pathLength deep)

/-- The chosen extension fixes only coordinates live in the bad restriction.
-/
theorem canonicalExtension_fixesOnlyLive_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (canonicalExtension (widthBound := widthBound)
      formula pathLength rho).fixedVariables ⊆ rho.liveVariables := by
  simp only [canonicalExtension, dif_pos deep]
  exact (chosenPath formula rho pathLength deep).satisfyingAssignment_fixesOnlyLive
    (chosenTrace formula rho pathLength deep)

/-- The explicit decoder recovers every restriction in the bad event from its
chosen encoding. -/
theorem decode_canonicalEncoding_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    decode formula
      (canonicalEncoding (widthBound := widthBound) formula pathLength rho) =
      rho := by
  simp only [canonicalEncoding, dif_pos deep]
  exact (chosenPath formula rho pathLength deep).decode_satisfyingEncoding
    (chosenTrace formula rho pathLength deep) bounded

/-- The canonical encoder is injective when restricted to the canonical-depth
bad event. -/
theorem canonicalEncoding_injectiveOn_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat) :
    ∀ left, formula.CanonicalDepthAtLeast left pathLength →
      ∀ right, formula.CanonicalDepthAtLeast right pathLength →
        canonicalEncoding (widthBound := widthBound)
            formula pathLength left =
          canonicalEncoding (widthBound := widthBound)
            formula pathLength right →
          left = right := by
  intro left leftDeep right rightDeep equal
  have decodedEqual := congrArg (decode formula) equal
  rw [decode_canonicalEncoding_of_deep formula bounded pathLength left leftDeep,
    decode_canonicalEncoding_of_deep formula bounded pathLength right
      rightDeep] at decodedEqual
  exact decodedEqual

end Switching

namespace RandomRestriction

open scoped ENNReal

/-- Exact division-free canonical switching bound. The factor `(4t)^s` is the
cardinality of one bounded position and two bits for each of the `s` path
queries. -/
theorem probability_canonicalDepthAtLeast_scaled_le
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ pathLength *
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((4 * widthBound : Nat) : ENNReal) ^ pathLength *
        (p : ENNReal) ^ pathLength := by
  have encoded := probability_scaled_le_of_refinement_encoding
    n p atMostOne
    (fun rho => formula.CanonicalDepthAtLeast rho pathLength)
    (Switching.Advice widthBound pathLength) pathLength
    (Switching.canonicalExtension (widthBound := widthBound)
      formula pathLength)
    (Switching.canonicalEncoding (widthBound := widthBound)
      formula pathLength)
    (Switching.canonicalEncoding_injectiveOn_deep
      formula bounded pathLength)
    (Switching.canonicalEncoding_fst_of_deep
      (widthBound := widthBound) formula pathLength)
    (Switching.canonicalExtension_fixesOnlyLive_of_deep
      (widthBound := widthBound) formula pathLength)
    (Switching.canonicalExtension_fixedCount_of_deep
      (widthBound := widthBound) formula pathLength)
  rw [Switching.card_advice] at encoded
  simpa only [Nat.cast_pow] using encoded

end RandomRestriction
end AC0
end Algebraic
