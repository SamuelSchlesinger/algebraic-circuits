import Algebraic.Basis.DeMorgan.StarBirth

/-!
# Face birth under circuit encodings

An injective encoder embeds all smaller-width Boolean functions into the
exception patterns on its image. A decoder and a membership circuit give
the converse construction. All three adapter costs count native gates.
-/

namespace Algebraic.DeMorgan

/-- Precomposing a scalar function with a multi-output circuit adds the adapter's native size. -/
theorem complexity_comp_le (function : ScalarFunction Bool m) (adapter : Circuit signature n e m) :
    complexity (fun input => function (adapter.eval interpretation input)) ≤ complexity function + e := by
  apply (complexity_le ((minimumCircuit function).circuit.comp adapter) ?_).trans_eq (Nat.add_comm _ _)
  intro input
  rw [Circuit.eval_comp]
  exact (minimumCircuit function).computes _

/-- The image support of an input encoding. -/
def encodingSupport (encode : (Fin m → Bool) → (Fin n → Bool)) : Finset (Fin n → Bool) :=
  Finset.univ.image encode

/-- Every encoded input belongs to the image support. -/
theorem mem_encodingSupport (encode : (Fin m → Bool) → (Fin n → Bool)) (input : Fin m → Bool) :
    encode input ∈ encodingSupport encode := Finset.mem_image.mpr ⟨input, Finset.mem_univ _, rfl⟩

/-- An injective encoding has precisely one support point per source assignment. -/
theorem card_encodingSupport (encode : (Fin m → Bool) → (Fin n → Bool)) (injective : Function.Injective encode) :
    (encodingSupport encode).card = 2 ^ m := by
  simp [encodingSupport, Finset.card_image_of_injective _ injective]

/-- Worst-case smaller-width complexity lower-bounds face birth on any injectively encoded support. -/
theorem maximumComplexity_le_faceBirth_add_encoder (encoder : Circuit signature m e n)
    (injective : Function.Injective (encoder.eval interpretation)) (value : Bool) :
    maximumComplexity m ≤ constantFaceBirth n value (encodingSupport (encoder.eval interpretation)) + e := by
  apply Finset.sup_le
  intro function _
  let subset := (Finset.univ.filter (fun input => function input ≠ value)).image (encoder.eval interpretation)
  have included : subset ⊆ encodingSupport (encoder.eval interpretation) :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have member (input : Fin m → Bool) : encoder.eval interpretation input ∈ subset ↔ function input ≠ value := by
    constructor
    · intro present
      obtain ⟨other, property, equal⟩ := Finset.mem_image.mp present
      have same := injective equal
      subst other
      exact (Finset.mem_filter.mp property).2
    · intro different
      exact Finset.mem_image.mpr ⟨input, Finset.mem_filter.mpr ⟨Finset.mem_univ _, different⟩, rfl⟩
  have identity : (fun input => BooleanCube.corner (fun _ => value) subset (encoder.eval interpretation input)) =
      function := by
    funext input
    simp only [BooleanCube.corner, member]
    cases result : function input <;> cases value <;> simp
  have composed := complexity_comp_le (BooleanCube.corner (fun _ => value) subset) encoder
  rw [identity] at composed
  exact composed.trans (Nat.add_le_add_right (complexity_corner_le_constantFaceBirth value included) e)

private theorem complexity_eval_zero_le (circuit : Circuit signature n g 1) :
    complexity (fun input => circuit.eval interpretation input 0) ≤ g := by
  apply complexity_le circuit
  intro input
  funext output
  have zero : output = 0 := Subsingleton.elim _ _
  simp [zero]

/-- Decoding and recognizing an encoded support bound the complexity of every exception pattern on it. -/
theorem complexity_corner_encodingSupport_le (encode : (Fin m → Bool) → (Fin n → Bool))
    (decoder : Circuit signature n d m) (tester : Circuit signature n t 1)
    (decodes : ∀ input, decoder.eval interpretation (encode input) = input)
    (recognizes : ∀ input, tester.eval interpretation input 0 = decide (input ∈ encodingSupport encode))
    (value : Bool) {subset : Finset (Fin n → Bool)} (included : subset ⊆ encodingSupport encode) :
    complexity (BooleanCube.corner (fun _ => value) subset) ≤ maximumComplexity m + d + t + 2 := by
  let target := BooleanCube.corner (fun _ => value) subset
  let residual : ScalarFunction Bool m := fun input => target (encode input)
  let mask : ScalarFunction Bool n := fun input => tester.eval interpretation input 0
  let decoded : ScalarFunction Bool n := fun input => residual (decoder.eval interpretation input)
  have residualBound : complexity decoded ≤ maximumComplexity m + d :=
    (complexity_comp_le residual decoder).trans (Nat.add_le_add_right (complexity_le_maximumComplexity residual) d)
  have maskBound : complexity mask ≤ t := complexity_eval_zero_le tester
  have negated := complexity_not_le mask
  have identity : target = fun input => if value then !(mask input) || decoded input
      else mask input && decoded input := by
    funext input
    by_cases present : input ∈ encodingSupport encode
    · obtain ⟨original, _, equal⟩ := Finset.mem_image.mp present
      have restored : encode (decoder.eval interpretation input) = input := by
        rw [← equal, decodes]
      have maskTrue : mask input = true := by simp [mask, recognizes, present]
      cases value <;> simp [maskTrue, decoded, residual, restored]
    · have absent : input ∉ subset := fun member => present (included member)
      have maskFalse : mask input = false := by simp [mask, recognizes, present]
      cases value <;> simp [target, BooleanCube.corner, absent, maskFalse]
  have joinedAnd := complexity_and_le mask decoded
  have joinedOr := complexity_or_le (fun input => !(mask input)) decoded
  change complexity target ≤ _
  rw [identity]
  cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Efficient decoding and membership testing control the birth of the whole encoded face. -/
theorem constantFaceBirth_encodingSupport_le (encode : (Fin m → Bool) → (Fin n → Bool))
    (decoder : Circuit signature n d m) (tester : Circuit signature n t 1)
    (decodes : ∀ input, decoder.eval interpretation (encode input) = input)
    (recognizes : ∀ input, tester.eval interpretation input 0 = decide (input ∈ encodingSupport encode))
    (value : Bool) :
    constantFaceBirth n value (encodingSupport encode) ≤ maximumComplexity m + d + t + 2 := by
  apply Finset.sup_le
  intro subset member
  exact complexity_corner_encodingSupport_le encode decoder tester decodes recognizes value
    (Finset.mem_powerset.mp member)

end Algebraic.DeMorgan
