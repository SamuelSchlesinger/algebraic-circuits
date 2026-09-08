import Algebraic.Basis.DeMorgan.StarBirth

/-!
# Large constant-star faces on structured supports

Fixing `k` input coordinates leaves `2^d` truth-table directions. Every
exception pattern on this support costs at most the worst-case complexity
on `d` inputs plus `k+1` gates, when `k` is positive. This applies to either
constant center and counts the mask and its output gate explicitly.
-/

namespace Algebraic.DeMorgan

/-- The input subcube with a fixed initial segment and an arbitrary `d`-bit suffix. -/
def inputSubcube (fixed : Fin k → Bool) (d : Nat) : Finset (Fin (k + d) → Bool) :=
  Finset.univ.image (Fin.append fixed)

/-- Input-subcube membership means agreement on precisely the fixed coordinates. -/
theorem mem_inputSubcube_iff (fixed : Fin k → Bool) (input : Fin (k + d) → Bool) :
    input ∈ inputSubcube fixed d ↔ ∀ i, input (Fin.castAdd d i) = fixed i := by
  constructor
  · intro member
    obtain ⟨suffix, _, rfl⟩ := Finset.mem_image.mp member
    simp
  · intro agree
    refine Finset.mem_image.mpr ⟨input ∘ Fin.natAdd k, Finset.mem_univ _, ?_⟩
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using (agree j).symm
    · intro j
      simp

/-- A `d`-dimensional input subcube supplies exactly `2^d` truth-table directions. -/
@[simp] theorem card_inputSubcube (fixed : Fin k → Bool) (d : Nat) :
    (inputSubcube fixed d).card = 2 ^ d := by
  have injective : Function.Injective (Fin.append fixed : (Fin d → Bool) → (Fin (k + d) → Bool)) := by
    intro left right equal
    funext i
    simpa using congrFun equal (Fin.natAdd k i)
  simp [inputSubcube, Finset.card_image_of_injective _ injective]

/-- Every exception pattern inside an input subcube has a circuit using a smaller-width residual. -/
theorem complexity_corner_inputSubcube_le (positive : 0 < k) (fixed : Fin k → Bool)
    (value : Bool) {subset : Finset (Fin (k + d) → Bool)} (included : subset ⊆ inputSubcube fixed d) :
    complexity (BooleanCube.corner (fun _ => value) subset) ≤ maximumComplexity d + k + 1 := by
  let target := BooleanCube.corner (fun _ => value) subset
  let residual : ScalarFunction Bool d := fun suffix => target (Fin.append fixed suffix)
  let restrictedMask : ScalarFunction Bool (k + d) :=
    fun input => mask Finset.univ fixed (!value) (input ∘ Fin.castAdd d)
  have maskBound : complexity restrictedMask ≤ k := by
    have rewired := complexity_mapInputs_le (mask Finset.univ fixed (!value)) (Fin.castAdd d)
    have bounded := complexity_mask_le Finset.univ fixed (!value)
    simp only [Finset.card_univ, Fintype.card_fin, Nat.max_eq_right positive] at bounded
    exact rewired.trans bounded
  have residualBound : complexity (fun input => residual (input ∘ Fin.natAdd k)) ≤ maximumComplexity d :=
    (complexity_mapInputs_le residual (Fin.natAdd k)).trans (complexity_le_maximumComplexity residual)
  have identity : target = fun input =>
      if value then restrictedMask input || residual (input ∘ Fin.natAdd k)
      else restrictedMask input && residual (input ∘ Fin.natAdd k) := by
    funext input
    by_cases agree : ∀ i, input (Fin.castAdd d i) = fixed i
    · have restored : Fin.append fixed (input ∘ Fin.natAdd k) = input := by
        funext i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simpa using (agree j).symm
        · intro j
          simp
      simp only [Function.comp_def] at restored
      cases value <;> simp [restrictedMask, mask, Function.comp_def, agree, residual, restored]
    · have absent : input ∉ subset := by
        intro member
        exact agree ((mem_inputSubcube_iff fixed input).mp (included member))
      cases value <;> simp [restrictedMask, mask, Function.comp_def, agree, target,
        BooleanCube.corner, absent]
  have andBound := complexity_and_le restrictedMask (fun input => residual (input ∘ Fin.natAdd k))
  have orBound := complexity_or_le restrictedMask (fun input => residual (input ∘ Fin.natAdd k))
  change complexity target ≤ _
  rw [identity]
  cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Structured supports can form exponentially large faces at a smaller-width circuit budget. -/
theorem constantFaceBirth_inputSubcube_le (positive : 0 < k) (fixed : Fin k → Bool)
    (value : Bool) (d : Nat) :
    constantFaceBirth (k + d) value (inputSubcube fixed d) ≤ maximumComplexity d + k + 1 := by
  apply Finset.sup_le
  intro subset member
  exact complexity_corner_inputSubcube_le positive fixed value (Finset.mem_powerset.mp member)

/-- Fixing `k` inputs leaves a full `2^d`-direction face by budget `M(d)+2*k`. -/
theorem inputSubcube_mem_constantLink (positive : 0 < k) (fixed : Fin k → Bool)
    (value : Bool) (d : Nat) :
    inputSubcube fixed d ∈ constantLink (k + d) (maximumComplexity d + 2 * k) value := by
  apply (mem_constantLink_iff_birth_le _ _ _ _).mpr
  have bound := constantFaceBirth_inputSubcube_le positive fixed value d
  omega

end Algebraic.DeMorgan
