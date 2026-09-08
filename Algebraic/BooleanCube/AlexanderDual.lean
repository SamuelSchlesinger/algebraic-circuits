import Algebraic.BooleanCube.Link
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Alexander duals and minimal nonfaces

The combinatorial dual reverses membership after complementing the support.
Empty faces are retained, so the void family and the family containing only
the empty face remain distinct. This module proves the combinatorial
correspondence; its homological comparison belongs in a separate module.
-/

namespace Algebraic.BooleanCube.Complex

variable {ι : Type*}

/-- A support absent from a family whose every proper subset is present. -/
def MinimalNonface (faces : Set (Finset ι)) (support : Finset ι) : Prop :=
  support ∉ faces ∧ ∀ part ⊂ support, part ∈ faces

/-- A maximal face, including the empty face when it is the only face. -/
def Facet (faces : Set (Finset ι)) (support : Finset ι) : Prop :=
  support ∈ faces ∧ ∀ larger, support ⊂ larger → larger ∉ faces

/-- Every absent support contains a minimal nonface. -/
theorem exists_minimalNonface_subset (faces : Set (Finset ι)) (support : Finset ι)
    (missing : support ∉ faces) : ∃ part ⊆ support, MinimalNonface faces part := by
  classical
  induction support using Finset.strongInductionOn with
  | _ support ih =>
    by_cases proper : ∀ part ⊂ support, part ∈ faces
    · exact ⟨support, Finset.Subset.refl _, missing, proper⟩
    · push Not at proper
      obtain ⟨part, smaller, absent⟩ := proper
      obtain ⟨minimal, included, property⟩ := ih part smaller absent
      exact ⟨minimal, included.trans smaller.subset, property⟩

/-- The family is determined by its faces with at most two directions. -/
def PairDetermined (faces : Set (Finset ι)) : Prop :=
  ∀ support, (∀ part ⊆ support, part.card ≤ 2 → part ∈ faces) → support ∈ faces

/-- Pairwise determination is equivalent to the absence of larger minimal obstructions. -/
theorem pairDetermined_iff (faces : Set (Finset ι)) :
    PairDetermined faces ↔ ∀ support, MinimalNonface faces support → support.card ≤ 2 := by
  constructor
  · intro determined support missing
    by_contra large
    apply missing.1
    apply determined support
    intro part included small
    have different : part ≠ support := by intro equal; rw [equal] at small; omega
    exact missing.2 part (Finset.ssubset_iff_subset_ne.mpr ⟨included, different⟩)
  · intro small support pairs
    by_contra missing
    obtain ⟨part, included, minimal⟩ := exists_minimalNonface_subset faces support missing
    exact minimal.1 (pairs part included (small part minimal))

/-- Failure of a graph description has a concrete minimal obstruction of size at least three. -/
theorem not_pairDetermined_iff (faces : Set (Finset ι)) :
    ¬PairDetermined faces ↔ ∃ support, MinimalNonface faces support ∧ 2 < support.card := by
  rw [pairDetermined_iff]
  push Not
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- The combinatorial Alexander dual on the same finite ground set. -/
def dual (faces : Set (Finset ι)) : Set (Finset ι) := {support | supportᶜ ∉ faces}

/-- Membership in the dual means absence of the complementary support. -/
@[simp] theorem mem_dual (faces : Set (Finset ι)) (support : Finset ι) :
    support ∈ dual faces ↔ supportᶜ ∉ faces := Iff.rfl

/-- Combinatorial duality is an involution, including the void and full families. -/
@[simp] theorem dual_dual (faces : Set (Finset ι)) : dual (dual faces) = faces := by
  ext support
  simp [dual]

/-- Duality reverses inclusion of face families. -/
theorem dual_antitone : Antitone (@dual ι _ _) := by
  intro left right included support member present
  exact member (included present)

/-- The dual of a downward-closed family is downward closed. -/
theorem dual_downward (faces : Set (Finset ι))
    (downward : ∀ {left right}, left ⊆ right → right ∈ faces → left ∈ faces)
    {left right : Finset ι} (included : left ⊆ right) (member : right ∈ dual faces) :
    left ∈ dual faces := by
  intro present
  exact member (downward (Finset.compl_subset_compl.mpr included) present)

/-- Complementation exchanges minimal nonfaces and maximal dual faces. -/
theorem minimalNonface_iff_facet_dual (faces : Set (Finset ι)) (support : Finset ι) :
    MinimalNonface faces support ↔ Facet (dual faces) supportᶜ := by
  constructor
  · rintro ⟨missing, proper⟩
    refine ⟨by simpa using missing, ?_⟩
    intro larger strict member
    have smaller : largerᶜ ⊂ support := by
      simpa using (Finset.compl_ssubset_compl.mpr strict)
    exact member (proper largerᶜ smaller)
  · rintro ⟨member, maximal⟩
    refine ⟨by simpa using member, ?_⟩
    intro part smaller
    have absent := maximal partᶜ (Finset.compl_ssubset_compl.mpr smaller)
    simpa using absent

/-- The full family and the void family are exchanged by duality. -/
@[simp] theorem dual_univ : dual (Set.univ : Set (Finset ι)) = ∅ := by
  ext support
  simp [dual]

/-- The void family is dual to the full simplex. -/
@[simp] theorem dual_empty : dual (∅ : Set (Finset ι)) = Set.univ := by
  ext support
  simp [dual]

/-- Minimal missing faces of a cubical link correspond to facets of its Alexander dual. -/
theorem minimalMissing_iff_facet_dual (vertices : Set (ι → Bool)) (base : ι → Bool) (support : Finset ι) :
    MinimalMissing vertices base support ↔ Facet (dual (link vertices base)) supportᶜ :=
  minimalNonface_iff_facet_dual _ _

end Algebraic.BooleanCube.Complex
