import Algebraic.Basis.DeMorgan.StarBirth
import Algebraic.BooleanCube.AlexanderDual

/-!
# Obstructions beyond pairwise constant-link geometry

The exact input-cube links are pair determined at budget `n`. Failure at
any other budget is equivalent to a minimal hard exception pattern with
at least three directions. Their complements form maximal dual faces.
-/

namespace Algebraic.DeMorgan

/-- The constant link at the input-width budget is completely determined by its pairs. -/
theorem constantLink_pairDetermined (positive : 0 < n) (value : Bool) :
    BooleanCube.Complex.PairDetermined (constantLink n n value) := by
  intro support pairs
  have small : support.card ≤ 2 := by
    apply BooleanCube.card_le_two_of_pairwise_adjacent
    intro left hl right hr different
    apply (pair_mem_constantLink_iff positive value left right different).mp
    apply pairs {left, right}
    · intro point member
      rcases Finset.mem_insert.mp member with rfl | member
      · exact hl
      · simpa [Finset.mem_singleton.mp member] using hr
    · simp [different]
  exact pairs support (Finset.Subset.refl _) small

/-- Every failure of a pairwise description yields an irredundant hard pattern on at least three inputs. -/
theorem not_constantLink_pairDetermined_iff (n budget : Nat) (value : Bool) :
    ¬BooleanCube.Complex.PairDetermined (constantLink n budget value) ↔
      ∃ support : Finset (Fin n → Bool),
        BooleanCube.MinimalMissing {f | complexity f ≤ budget} (fun _ => value) support ∧ 2 < support.card :=
  BooleanCube.Complex.not_pairDetermined_iff _

/-- The Alexander dual of the constant link, with its augmented empty-face convention. -/
def constantLinkDual (n budget : Nat) (value : Bool) : Set (Finset (Fin n → Bool)) :=
  BooleanCube.Complex.dual (constantLink n budget value)

/-- Increasing the circuit budget shrinks the dual obstruction complex. -/
theorem constantLinkDual_antitone (n : Nat) (value : Bool) : Antitone (fun budget => constantLinkDual n budget value) := by
  intro small large included
  apply BooleanCube.Complex.dual_antitone
  exact BooleanCube.link_mono (fun _ member => member.trans included) _

/-- Maximal dual faces are precisely complements of minimal hard exception supports. -/
theorem constantLinkDual_facet_iff (n budget : Nat) (value : Bool) (support : Finset (Fin n → Bool)) :
    BooleanCube.Complex.Facet (constantLinkDual n budget value) supportᶜ ↔
      budget < complexity (BooleanCube.corner (fun _ => value) support) ∧
        ∀ part ⊂ support, complexity (BooleanCube.corner (fun _ => value) part) ≤ budget := by
  unfold constantLinkDual constantLink
  rw [← BooleanCube.Complex.minimalMissing_iff_facet_dual]
  exact BooleanCube.minimalMissing_sublevel_iff _ _ _ _

end Algebraic.DeMorgan
