import Algebraic.LowerBound.Fusion.Graph.Canonical
import Algebraic.LowerBound.Fusion.Neq

/-!
# Canonical graph Fusion regressions

The upper bound has its restricted admissibility class explicitly present.
The three-point example checks that an extension of a covered semi-filter
can preserve the same pair. Covering minimal witnesses does not suffice.
-/

namespace AlgebraicTests

open Algebraic.Fusion

example (graph : Set (Fin 16 × Fin 16)) :
    pairCoverComplexity (Graph.problem graph) (Graph.canonicalClass graph) ≤
      (128 : Nat) :=
  Graph.canonical_coverComplexity_le (n := 4) (by decide) graph

private def nonemptyFilter : Semifilter (Fin 3) where
  carrier := {set | set.Nonempty}
  nonempty := ⟨Set.univ, ⟨0, Set.mem_univ _⟩⟩
  upward := fun ⟨point, present⟩ inclusion => ⟨point, inclusion present⟩
  empty_not_mem := Set.not_nonempty_empty

private def testPair : Set (Fin 3) × Set (Fin 3) :=
  ({point | point ≠ 2}, {point | point ≠ 0})

example : ¬ (Semifilter.twoPoint (0 : Fin 3) 2).PreservesPair testPair := by
  intro preserves
  have leftAccepted : testPair.1 ∈ Semifilter.twoPoint (0 : Fin 3) 2 :=
    Or.inl (by change (0 : Fin 3) ≠ 2; decide)
  have rightAccepted : testPair.2 ∈ Semifilter.twoPoint (0 : Fin 3) 2 :=
    Or.inr (by change (2 : Fin 3) ≠ 0; decide)
  have intersectionAccepted := preserves leftAccepted rightAccepted
  change (0 ≠ (2 : Fin 3) ∧ 0 ≠ (0 : Fin 3)) ∨
    (2 ≠ (2 : Fin 3) ∧ 2 ≠ (0 : Fin 3)) at intersectionAccepted
  simp at intersectionAccepted

example : nonemptyFilter.PreservesPair testPair := by
  intro _ _
  exact ⟨1, by change (1 : Fin 3) ≠ 2; decide,
    by change (1 : Fin 3) ≠ 0; decide⟩

example : ∀ set ∈ Semifilter.twoPoint (0 : Fin 3) 2,
    set ∈ nonemptyFilter := by
  intro set present
  rcases present with left | right
  · exact ⟨0, left⟩
  · exact ⟨2, right⟩

end AlgebraicTests
