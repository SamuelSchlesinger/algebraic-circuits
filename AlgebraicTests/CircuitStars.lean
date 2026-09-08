import Algebraic.Basis.DeMorgan.StarAsymptotics
import Algebraic.Basis.DeMorgan.StarCycles
import Algebraic.Basis.DeMorgan.StarSubcube
import Algebraic.Basis.DeMorgan.StarRepetition
import Algebraic.Basis.DeMorgan.StarTranslation
import Algebraic.Basis.DeMorgan.ApproximationGeometry
import Algebraic.Basis.DeMorgan.StarDuality

/-!
# Downstream checks for circuit-complexity stars

The statements test the native cost model, both constant centers, actual
geometric intersection, and the Mathlib simplicial-complex interface.
-/

open Algebraic Algebraic.DeMorgan

noncomputable section

example (positive : 0 < n) (center : Bool) :
    constantLinkGraph n n center = BooleanCube.graph :=
  constantLinkGraph_eq_cube positive center

example (positive : 0 < n) (center : Bool) (point : Fin n → Bool) :
    {point} ∈ constantLinkComplex n n center := by
  exact ⟨Finset.singleton_nonempty point, singleton_mem_constantLink positive center point⟩

example (center : Bool) :
    {(![false, false] : Fin 2 → Bool), ![true, true]} ∉ constantLink 2 2 center := by
  rw [pair_mem_constantLink_iff (by decide) center _ _ (by decide)]
  change hammingDist (![false, false] : Fin 2 → Bool) ![true, true] ≠ 1
  decide

example (center : Bool) : constantLinkFaceCount 3 3 center 1 = 8 := by
  rw [constantLinkFaceCount_one (by decide)]
  norm_num

example (center : Bool) : constantLinkFaceCount 3 3 center 2 = 12 := by
  rw [constantLinkFaceCount_two (by decide)]
  norm_num

example (center : Bool) : constantLinkFaceCount 3 3 center 3 = 0 :=
  constantLinkFaceCount_eq_zero (by decide) center (by decide)

example (center : Bool) : constantLinkCycleRank ℚ (by decide : 0 < 3) center = 5 := by
  rw [constantLinkCycleRank_eq]
  norm_num

example (center : Bool) : constantLinkCycleRank ℚ (by decide : 0 < 4) center = 17 := by
  rw [constantLinkCycleRank_eq]
  norm_num

example : BooleanCube.GraphCycles.cycleRank ℚ 0 = 0 := by
  rw [BooleanCube.GraphCycles.cycleRank_eq]
  norm_num

example (center : Bool) : constantLinkCycleRank ℚ (by decide : 0 < 1) center = 0 := by
  rw [constantLinkCycleRank_eq]
  norm_num

example (center : Bool) :
    {(![false, false] : Fin 2 → Bool), ![true, false]} ∈ constantLink 2 2 center := by
  rw [pair_mem_constantLink_iff (by decide) center _ _ (by decide)]
  change hammingDist (![false, false] : Fin 2 → Bool) ![true, false] = 1
  decide

example (n : Nat) : maximumComplexity n ≤ 2 * constantStarMeeting n + 2 :=
  maximumComplexity_le_twice_constantStarMeeting n

example (n : Nat) : constantStarMeeting (n + 1) ≤ maximumComplexity n + 1 :=
  constantStarMeeting_succ_le n

example (n budget : Nat)
    (meet : (BooleanCube.closedStar {f : ScalarFunction Bool n | complexity f ≤ budget}
      (fun _ => false) ∩ BooleanCube.closedStar {f | complexity f ≤ budget}
        (fun _ => true)).Nonempty) : maximumComplexity n ≤ 2 * budget + 2 :=
  maximumComplexity_le_of_constant_star_intersection budget meet

example : ∀ᶠ n in Filter.atTop,
    2 ^ n ≤ 4 * n * constantStarMeeting n ∧ n * constantStarMeeting n ≤ 32 * 2 ^ n :=
  eventually_constantStarMeeting_bounds

example (center : Bool) (directions : Finset (Fin n → Bool)) :
    constantFaceBirth n (!center) directions ≤ constantFaceBirth n center directions + 1 :=
  constantFaceBirth_complement_le center directions

example (circuit : Circuit DeMorgan.signature n g 1)
    (f : ScalarFunction Bool n) (computes : circuit.Computes DeMorgan.interpretation (fun input _ => f input)) :
    complexity f ≤ circuit.cost DeMorgan.standardCost + 2 :=
  complexity_le_standardCost_add_two circuit computes

example (n : Nat) (base : Fin n → Bool) (vertices : Set (Fin n → Bool)) (admitted : base ∈ vertices) :
    ContractibleSpace (BooleanCube.closedStar vertices base) :=
  BooleanCube.closedStar_contractible vertices base admitted

example (center : Bool) :
    ContractibleSpace (BooleanCube.closedStar
      {function : ScalarFunction Bool n | complexity function ≤ n + 1} (fun _ => center)) :=
  constantStar_contractible n center (by omega)

example (fixed : Fin k → Bool) (d : Nat) : (inputSubcube fixed d).card = 2 ^ d :=
  card_inputSubcube fixed d

example (positive : 0 < k) (fixed : Fin k → Bool) (center : Bool) (d : Nat) :
    constantFaceBirth (k + d) center (inputSubcube fixed d) ≤ maximumComplexity d + k + 1 :=
  constantFaceBirth_inputSubcube_le positive fixed center d

example (fixed : Fin 2 → Bool) (center : Bool) :
    inputSubcube fixed 4 ∈ constantLink 6 (maximumComplexity 4 + 4) center :=
  inputSubcube_mem_constantLink (by decide) fixed center 4

example (n budget : Nat) (center : Bool) (directions : Finset (Fin n → Bool))
    (missing : directions ∉ constantLink n budget center) :
    ∃ subset ⊆ directions,
      budget < complexity (BooleanCube.corner (fun _ => center) subset) ∧
        ∀ part ⊂ subset, complexity (BooleanCube.corner (fun _ => center) part) ≤ budget :=
  exists_minimal_hard_support n budget center directions missing

example (value : Bool) :
    maximumComplexity 3 ≤ constantFaceBirth 6 value (repetitionSupport 3) ∧
      constantFaceBirth 6 value (repetitionSupport 3) ≤ maximumComplexity 3 + 18 :=
  ⟨maximumComplexity_le_repetition_birth 3 value, repetition_birth_le 3 value⟩

example : (repetitionSupport 3).card = 8 := by rw [card_repetitionSupport]; norm_num

example : (![false, true, false, false, true, false] : Fin 6 → Bool) ∈ repetitionSupport 3 := by
  rw [mem_repetitionSupport_iff]
  decide

example : (![false, true, false, false, false, false] : Fin 6 → Bool) ∉ repetitionSupport 3 := by
  rw [mem_repetitionSupport_iff]
  decide

example (fixed : Fin 5 → Bool) (value : Bool) :
    maximumComplexity 3 ≤ constantFaceBirth 8 value (inputSubcube fixed 3) + 2 :=
  maximumComplexity_le_inputSubcube_birth_add_two fixed 3 value

example (left right : ScalarFunction Bool n) :
    complexity (fun input => Bool.xor (left input) (right input)) ≤ complexity left + complexity right + 4 :=
  complexity_xor_le left right

example (function : ScalarFunction Bool n) :
    approximationDistance function 1 (by omega) = 0 ↔ complexity function ≤ 1 :=
  approximationDistance_eq_zero function 1 (by omega)

example : (BooleanCube.ball (fun _ : Fin 3 => false) 1).card = 4 := by
  rw [BooleanCube.card_ball]
  norm_num [Finset.sum_range_succ]

example (vertices : Finset (Fin 3 → Bool)) :
    (BooleanCube.neighborhood vertices 1).card ≤ vertices.card * 4 := by
  simpa [Finset.sum_range_succ] using BooleanCube.card_neighborhood_le vertices 1

example : ¬BooleanCube.Complex.PairDetermined {support : Finset (Fin 3) | support.card ≤ 2} := by
  rw [BooleanCube.Complex.not_pairDetermined_iff]
  refine ⟨Finset.univ, ?_, by decide⟩
  unfold BooleanCube.Complex.MinimalNonface
  decide

example : BooleanCube.Complex.Facet
    (BooleanCube.Complex.dual {support : Finset (Fin 3) | support.card ≤ 2}) ∅ := by
  have missing : BooleanCube.Complex.MinimalNonface
      {support : Finset (Fin 3) | support.card ≤ 2} Finset.univ := by
    unfold BooleanCube.Complex.MinimalNonface
    decide
  simpa using (BooleanCube.Complex.minimalNonface_iff_facet_dual _ _).mp missing

open BooleanCube.SimplicialF2 in
example (value : Bool) :
    ReducedHomology (constantLink 3 5 value) 1 ≃ₗ[ZMod 2]
      ReducedCohomology (constantLinkDual 3 5 value) 4 :=
  constantLinkAlexanderDuality 3 5 value 1

open BooleanCube.SimplicialF2 in
example : ReducedHomology (∅ : Set (Finset (Fin 1))) (-1) ≃ₗ[ZMod 2]
    ReducedCohomology (BooleanCube.Complex.dual (∅ : Set (Finset (Fin 1)))) (-1) :=
  reducedAlexanderDuality 0 ∅ (by simp) (-1)

open BooleanCube.SimplicialF2 in
example (chain : Chains (Fin 3)) : boundary (boundary chain) = 0 := boundary_boundary chain

open BooleanCube.SimplicialF2 in
example : boundary (fun support : Finset (Fin 3) => if support.card = 2 then (1 : ZMod 2) else 0) = 0 := by
  decide
