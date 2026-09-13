import Algebraic.Basis.DeMorgan.StarAsymptotics
import Algebraic.Basis.DeMorgan.StarCycles
import Algebraic.Basis.DeMorgan.StarSubcube

/-!
# Downstream checks for circuit-complexity stars

The statements test the native cost model, both constant centers, actual
geometric intersection, and the Mathlib simplicial-complex interface.
-/

open Algebraic Algebraic.DeMorgan

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
    (f : ScalarFunction Bool n) (computes : circuit.ComputesWith DeMorgan.interpretation (fun input _ => f input)) :
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
