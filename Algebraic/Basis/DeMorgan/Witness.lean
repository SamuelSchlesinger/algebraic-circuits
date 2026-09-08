import Algebraic.Basis.DeMorgan.Betti
import Algebraic.BooleanCube.Witness

/-!
# Localized circuit lower-bound witnesses

A nonbounding cycle yields an actual Boolean function in the next `n` cost
levels, selected from a finite list of prefix erasures. Uniform circuit
reductions from that list to a target transfer the lower bound to the target.
The nonbounding certificate and reductions remain explicit hypotheses.
-/

namespace Algebraic.DeMorgan

variable (R : Type*) [CommRing R]

/-- The actual Boolean functions in a cycle's finite erasure candidate list. -/
noncomputable def erasureFunctions (n : Nat) (chain : BooleanCube.Chains R (2 ^ n)) :
    Finset (ScalarFunction Bool n) :=
  (BooleanCube.Chains.erasureVertices R chain).map (truthTableEquiv n).toEmbedding

/-- Membership transports the finite vertex list through the truth-table equivalence. -/
@[simp] theorem mem_erasureFunctions (n : Nat) (chain : BooleanCube.Chains R (2 ^ n))
    (function : ScalarFunction Bool n) :
    function ∈ erasureFunctions R n chain ↔
      (truthTableEquiv n).symm function ∈ BooleanCube.Chains.erasureVertices R chain := by
  classical
  simp [erasureFunctions]

/-- A nonbounding circuit cycle yields a shell function in its explicit erasure list. -/
theorem exists_shell_function_of_cycle (positive : 0 < n) (budget degree : Nat)
    (degreePositive : 0 < degree) (chain : BooleanCube.Chains R (2 ^ n))
    (closed : chain ∈ BooleanCube.Chains.cycles R {vector | orderedComplexity n vector ≤ budget} degree)
    (nonboundary : chain ∉ BooleanCube.Chains.boundaries R
      {vector | orderedComplexity n vector ≤ budget} degree) :
    ∃ function ∈ erasureFunctions R n chain, function ∈ complexityShell n budget := by
  obtain ⟨vector, candidate, outside⟩ := BooleanCube.Chains.exists_erasure_vertex_not_mem R
    _ _ degree degreePositive chain closed nonboundary
  refine ⟨truthTableEquiv n vector, ?_, ?_⟩
  · simpa using candidate
  · apply (mem_complexityShell n budget _).mpr
    refine ⟨Nat.lt_of_not_ge outside, ?_⟩
    obtain ⟨threshold, _, original, member, rfl⟩ :=
      (BooleanCube.Chains.mem_erasureVertices R chain vector).mp candidate
    exact (orderedComplexity_erase_le positive threshold original).trans
      (Nat.add_le_add_right (BooleanCube.Chains.vertices_subset R closed.1 member) n)

/-- Uniform reductions of every uncertified candidate transfer a cycle witness to one target. -/
theorem complexity_add_overhead_gt_of_cycle (positive : 0 < n) (budget degree overhead : Nat)
    (degreePositive : 0 < degree) (chain : BooleanCube.Chains R (2 ^ n))
    (closed : chain ∈ BooleanCube.Chains.cycles R {vector | orderedComplexity n vector ≤ budget} degree)
    (nonboundary : chain ∉ BooleanCube.Chains.boundaries R
      {vector | orderedComplexity n vector ≤ budget} degree)
    (target : ScalarFunction Bool n)
    (reduces : ∀ function ∈ erasureFunctions R n chain,
      complexity function ≤ budget ∨ complexity function ≤ complexity target + overhead) :
    budget < complexity target + overhead := by
  obtain ⟨function, candidate, shell⟩ := exists_shell_function_of_cycle R positive budget degree
    degreePositive chain closed nonboundary
  have hard := ((mem_complexityShell n budget function).mp shell).1
  rcases reduces function candidate with easy | reduced
  · omega
  · exact hard.trans_le reduced

end Algebraic.DeMorgan
