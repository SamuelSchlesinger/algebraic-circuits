import Algebraic.BooleanCube.Boundary
import Algebraic.BooleanCube.Neighbors
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Cycle rank of the input-cube graph

The graph is treated as one-dimensional: there are vertex and edge chains,
and no square fillings. The boundary of an edge is its true endpoint minus
its false endpoint. Its kernel has dimension `n*2^(n-1)+1-2^n` over any field.
-/

namespace Algebraic.BooleanCube.GraphCycles

open scoped BigOperators

/-- Canonically oriented edges of the Boolean input cube. -/
abbrev Edge (n : Nat) := {edge : (Fin n → Bool) × Fin n // edge ∈ BooleanCube.edges}

variable (K : Type*) [Field K]

/-- The oriented graph boundary on finite edge chains. -/
noncomputable def boundary (n : Nat) : (Edge n →₀ K) →ₗ[K] ((Fin n → Bool) →₀ K) :=
  Finsupp.linearCombination K (fun edge =>
    Finsupp.single (edgeEnd edge.val) 1 - Finsupp.single edge.val.1 1)

/-- Sum the coefficients of a vertex chain. -/
noncomputable def total (n : Nat) : ((Fin n → Bool) →₀ K) →ₗ[K] K :=
  Finsupp.linearCombination K (fun _ => (1 : K))

/-- Graph cycles are exactly the edge chains with zero boundary. -/
noncomputable abbrev CycleSpace (n : Nat) := LinearMap.ker (boundary K n)

/-- Number of independent cycles in the one-dimensional input-cube graph. -/
noncomputable def cycleRank (n : Nat) : Nat := Module.finrank K (CycleSpace K n)

/-- The boundary of a single oriented edge is the difference of its endpoints. -/
@[simp] theorem boundary_single (edge : Edge n) (a : K) :
    boundary K n (Finsupp.single edge a) =
      a • (Finsupp.single (edgeEnd edge.val) 1 - Finsupp.single edge.val.1 1) := by
  simp [boundary]

/-- A single vertex chain has its stated total coefficient. -/
@[simp] theorem total_single (vertex : Fin n → Bool) (a : K) :
    total K n (Finsupp.single vertex a) = a := by
  simp [total]

/-- Every edge boundary has total coefficient zero. -/
theorem total_boundary (chain : Edge n →₀ K) : total K n (boundary K n chain) = 0 := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add left right hl hr => simp [hl, hr]
  | single edge a => simp

private theorem flip_difference_mem_range (vertex : Fin n → Bool) (i : Fin n) :
    Finsupp.single (flip vertex i) (1 : K) - Finsupp.single vertex 1 ∈ LinearMap.range (boundary K n) := by
  classical
  cases value : vertex i
  · let edge : Edge n := ⟨(vertex, i), by simp [BooleanCube.edges, value]⟩
    refine ⟨Finsupp.single edge 1, ?_⟩
    simp [edge, edgeEnd, flip, value]
  · let other := flip vertex i
    let edge : Edge n := ⟨(other, i), by simp [BooleanCube.edges, other, flip, value]⟩
    have endpoint : edgeEnd edge.val = vertex := by
      funext j
      by_cases same : j = i <;> simp [edgeEnd, edge, other, flip, same, value]
    refine ⟨Finsupp.single edge (-1), ?_⟩
    simp [endpoint, edge, other]

/-- Every difference from the zero vertex is a graph boundary. -/
theorem difference_mem_range (vertex : Fin n → Bool) :
    Finsupp.single vertex (1 : K) - Finsupp.single (fun _ => false) 1 ∈ LinearMap.range (boundary K n) := by
  classical
  apply BooleanCube.update_induction (fun _ => false) vertex
    (fun current => Finsupp.single current (1 : K) - Finsupp.single (fun _ => false) 1 ∈
      LinearMap.range (boundary K n)) (by simp)
  intro current i value previous
  by_cases same : value = current i
  · simpa [same] using previous
  · have opposite : value = !(current i) := by cases value <;> cases h : current i <;> simp_all
    have step := flip_difference_mem_range K current i
    have sum := (LinearMap.range (boundary K n)).add_mem step previous
    simpa [flip, opposite] using sum

/-- The incidence image is precisely the space of vertex chains with total coefficient zero. -/
theorem range_boundary_eq_ker_total (n : Nat) :
    LinearMap.range (boundary K n) = LinearMap.ker (total K n) := by
  classical
  apply le_antisymm
  · rintro _ ⟨chain, rfl⟩
    exact total_boundary K chain
  · intro chain zero
    have coefficients : ∑ vertex ∈ chain.support, chain vertex = 0 := by
      simpa [total, Finsupp.linearCombination_apply, Finsupp.sum] using zero
    have supported :
        (∑ vertex ∈ chain.support, chain vertex •
          (Finsupp.single vertex (1 : K) - Finsupp.single (fun _ => false) 1)) ∈
            LinearMap.range (boundary K n) := by
      apply Submodule.sum_mem
      intro vertex _
      exact Submodule.smul_mem _ _ (difference_mem_range K vertex)
    have identity :
        (∑ vertex ∈ chain.support, chain vertex •
          (Finsupp.single vertex (1 : K) - Finsupp.single (fun _ => false) 1)) = chain := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, coefficients, zero_smul, sub_zero]
      simpa only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum] using chain.sum_single
    simpa [identity] using supported

/-- The total-coefficient map is onto the coefficient field. -/
theorem total_surjective (n : Nat) : Function.Surjective (total K n) := by
  intro a
  exact ⟨Finsupp.single (fun _ => false) a, total_single K _ a⟩

/-- Euler's graph identity for the cube, expressed without truncated subtraction. -/
theorem cycleRank_add_vertices (n : Nat) :
    cycleRank K n + 2 ^ n = n * 2 ^ (n - 1) + 1 := by
  classical
  have vertices : Module.finrank K (LinearMap.range (total K n)) +
      Module.finrank K (LinearMap.ker (total K n)) = Module.finrank K ((Fin n → Bool) →₀ K) :=
    (total K n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (total_surjective K n)] at vertices
  have edges : Module.finrank K (LinearMap.range (boundary K n)) + cycleRank K n =
      Module.finrank K (Edge n →₀ K) := (boundary K n).finrank_range_add_finrank_ker
  rw [range_boundary_eq_ker_total] at edges
  have count : Fintype.card (Edge n) = n * 2 ^ (n - 1) := by
    simpa [Edge] using (BooleanCube.card_edges (ι := Fin n))
  simp only [finrank_top, Module.finrank_self, Module.finrank_finsupp_self,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at vertices
  simp only [Module.finrank_finsupp_self, count] at edges
  omega

/-- The number of independent link-graph loops, valid also in dimensions zero and one. -/
theorem cycleRank_eq (n : Nat) : cycleRank K n = n * 2 ^ (n - 1) + 1 - 2 ^ n := by
  have identity := cycleRank_add_vertices K n
  omega

end Algebraic.BooleanCube.GraphCycles
