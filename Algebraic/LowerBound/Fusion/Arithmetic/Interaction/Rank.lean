import Algebraic.LowerBound.Fusion.Arithmetic.Interaction
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Rank bounds from arithmetic interaction spans

When an interaction certificate takes values in a space of linear maps, rank
turns its span theorem into a multiplication lower bound.  If every product
interaction has rank at most `r`, a target feature of rank at least `R`
requires at least `ceil(R / r)` multiplication gates.

This result is agnostic about the source of the feature.  Matrix
flattenings, shifted Hessians, and derivative spaces can share the same
circuit argument.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Rank

open Cardinal

variable {K : Type u} {C : Type v} {U : Type w}
variable {A : Type x} {B : Type y}
variable [Field K] [Add U] [Mul U]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

/-- An interaction certificate equipped with target and local rank bounds. -/
structure Certificate
    (constant : C → U)
    (problem : Problem U)
    extends Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem where
  /-- Natural lower bound on the target feature rank. -/
  targetRank : Nat
  /-- Natural upper bound on each multiplication interaction rank. -/
  interactionRank : Nat
  /-- Every multiplication creates a feature interaction of bounded rank. -/
  interaction_rank_le : ∀ left right,
    LinearMap.rank (interaction left right) ≤ interactionRank
  /-- The target realizes the claimed rank. -/
  target_rank_ge : (targetRank : Cardinal) ≤
    LinearMap.rank (feature problem.target)

/-- Rank of a scalar multiple of a linear map is at most its rank. -/
theorem linearMap_rank_smul_le
    (scalar : K)
    (map : A →ₗ[K] B) :
    LinearMap.rank (scalar • map) ≤ LinearMap.rank map :=
  Submodule.rank_mono (LinearMap.range_smul_le_range map scalar)

/-- Every interaction retained from an atom list satisfies the certificate's
local rank bound. -/
theorem Certificate.rank_le_of_mem_interactions
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (A := A) (B := B)
      constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U))
    (interaction : A →ₗ[K] B)
    (present : interaction ∈
      interactions certificate.toCertificate atoms) :
    LinearMap.rank interaction ≤ certificate.interactionRank := by
  change interaction ∈
      atoms.filterMap (Atom.interaction? certificate.toCertificate) at present
  rw [List.mem_filterMap] at present
  obtain ⟨atom, _, interactionEqual⟩ := present
  cases atom with
  | mk op arguments =>
      cases op with
      | add => simp [Atom.interaction?] at interactionEqual
      | mul =>
          change Fin 2 → U at arguments
          simp only [Atom.interaction?] at interactionEqual
          rw [← Option.some.inj interactionEqual]
          exact certificate.interaction_rank_le
            (arguments (0 : Fin 2)) (arguments (1 : Fin 2))
      | constant scalar => simp [Atom.interaction?] at interactionEqual

/-- Rank of the target feature is at most the number of interactions times
their individual rank bound. -/
theorem Certificate.target_rank_le_interactions
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (A := A) (B := B)
      constant problem)
    (cover : Cover (model certificate.toCertificate)) :
    LinearMap.rank (certificate.feature problem.target) ≤
      ((interactions certificate.toCertificate cover.atoms).length :
        Cardinal) * certificate.interactionRank := by
  classical
  let interactionFeature :
      Fin (interactions certificate.toCertificate cover.atoms).length →
        (A →ₗ[K] B) :=
    fun index => (interactions certificate.toCertificate cover.atoms).get index
  have targetMem : certificate.feature problem.target ∈
      Submodule.span K (Set.range interactionFeature) := by
    simpa [generatedSubmodule, interactionFeature] using
      targetFeature_mem_generatedSubmodule certificate.toCertificate cover
  have targetMemImage : certificate.feature problem.target ∈
      Submodule.span K
        (interactionFeature ''
          (Finset.univ : Finset
            (Fin (interactions certificate.toCertificate
              cover.atoms).length))) := by
    simpa [Set.image_univ] using targetMem
  obtain ⟨coefficients, coefficientsSpec⟩ :=
    (Submodule.mem_span_image_finset_iff_exists_fun
      (R := K) (v := interactionFeature)).mp targetMemImage
  rw [← coefficientsSpec]
  calc
    LinearMap.rank
        (∑ index, coefficients index • interactionFeature index) ≤
        ∑ index,
          LinearMap.rank (coefficients index • interactionFeature index) := by
      simpa using LinearMap.rank_finsetSum_le
        (Finset.univ : Finset
          ((Finset.univ : Finset
            (Fin (interactions certificate.toCertificate
              cover.atoms).length)) : Type))
        (fun index => coefficients index • interactionFeature index)
    _ ≤ ∑ _index, (certificate.interactionRank : Cardinal) := by
      apply Finset.sum_le_sum
      intro index _
      exact (linearMap_rank_smul_le
        (coefficients index) (interactionFeature index)).trans
          (certificate.rank_le_of_mem_interactions cover.atoms
            (interactionFeature index) (by
              simp [interactionFeature]))
    _ = ((interactions certificate.toCertificate cover.atoms).length :
          Cardinal) * certificate.interactionRank := by
      simp [nsmul_eq_mul]

/-- Natural-number form of the rank-versus-interaction inequality. -/
theorem Certificate.targetRank_le_mul_coverCost
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (A := A) (B := B)
      constant problem)
    (cover : Cover (model certificate.toCertificate)) :
    certificate.targetRank ≤
      cover.cost * certificate.interactionRank := by
  have cardinalBound : (certificate.targetRank : Cardinal) ≤
      ((interactions certificate.toCertificate cover.atoms).length :
        Cardinal) * certificate.interactionRank :=
    certificate.target_rank_ge.trans
      (certificate.target_rank_le_interactions cover)
  have naturalBound : certificate.targetRank ≤
      (interactions certificate.toCertificate cover.atoms).length *
        certificate.interactionRank := by
    exact_mod_cast cardinalBound
  change certificate.targetRank ≤
    Atom.listCost cover.atoms
      (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        certificate.interactionRank
  rw [← interactions_length certificate.toCertificate cover.atoms]
  exact naturalBound

/-- Dividing by a positive local interaction-rank bound gives a cover lower
bound. -/
theorem Certificate.ceilDiv_targetRank_le_coverCost
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (A := A) (B := B)
      constant problem)
    (positive : 0 < certificate.interactionRank)
    (cover : Cover (model certificate.toCertificate)) :
    certificate.targetRank ⌈/⌉ certificate.interactionRank ≤ cover.cost :=
  (ceilDiv_le_iff_le_mul positive).2
    (by simpa [Nat.mul_comm] using
      certificate.targetRank_le_mul_coverCost cover)

/-- Interaction rank gives a multiplication lower bound for every arithmetic
circuit constructing the target. -/
theorem Certificate.circuit_lowerBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (A := A) (B := B)
      constant problem)
    (positive : 0 < certificate.interactionRank)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant)) :
    certificate.targetRank ⌈/⌉ certificate.interactionRank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  (model certificate.toCertificate).lowerBound
    (certificate.ceilDiv_targetRank_le_coverCost positive)
    circuit constructs

end Rank
end Interaction
end Arithmetic
end Fusion
end Algebraic
