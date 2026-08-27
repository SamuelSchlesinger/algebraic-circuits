import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Local

/-!
# Multiplication-occurrence rank budgets

Present the nonuniform interaction-rank theorem directly in terms of the
evaluated multiplication gates of an arithmetic circuit.  This avoids asking
clients to index a second, certificate-dependent filtered list while retaining
one budget entry for every gate occurrence, including repeated semantic
products.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Rank
namespace Occurrence

open Cardinal

variable {K : Type u} {C : Type v} {U : Type w}
variable {A : Type x} {B : Type y}
variable [Field K] [Add U] [Mul U]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

/-- The interaction map created by a particular evaluated multiplication-gate
occurrence. -/
def interactionFamily
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1) :
    Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
      (A →ₗ[K] B) :=
  fun index =>
    let arguments :=
      (circuitMultiplicationArguments constant problem.inputs circuit).get index
    certificate.interaction
      (arguments (0 : Fin 2)) (arguments (1 : Fin 2))

/-- Nonuniform rank budget indexed directly by evaluated multiplication-gate
occurrences. -/
def IndexedBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (budget :
      Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
        Nat) : Prop :=
  ∀ index,
    LinearMap.rank (interactionFamily certificate circuit index) ≤ budget index

/-- A semantic budget function can be checked on membership in the
multiplication-occurrence list.  The final sum still counts duplicate
occurrences separately. -/
def ArgumentBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (budget : (Fin 2 → U) → Nat) : Prop :=
  ∀ arguments,
    arguments ∈
      circuitMultiplicationArguments constant problem.inputs circuit →
    LinearMap.rank
      (certificate.interaction
        (arguments (0 : Fin 2)) (arguments (1 : Fin 2))) ≤ budget arguments

/-- The target feature is spanned by the occurrence-indexed interaction
family. -/
theorem targetFeature_mem_span
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant)) :
    certificate.feature problem.target ∈
      Submodule.span K (Set.range (interactionFamily certificate circuit)) := by
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation constant) problem.inputs
  apply (show generatedSubmodule certificate atoms ≤
      Submodule.span K (Set.range (interactionFamily certificate circuit))
    from ?_)
  · simpa [atoms] using
      targetFeature_mem_circuitSubmodule certificate circuit constructs
  · rw [generatedSubmodule]
    apply Submodule.span_le.2
    intro interaction present
    obtain ⟨interactionIndex, interactionEqual⟩ := present
    have interactionPresent : interaction ∈
        interactions certificate atoms := by
      rw [← interactionEqual]
      exact List.get_mem _ interactionIndex
    rw [interactions_eq_map_multiplicationArguments certificate atoms,
      List.mem_map] at interactionPresent
    obtain ⟨arguments, argumentsPresent, argumentsEqual⟩ :=
      interactionPresent
    rw [← argumentsEqual]
    apply Submodule.subset_span
    obtain ⟨argumentIndex, argumentEqual⟩ :=
      List.mem_iff_get.mp argumentsPresent
    refine ⟨argumentIndex, ?_⟩
    change certificate.interaction
      ((multiplicationArguments atoms).get argumentIndex (0 : Fin 2))
      ((multiplicationArguments atoms).get argumentIndex (1 : Fin 2)) =
        certificate.interaction
          (arguments (0 : Fin 2)) (arguments (1 : Fin 2))
    rw [argumentEqual]

/-- An argument-indexed semantic budget induces an occurrence-indexed
budget by evaluating it at each gate's actual arguments. -/
theorem IndexedBound.of_argumentBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (budget : (Fin 2 → U) → Nat)
    (bound : ArgumentBound certificate circuit budget) :
    IndexedBound certificate circuit
      (fun index => budget
        ((circuitMultiplicationArguments constant problem.inputs circuit).get
          index)) := by
  intro index
  exact bound _ (List.get_mem _ index)

/-- Target rank is at most the sum of occurrence-indexed local rank budgets. -/
theorem target_rank_le_sum_indexedBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget :
      Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
        Nat)
    (localBound : IndexedBound certificate circuit budget) :
    LinearMap.rank (certificate.feature problem.target) ≤
      ∑ index, (budget index : Cardinal) :=
  Rank.linearMap_rank_le_sum_of_mem_span
    (certificate.feature problem.target)
    (interactionFamily certificate circuit) budget
    (targetFeature_mem_span certificate circuit constructs) localBound

/-- Natural-number form of the occurrence-indexed rank inequality. -/
theorem targetRank_le_sum_indexedBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget :
      Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
        Nat)
    (localBound : IndexedBound certificate circuit budget) :
    targetRank ≤ ∑ index, budget index := by
  have cardinalBound : (targetRank : Cardinal) ≤
      ∑ index, (budget index : Cardinal) :=
    target_rank_ge.trans
      (target_rank_le_sum_indexedBudget certificate circuit constructs budget
        localBound)
  exact_mod_cast cardinalBound

/-- A semantic argument budget bounds target rank by its list sum over actual
multiplication occurrences. -/
theorem targetRank_le_sum_argumentBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget : (Fin 2 → U) → Nat)
    (localBound : ArgumentBound certificate circuit budget) :
    targetRank ≤
      ((circuitMultiplicationArguments constant problem.inputs circuit).map
        budget).sum := by
  simpa [← Fin.sum_ofFn] using
    targetRank_le_sum_indexedBudget certificate targetRank target_rank_ge
      circuit constructs
      (fun index => budget
        ((circuitMultiplicationArguments constant problem.inputs circuit).get
          index))
      (IndexedBound.of_argumentBound certificate circuit budget localBound)

end Occurrence
end Rank
end Interaction
end Arithmetic
end Fusion
end Algebraic
