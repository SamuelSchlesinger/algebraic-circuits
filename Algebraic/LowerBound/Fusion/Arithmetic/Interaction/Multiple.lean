import Algebraic.LowerBound.Fusion.Arithmetic.Interaction
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Multi-output arithmetic interaction bounds

All outputs of one arithmetic circuit share the same multiplication gates and
hence the same interaction span.  If the feature values of `m` requested
outputs are linearly independent, that common span needs at least `m`
generators.  Because one generator is extracted from each multiplication
gate, the circuit needs at least `m` multiplications.

The `target` field of the base `Problem` is intentionally irrelevant here;
the problem supplies the common input family used by the interaction
certificate.  The requested output family is passed separately.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Multiple

variable {K : Type u} {C : Type v} {U : Type w} {Q : Type x}
variable [Field K] [Add U] [Mul U]
variable [AddCommGroup Q] [Module K Q]

/-- A multi-output circuit constructs a requested family when all designated
outputs have the specified semantic values. -/
def Constructs
    {constant : C → U}
    (problem : Problem U)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m) : Prop :=
  circuit.eval (Algebraic.Arithmetic.interpretation constant)
    problem.inputs = targets

/-- Every requested output feature belongs to the common interaction span of
a constructing circuit. -/
theorem targetFeature_mem_circuitSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m)
    (constructs : Constructs (constant := constant) problem targets circuit)
    (output : Fin m) :
    certificate.feature (targets output) ∈
      generatedSubmodule certificate
        (circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation constant) problem.inputs) := by
  rw [← congrFun constructs output]
  exact feature_circuit_output_mem certificate circuit output

/-- Linearly independent output features force one multiplication interaction
per output. -/
theorem circuit_multiplication_lowerBound_of_linearIndependent
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (independent : LinearIndependent K (certificate.feature ∘ targets))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m)
    (constructs : Constructs (constant := constant) problem targets circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  classical
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation constant) problem.inputs
  let interactionFeature :
      Fin (interactions certificate atoms).length → Q :=
    fun index => (interactions certificate atoms).get index
  have targetMem : ∀ output,
      certificate.feature (targets output) ∈
        generatedSubmodule certificate atoms := by
    intro output
    exact targetFeature_mem_circuitSubmodule certificate targets circuit
      constructs output
  have targetRange_le :
      Set.range (certificate.feature ∘ targets) ⊆
        Submodule.span K (Set.range interactionFeature) := by
    intro featureValue present
    obtain ⟨output, rfl⟩ := present
    exact targetMem output
  have cardinalBound : Cardinal.mk (Fin m) ≤
      Fintype.card (Set.range interactionFeature) :=
    linearIndependent_le_span'
      (certificate.feature ∘ targets) independent
      (Set.range interactionFeature) targetRange_le
  have naturalBound : m ≤
      Fintype.card (Set.range interactionFeature) := by
    simpa using cardinalBound
  have outputCount_le_interactions : m ≤
      (interactions certificate atoms).length :=
    naturalBound.trans (by
      simpa using Fintype.card_range_le interactionFeature)
  calc
    m ≤ (interactions certificate atoms).length :=
      outputCount_le_interactions
    _ = Atom.listCost atoms
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
      interactions_length certificate atoms
    _ = circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
      simpa [atoms] using circuitAtoms_cost circuit
        (Algebraic.Arithmetic.interpretation constant) problem.inputs
        (Algebraic.Arithmetic.multiplicationCost (K := C))

end Multiple
end Interaction
end Arithmetic
end Fusion
end Algebraic
