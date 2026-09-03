import Algebraic.LowerBound.AC0.LayerIterationBounds
import Algebraic.LowerBound.AC0.ParityTopGate

/-!
# Variable-parameter depth reduction for parity circuits

This module composes the variable-parameter layer iterator with the parity
top-gate obstruction. A circuit of logical depth at most `rounds + 1` needs
only `rounds` restriction steps: the final unreduced AND or OR is handled as a
bounded-width normal form.

Under the explicit per-round switching and survivor inequalities, any parity
circuit forces `retained rounds <= treeBound rounds`. If the chosen schedule
ends above that tree bound, the circuit cannot compute parity. This is the
complete structural contradiction with the source-faithful `d - 1` round
count; selecting closed-form parameters remains a separate arithmetic task.
-/

namespace Algebraic
namespace AC0
namespace Circuit

open scoped ENNReal

/-- A depth-`rounds + 1` parity circuit satisfying an explicit reduction
schedule forces the final survivor count below the final tree bound. -/
theorem retained_le_treeBound_of_iterated_parity
    (circuit : Algebraic.Circuit signature n g 1)
    (normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.Computes interpretation (Parity.target n))
    (rounds : Nat)
    (circuitDepth : logicalDepth circuit ≤ rounds + 1)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal)) :
    retained rounds ≤ treeBound rounds := by
  obtain ⟨rho, shallow, survivors⟩ :=
    Program.exists_shallowUpTo_with_liveCount_bounds
      circuit.program normal rounds treeBound oneLeInitialBound p
      atMostOne boundMonotone retained initial failureLe room
  exact survivors.trans
    (liveCount_le_of_shallowBelowTop_computes_parity
      normal computes circuitDepth shallow)

/-- Parameterized `rounds`-step parity lower bound with one unreduced top
layer: a schedule ending above its final tree allowance rules out the
circuit. -/
theorem not_computes_parity_of_iterated_switching_below_top
    (circuit : Algebraic.Circuit signature n g 1)
    (normal : Program.NegationsAtInputs circuit.program)
    (rounds : Nat)
    (circuitDepth : logicalDepth circuit ≤ rounds + 1)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal))
    (tooMany : treeBound rounds < retained rounds) :
    ¬circuit.Computes interpretation (Parity.target n) := by
  intro computes
  exact (Nat.not_lt_of_ge
    (retained_le_treeBound_of_iterated_parity
      circuit normal computes rounds circuitDepth treeBound
      oneLeInitialBound p atMostOne boundMonotone retained initial
      failureLe room)) tooMany

end Circuit
end AC0
end Algebraic
