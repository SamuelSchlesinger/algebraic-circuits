import Algebraic.Basis.Arithmetic.Power
import Algebraic.LowerBound.FanIn
import Algebraic.LowerBound.Counting.Shannon
import Algebraic.LowerBound.GateElimination.DeMorganXor
import Algebraic.LowerBound.Monotone.Clique.Exponential
import Algebraic.LowerBound.Fusion.Cyclic.Complete
import Algebraic.LowerBound.Fusion.SumOfTerms.Rectangle

/-!
# Curated applications

This facade gives short names to a deliberately small set of ready-to-use
compilers and flagship lower-bound endpoints. The defining modules remain the
source of truth for hypotheses and supporting theory.
-/

namespace Algebraic
namespace Applications

export Arithmetic.Power
  (binaryPowerGateCount
   binaryPowerCircuit
   binaryPowerCircuit_eval
   binaryPowerCircuit_multiplicationCost
   binaryPowerCircuit_additionCost)

export Circuit
  (card_inputSupport_le_size
   card_inputSupport_le_depth
   essential_le_size
   essential_le_depth
   asymptoticallyAlmostAllHard_shannon
   tendsto_easyDensity_zero_shannon
   tendsto_boolean_easyDensity_zero_shannon
   tendsto_finiteField_easyDensity_zero_shannon)

export Shannon (gateBudget)

export DeMorgan (xor_lowerBound)

export Fusion
  (pairCoverComplexity_eq_joinMeetCyclicComplexity
   pairCoverComplexity_eq_andOrCyclicComplexity)

export Fusion.SumOfTerms.Rectangle (diagonal_lowerBound)

export Monotone.Clique.Exponential
  (powSelf_lt_circuitSize
   twoPow_lt_circuitSize)

end Applications
end Algebraic
