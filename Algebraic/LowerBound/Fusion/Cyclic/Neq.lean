import Algebraic.LowerBound.Fusion.Cyclic
import Algebraic.LowerBound.Fusion.Neq

/-!
# A cyclic fusion lower bound for inequality graphs

The canonical semi-ultrafilter coding bound for the inequality graph applies
unchanged to least-fixed-point cyclic AND/OR circuits.  Thus cycles do not
reduce the `n`-AND cost of constructing inequality on `2 ^ n` vertices.
-/

namespace Algebraic
namespace Fusion
namespace Neq

/-- Every least-fixed-point cyclic row/column construction of inequality on
`2 ^ n` vertices uses at least `n` AND equations, even with free OR equations. -/
theorem cyclic_and_lowerBound
    (circuit : CyclicCircuit AndOr.signature
      ((2 ^ n) + (2 ^ n)) g)
    (constructs : circuit.Constructs (problem := problem (2 ^ n))
      (AndOr.setInterpretation (Ground (2 ^ n)))) :
    n ≤ circuit.cost AndOr.andCost :=
  cyclic_pairCover_lowerBound (problem (2 ^ n))
    SemifilterClass.ultra ultraPairCover_cost_lowerBound circuit constructs

end Neq
end Fusion
end Algebraic
