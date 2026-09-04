import Algebraic.MassProduction.BlockInduction
import Algebraic.MassProduction.LupanovSynthesis
import Algebraic.MassProduction.RoutingPasses
import Algebraic.MassProduction.Nonuniform
import Algebraic.MassProduction.HighRate

/-!
# Boolean circuit mass production

This umbrella formalizes the exact results developed in the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production).
Its two principal endpoints are:

* `BlockInduction.exponentialMassProduction`, which gives a uniform
  `O(2 ^ n / n)` upper bound for every fixed rational copy exponent below one;
* `LupanovSynthesis.uhlig_massProduction`, which gives coefficient-one mass
  production through every copy bound `2 ^ o(n / log n)`.

The imported implementation develops independent direct products, explicit
De Morgan circuits, finite-field local recovery, disjoint-line scheduling,
routing, and the finite cost bounds used by those theorems. Approximation
results are intentionally outside this formalization.

The nonuniform extension additionally proves universal scheduling menus,
linear-size propagation primitives, high-rate systematic line-recovery codes,
and their Boolean packing semantics. The complete nonuniform scheduler cost
and improved exponential-range leading coefficient remain outside the checked
endpoints; see the `Nonuniform` and `HighRate` umbrella docstrings.
-/
