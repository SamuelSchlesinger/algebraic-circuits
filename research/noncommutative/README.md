# Noncommutative recurrence research

`DescendingChain.lean` preserves a numerical recurrence estimate and its
small regression examples. It is outside the `Algebraic` and `AlgebraicTests`
library roots and is not exported by `Algebraic.LowerBound`.

The missing step is a construction associating the required rank profile to
an actual noncommutative circuit. Until that reduction is proved, this file
does not establish a circuit lower bound. Further recurrence refinements need
a concrete circuit application.

Check the standalone source from the repository root:

```sh
lake env lean research/noncommutative/DescendingChain.lean
```
