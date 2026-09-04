import Algebraic.MassProduction.HighRate.BooleanRecovery

/-!
# High-rate punctured-line recovery codes

`HighRate.existsHighRateLineCode` constructs a systematic code with exact
dimension `A^m - (A-1)^m`, for `A = 2^(blockWidth * dimension)` and field
width `blockWidth * m`. `HighRate.retainedDimension_hasRateOne` proves its
rate tends to one in an integer precision formulation with an explicit
cutoff. Packing loses at most one extra codeword; Boolean resource recovery
and uniqueness of scheduled resource incidences are proved separately.

The stronger mass-production leading coefficient is not an endpoint of
this module. Its runtime lookup, scheduling, routing, and asymptotic circuit
composition still require integration.
-/
