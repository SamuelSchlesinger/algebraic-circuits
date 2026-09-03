import Algebraic.MassProduction.DirectProduct
import Algebraic.MassProduction.Statement
import Algebraic.MassProduction.Uhlig
import Algebraic.MassProduction.UhligCircuit
import Algebraic.MassProduction.UhligRecursion
import Algebraic.MassProduction.UhligTheorem
import Algebraic.MassProduction.LupanovSynthesis
import Algebraic.MassProduction.LowDegree
import Algebraic.MassProduction.EvaluationCode
import Algebraic.MassProduction.Scheduler
import Algebraic.MassProduction.Recovery
import Algebraic.MassProduction.BinaryField
import Algebraic.MassProduction.Projective
import Algebraic.MassProduction.ProjectiveCircuit
import Algebraic.MassProduction.ProjectiveRank
import Algebraic.MassProduction.SortingCorrectness
import Algebraic.MassProduction.SortingBy
import Algebraic.MassProduction.LeastMissing
import Algebraic.MassProduction.FreshDirection
import Algebraic.MassProduction.ForbiddenRanks
import Algebraic.MassProduction.SchedulerStage
import Algebraic.MassProduction.LineEnumeration
import Algebraic.MassProduction.SchedulerIteration
import Algebraic.MassProduction.ScheduledRecovery
import Algebraic.MassProduction.Routing
import Algebraic.MassProduction.RoutingCorrectness
import Algebraic.MassProduction.RoutingPasses
import Algebraic.MassProduction.RoutingRecords
import Algebraic.MassProduction.GroupedScheduler
import Algebraic.MassProduction.ResourcePacking
import Algebraic.MassProduction.GroupedRecovery
import Algebraic.MassProduction.PackedGroupedRecovery
import Algebraic.MassProduction.BinaryEncoding
import Algebraic.MassProduction.IncidenceRouting
import Algebraic.MassProduction.CanonicalRouting
import Algebraic.MassProduction.CanonicalScatter
import Algebraic.MassProduction.RoutingMetadata
import Algebraic.MassProduction.CanonicalMetadataRouting
import Algebraic.MassProduction.GatherRouting
import Algebraic.MassProduction.GatherDecoder
import Algebraic.MassProduction.ResourceEvaluation
import Algebraic.MassProduction.PackedPipeline
import Algebraic.MassProduction.RoutingAssembly
import Algebraic.MassProduction.CanonicalPacking
import Algebraic.MassProduction.FixedDivision
import Algebraic.MassProduction.BaseConversion
import Algebraic.MassProduction.RuntimePacking
import Algebraic.MassProduction.DynamicGatherDecoder
import Algebraic.MassProduction.RuntimePipeline
import Algebraic.MassProduction.InputSplit
import Algebraic.MassProduction.CompositionBound
import Algebraic.MassProduction.ShannonSynthesis
import Algebraic.MassProduction.FiniteParameters
import Algebraic.MassProduction.CodeParameters
import Algebraic.MassProduction.OverheadBound
import Algebraic.MassProduction.Growth
import Algebraic.MassProduction.EqualBlock
import Algebraic.MassProduction.BlockInduction

/-!
# Circuit mass production

This umbrella collects the formalization of the exact Boolean
mass-production manuscript in `projects/complexity/sharing`. The current
foundation defines independent direct products, Uhlig's two-copy gadget,
finite-field local recovery and disjoint scheduling, and explicit polynomial-
size binary-field, projective-normalization, exact initial-interval projective
rank/unrank, Batcher sorting, a finite-capacity-correct least-missing selector,
and a complete constructive greedy-scheduler stage from packed used points
through a geometrically disjoint direction to exact enumeration of every
non-target affine-line point. The greedy scheduler is recursively unrolled,
proved to emit pairwise-disjoint punctured lines for every target multiset,
and given an explicit per-request cost ledger. Guarded zero/sentinel ranking,
difference generation, sorting, selection, unranking, and line enumeration
all carry explicit polynomial gate ledgers. The sorter is proved to order
keys while permuting complete records, and the matching pass has verified
boundary, tag, payload, adjacency, end-to-end routing, and cost behavior under
its unique-record invariant. Concrete source, destination, and padding records
are packed into exact power-of-two layouts. Scheduled incidences have explicit
logarithmic `(group, point)` keys, route their request payloads to the matching
resource slots, and then undergo a second checked sort which places the entire
active destination key space at fixed canonical wire indices. A parallel bank
of supplied shorter mass-production circuits is wired to those slots with an
exact additive cost ledger. A metadata-preserving reverse gather places every
returned field value at its literal row-major incidence wire, and an explicit
XOR decoder is proved, together with the algebraic line identity, to recover
every requested Boolean value. This gives a checked finite
scatter-evaluate-gather-decode theorem for the deterministic grouped
scheduler. Fixed-divisor division and repeated base conversion implement the
canonical prefix placement on runtime bits; a one-hot runtime decoder then
packages every stage into one circuit proved to compute the ordinary
row-major direct product, with an exact additive cost ledger. The uniform
finite composition bound is also derived from uniform bounds on the shorter
resource circuits. An Algebraic-native shared-minterm/full-column Shannon
synthesis gives every `N >= 16` Boolean function a standard De Morgan circuit
of cost at most `27 * 2^N / N`, together with its replicated finite bound.
Canonical power-of-two record depths and the least admissible extension-field
width discharge the finite packing and routing bookkeeping, bound the number
of resources by a dimension-dependent constant times the prefix truth-table
size, and reduce direction capacity to one explicit exponential load
inequality.  The non-resource gate ledger is factored into its scheduler,
incidence-routing, resource-slot, packing, and decoder volumes with explicit
polynomial coefficients.  Exact natural-number growth estimates absorb that
ledger below the Shannon scale.  The two-block base proves every rational
copy exponent below one half; the recursively grouped equal-block step raises
the thresholds through `k / (k + 1)`.  Bounded input padding closes both the
arbitrary-length induction step and the finite initial segment.  Consequently
`BlockInduction.exponentialMassProduction` proves the manuscript's complete
fixed-rate theorem for every rational exponent strictly below one.  A separate
shared-minterm Lupanov block-table synthesis has exact semantics and a sharp
coefficient-one cost proof.  Combined with the exact recursive two-copy
construction, `LupanovSynthesis.uhlig_massProduction` proves Uhlig's sharp
`2 ^ o(n / log n)` mass-production theorem unconditionally.  Approximation
results are intentionally outside this formalization.
-/
