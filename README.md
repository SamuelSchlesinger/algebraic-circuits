# Algebraic

Algebraic is a small Lean 4 library for finite-arity universal algebra and
shared circuit computation over algebraic interpretations.

The core library has six layers:

- `Signature` describes operation symbols and their arities.
- `Interpretation` assigns concrete operations to a signature.
- `Homomorphism` defines maps that preserve those operations.
- `Program` is a topologically ordered sequence of shared internal gates.
- `Circuit` designates input or gate wires as outputs of a program.
- `Translation` implements the operations of one signature by circuits over
  another signature.

A program gate may read an original input or an earlier gate. Designating an
output wire is free, so projections require no identity gate. Circuit size is
the program's gate count. Inputs have depth zero, each gate adds one to the
maximum depth of its arguments, and circuit depth is the maximum designated
output depth.

Evaluation of lines, programs, and circuits commutes with homomorphisms.

The core program API also supports semantics-preserving structural changes:

- `Wire.Renaming` represents wire maps that fix original inputs, with identity,
  composition, extension, and permutation constructors.
- `Line.mapWires`, `Line.eval_mapWires`, and `Line.eval_mapRenaming` transport a
  line across a wire map.
- `Wire.Substitution`, `Program.instantiate`, and `Circuit.comp` substitute
  arbitrary input wires and compose circuits without materializing outputs as
  gates; their evaluation and weighted-cost laws are exact.
- simp lemmas describe the old and last gate of an appended program.
- `Program.gateFunction` and `Program.wireFunction` expose scalar semantics.
- `Program.lines` views a program as a fully widened indexed collection of
  lines; `Program.lines_eval` relates that view back to program evaluation.

Reusable circuit analysis is kept separate from particular lower-bound methods:

- `ScalarFunction`, `Target`, and `Circuit.outputFunction` name the scalar and
  multi-output semantic views used throughout the library.
- `Circuit.GateHard` and `Circuit.DepthHard` package the conclusions of size and
  depth lower bounds without exposing their quantified circuit witnesses.
- `Computes`, `Interpretation.FunctionallyComplete`, `DependsOnlyOn`, and
  `EssentialAt` give the semantic vocabulary.
- `Circuit.inputSupport` computes the structural input support of a circuit.
- `Circuit.FanInAtMost` states the structural bounded-fan-in hypothesis.
- `Circuit.card_inputSupport_le_depth` and `Circuit.card_inputSupport_le_size`
  bound that support for bounded-fan-in circuits.
- `Circuit.essential_le_depth` and `Circuit.essential_le_size` turn those
  structural bounds into semantic lower-bound tools.
- `Signature.depthInterpretation` evaluates gates as arrival times. Circuit
  evaluation in this interpretation is exactly `Circuit.outputDepths`, and a
  translated circuit therefore inherits an exact per-operation delay semantics.

Changing signatures is proof-carrying:

- `Translation.pull` turns a target interpretation into the derived source
  interpretation implemented by the operation circuits.
- `Translation.compile_eval` proves that compiling a circuit and then
  evaluating it is exactly evaluation in the pulled-back interpretation.
- `Translation.pullCost` charges each source operation by the weighted cost of
  its implementation, and `Translation.compile_cost` proves exact cost
  preservation. Unit cost recovers exact gate count, and a uniform local
  `K`-gate bound yields the usual `K`-factor size simulation.
- `OptimalRealization` and `Realization.minimumCost` replace arbitrary chosen
  gadgets by genuinely minimum-cost implementations. The resulting source
  cost is independent of the realization used to witness implementability and
  equals the target-basis scalar complexity of each operation.
- `Circuit.costComplexity` and `Circuit.gateComplexity` take the infimum over
  all implementations in `ℕ∞`; a nonrepresentable target has complexity
  `⊤`. Exact circuit-level cost preservation induces the weighted complexity
  inequality and the conventional constant-factor gate-complexity comparison.
- Translations have identity and composition operations. Interpretations and
  costs pull back contravariantly; one-stage and two-stage compilation have the
  same semantics and cost (their gate names need not be syntactically equal).
- `ObservedSignature U` quotients translations by their action on all
  `U`-valued interpretations and all weighted costs, yielding an actual
  Mathlib category rather than claiming intensional equality of compiled
  programs.
- `Realization` records equality with a chosen source interpretation.
  `Simulation T I J` is definitionally just `Homomorphism I (T.pull J)`, so
  the same theorem handles carrier and signature changes without duplicating
  the homomorphism interface. Identities and composition are available for
  homomorphisms, realizations, and simulations.
- For finite source signatures, `Interpretation.simulationOverhead` is the
  optimal maximum gadget size. It is normalized to at least one because free
  projections can use zero gates, and is `⊤` when no realization exists.
  It is submultiplicative; its extended-real logarithm
  `simulationDistance` satisfies the directed triangle inequality. Two finite,
  functionally complete bases consequently have explicit two-sided linear
  gate-complexity bounds.
- `BlockTranslation` implements one source value by a fixed-width block of
  target values. Its compiler shares each multi-output gadget, preserves
  evaluation and weighted cost exactly, and `BlockSimulation` is again a
  homomorphism into the pulled-back interpretation.

Several other compositional analyses are interpretations too:

- support evaluation exactly recovers the existing structural output support;
- degree modes propagate syntactic degree through constant-, maximum-, and
  sum-like operations;
- the four-point polarity domain propagates signed dependencies; and
- finite possible-value sets soundly overapproximate arbitrary concrete input
  sets and are exact on singleton inputs.

Compiling and then running any of these analyses is exactly source evaluation
in the pulled-back abstract interpretation. Degree and polarity deliberately
separate this generic propagation theorem from the basis-specific proof that a
chosen local policy soundly describes concrete polynomial degree or
monotonicity.

Lower-bound methods live under `Algebraic/LowerBound`. `Algebraic.LowerBound`
is an import umbrella. The bounded-fan-in method has separate size and depth
modules under `Algebraic/LowerBound/FanIn`.

Gate elimination is organized as a proof-carrying, basis-independent method:

- `OperationCost` assigns arbitrary natural weights to operation symbols.
- `InputSubstitution` covers restrictions, identifications, and more general
  semantic substitutions.
- `Circuit.Reduction` packages a residual circuit, semantic preservation under
  a substitution, and a certified cost saving.
- `GateElimination.Framework` turns well-founded local reductions into a
  global lower bound for an arbitrary state-indexed target family.
- `GateElimination.OptimalFramework` lets the local proof assume a circuit
  lexicographically minimal by weighted cost and internal gate count; the
  library chooses that representative and transfers the result back to every
  circuit.
- `GateElimination.Xor.ThreeGateEliminator` is the sole local obligation for
  the `3 * (n - 1)` XOR lower bound over any weighted Boolean basis.
- The De Morgan specialization charges AND and OR while treating constants and
  identity and NOT as free. `DeMorgan.xorThreeGateEliminator` discharges the
  local obligation, and `DeMorgan.xor_lowerBound` exports the unconditional
  lower bound. `parity_lowerBound_of_deMorgan_realization` transports it to any
  macro basis, charging every macro by the AND/OR cost of its selected De Morgan
  implementation. `parity_lowerBound_of_deMorgan_minimumCost` strengthens this
  to the minimum possible AND/OR implementation cost of each macro.
  `parity_size_lowerBound_of_deMorgan_minimumCost` gives the ceiling-divided
  unit-size consequence under a uniform intrinsic-cost bound, while
  `parity_size_lowerBound_of_deMorgan_realization` uses a uniform bound on the
  total size of selected implementations.
  The library does not currently formalize a matching upper-bound construction.
- Minimum-circuit and elimination witnesses are chosen classically. These APIs
  certify lower bounds in Lean but do not implement an executable optimizer or
  gate-elimination algorithm.

The counting development is exported by `Algebraic.LowerBound.Counting`:

- `Algebraic.Counting.Syntax` gives finite instances and exact cardinality
  formulas for lines, programs, circuits, and the full target-function space;
  `Target.count` names the latter cardinality.
- `Counting.Basic` bounds the functions computed with at most `G` internal
  gates and works relative to any finite family of target functions;
  `Signature.orderedBudget` names the exact ordered-syntax count.
- `Counting.Depth` constructs the interpretation-sensitive closure of scalar
  functions under one operation layer and proves exact, numeric, and
  arity-only depth criteria.
- `Counting.Normalization` semantically hash-conses a circuit without
  increasing its gate count.
- `Counting.Sharp` removes the artificial topological ordering: for exactly
  `g` irredundant gates, the number of computed functions times `g!` is at most
  `lineCount (n + g) ^ g * (n + g) ^ m`. The second factor counts the freely
  designated output wires. Summing the resulting quotients gives
  `Signature.sharpBudget`.
- `Counting.Arity` packages maximum arity and bounds the number of available
  lines; `Counting.Coarse` derives elementary arity-only size bounds.
- `Counting.FinalTerm` replaces the exact sharp sum by the named real-valued
  `Signature.finalTerm` envelope without using Stirling.
- `Counting.AlmostAll` defines easy and hard subfamilies, gives a division-free
  density-zero criterion, and relates it to the conventional
  `Circuit.easyDensity` limit.
- `Counting.Shannon` applies Stirling and proves the closed-form theorem for an
  arbitrary fixed finite basis. If `q` is the universe size, `r ≥ 2` is the
  attained maximum gate arity, and `m > 0` is fixed, then the density of
  functions computable with at most
  `⌊m * q ^ n / ((r - 1) * n)⌋` internal gates tends to zero. Boolean and
  finite-field forms are included; for binary one-output Boolean bases the
  budget simplifies to `2 ^ n / n`.

The sharp lower bound does not assume functional completeness. When an
interpretation is complete, `Circuit.exists_hard_sharp_of_complete` additionally
returns a circuit computing the hard target, so the conclusion is a genuine
finite complexity lower bound rather than mere non-representability.
The closed almost-all theorem also avoids a completeness assumption: its
conclusion is that no circuit within the stated budget computes the target.

## Build

```sh
lake build --wfail
```

Generate the API documentation with:

```sh
cd docbuild
lake build Algebraic:docs
```

The generated site starts at `docbuild/.lake/build/doc/index.html`.
Serve that directory over HTTP for working search and navigation, for example:

```sh
cd docbuild/.lake/build/doc
python3 -m http.server
```

## License

Algebraic is available under the [MIT License](LICENSE).
