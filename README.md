# Algebraic

Algebraic is a small Lean 4 library for finite-arity universal algebra and
shared circuit computation over algebraic interpretations.

The core library has five layers:

- `Signature` describes operation symbols and their arities.
- `Interpretation` assigns concrete operations to a signature.
- `Homomorphism` defines maps that preserve those operations.
- `Program` is a topologically ordered sequence of shared internal gates.
- `Circuit` adds a terminal layer of output gates to a program.

A program gate may read an original input or an earlier gate. Output gates may
read any input or internal gate, but cannot feed internal gates or one another.
Circuit size counts internal and output gates. Inputs have depth zero, each gate
adds one to the maximum depth of its arguments, and circuit depth is the maximum
terminal-output depth.

Evaluation of lines, programs, and circuits commutes with homomorphisms.

The core program API also supports semantics-preserving structural changes:

- `Wire.Renaming` represents wire maps that fix original inputs, with identity,
  composition, extension, and permutation constructors.
- `Line.mapWires`, `Line.eval_mapWires`, and `Line.eval_mapRenaming` transport a
  line across a wire map.
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

Lower-bound methods live under `Algebraic/LowerBound`. `Algebraic.LowerBound`
is an import umbrella. The bounded-fan-in method has separate size and depth
modules under `Algebraic/LowerBound/FanIn`.

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
  `lineCount (n + g) ^ (g + m)`. Summing the resulting quotients gives
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
