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

Reusable circuit analysis is kept separate from particular lower-bound methods:

- `Computes`, `DependsOnlyOn`, and `EssentialAt` give the semantic vocabulary.
- `Circuit.inputSupport` computes the structural input support of a circuit.
- `Circuit.FanInAtMost` states the structural bounded-fan-in hypothesis.
- `Circuit.card_inputSupport_le_depth` and `Circuit.card_inputSupport_le_size`
  bound that support for bounded-fan-in circuits.
- `Circuit.essential_le_depth` and `Circuit.essential_le_size` turn those
  structural bounds into semantic lower-bound tools.

Lower-bound methods live under `Algebraic/LowerBound`. `Algebraic.LowerBound`
is an import umbrella; the current bounded-fan-in method has separate size and
depth modules under `Algebraic/LowerBound/FanIn`.

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
