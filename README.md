# Algebraic

Algebraic is a Lean 4 library for finite-arity universal algebra and shared
circuit computation. It provides reusable syntax, semantics, translations,
analyses, and lower-bound frameworks without fixing a particular carrier or
gate basis.

## Design

- A `Signature` describes operation symbols and their arities, while an
  `Interpretation` assigns them concrete meaning.
- A `Program` is a topologically ordered, shared computation. A `Circuit`
  designates input or gate wires as outputs, so projections and multi-output
  circuits do not need artificial output gates.
- Homomorphisms connect interpretations. Translations implement one signature
  by circuits over another and carry semantic and weighted-cost guarantees.
- Structural and abstract analyses are kept separate from concrete bases, so
  they can be transported through translations and reused by lower-bound
  arguments.

Reusable Boolean, arithmetic, and sum-of-terms bases live under
`Algebraic.Basis`. The main `Algebraic` module is the umbrella import; focused
imports are available throughout the directory tree.

## Lower bounds

`Algebraic.LowerBound` collects several independent methods, including
bounded-fan-in arguments, counting, gate elimination, and Fusion.

The Fusion development is parameterized by the circuit signature,
interpretation, target problem, observation model, and operation costs. This
keeps the circuit-to-cover argument independent of its set-theoretic or
algebraic applications. A separate least-fixed-point model handles cyclic
circuits without weakening the acyclic invariant of `Program`.

This README deliberately does not inventory individual definitions or
theorems. Module docstrings and the generated API reference are the source of
truth for the results currently available and their precise hypotheses.

## Build

```sh
lake build --wfail
```

## Documentation

The API reference is generated with
[doc-gen4](https://github.com/leanprover/doc-gen4). First build the local site:

```sh
scripts/build_docs.sh
```

Then serve it and open <http://localhost:8000/>:

```sh
python3 -m http.server --directory _site
```

The first documentation build also processes imported Mathlib modules and can
take substantially longer than later incremental builds.

## License

Algebraic is available under the [MIT License](LICENSE).
