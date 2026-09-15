# Algebraic

Algebraic is a Lean 4 library for finite-arity universal algebra and shared
circuit computation built on [CSLib](https://github.com/leanprover/cslib).
It extends CSLib's circuit model with semantics, costs, translations,
analyses, and lower-bound frameworks without fixing a particular carrier or
gate basis.

## Design

The signatures, interpretations, homomorphisms, wires, programs, and circuits
come from `Cslib.Computability.Circuit`. The `Algebraic` core imports re-export
these types and their operations, so native CSLib circuits work directly with
the library's constructions and lower bounds. Lake pins CSLib to revision
`85805b8447124a6561a5751d8b488f8fae96699e`, the stacked head of
[Shannon #891](https://github.com/leanprover/cslib/pull/891) and
[Lupanov #890](https://github.com/leanprover/cslib/pull/890), with their matching
Lean and Mathlib versions.

- A `Signature` describes operation symbols and their arities, while an
  `Interpretation` assigns them concrete meaning.
- A `Program` is a topologically ordered, shared computation. A `Circuit`
  designates input or gate wires as outputs, so projections and multi-output
  circuits do not need artificial output gates.
- `circuit.ComputesWith interpretation target` expresses generic computation.
  CSLib's `circuit.Computes function` specializes to its scalar Boolean basis.
  The former generic name remains available as `Algebraic.Circuit.Computes`.
- Homomorphisms connect interpretations. Translations implement one signature
  by circuits over another and carry semantic and weighted-cost guarantees.
- Structural and abstract analyses are kept separate from concrete bases, so
  they can be transported through translations and reused by lower-bound
  arguments.

Reusable Boolean, arithmetic, and sum-of-terms bases live under
`Algebraic.Basis`. The main `Algebraic` module is the umbrella import; focused
imports are available throughout the directory tree.

Choose an entry point for the task:

- `import Algebraic.Core` for signatures, shared circuits, semantics, costs,
  substitution, and translation;
- `import Algebraic.Applications` for the umbrella of curated binary-power and
  lower-bound endpoints; prefer focused application imports when possible;
- `import Algebraic.Basis.DeMorgan.Complexity` for minimum native circuit
  size, point updates, and the Hamming Lipschitz bound;
- `import Algebraic.Basis.DeMorgan.PairIndicator` for support/read-once
  arguments and native size bounds for functions with two exceptional inputs;
- `import Algebraic` for the complete library.

The naming, namespace, simp, and stability conventions are recorded in
[`STYLE.md`](STYLE.md).

See the [application guide](docs/applications.md) for focused imports, cost
conventions, and checked examples. In particular,
`Algebraic.Applications.Hessian` accepts an ordinary polynomial computation
equality, and `Algebraic.Applications.Waring` accepts a finite sum-of-powers
equality. Neither interface requires callers to construct a Fusion certificate.

Elementary Boolean completeness is available from
`Algebraic.Basis.DeMorgan.Completeness`. Its truth-table construction and
multi-output completeness theorem do not depend on Lupanov synthesis or
minimum circuit complexity.

The point-update and counting arguments for strict circuit size hierarchies
are described in [`docs/circuit-hierarchy.md`](docs/circuit-hierarchy.md).
Basic Boolean operations, input masks, numerical thresholds, and the compiler
that shares constant gates remain available as focused modules under
`Algebraic.Basis.DeMorgan`.

## Lower bounds

`Algebraic.LowerBound` collects several independent methods, including
bounded-fan-in arguments, counting, gate elimination, and Fusion.

Completed results include Shannon counting, the De Morgan parity lower bound,
AC0 parity separation, monotone Boolean CLIQUE, monotone arithmetic clique
support bounds, Hessian rank, and Waring and rectangle bounds. Restricted
models and their charged operations are explicit in the theorem statements.
The AC0 development has a detailed [theory map](docs/ac0-theory-map.md).

`Algebraic.Basis.DeMorgan.ShannonLupanov` transfers CSLib's sharp bounds to
the local De Morgan complexity measures. The conversions preserve semantics,
remove identity gates when exporting to CSLib, and track the difference between
total gate count and weighted logical-gate cost. The local mass-production
constructions retain their explicit finite cost bounds.

The Fusion development is parameterized by the circuit signature,
interpretation, target problem, observation model, and operation costs. This
keeps the circuit-to-cover argument independent of its set-theoretic or
algebraic applications. A separate least-fixed-point model handles cyclic
circuits without weakening the acyclic invariant of `Program`.

The [application guide](docs/applications.md) maps representative results to
their imports, models, and charged operations. Module docstrings and the
generated API reference give their full statements. The
[upstream preparation record](docs/upstream-readiness.md) tracks the remaining
integration and review work.

The [library stocktake](research/library-stocktake-2026-09-08.md) records the
retained results and the removal of the later star/topology research branch.
The preparatory noncommutative recurrence is kept in
[`research/noncommutative`](research/noncommutative/README.md), outside the
public library and regression suite.

## Build

```sh
lake build --wfail
```

Run all default declaration linters over the `Algebraic` modules:

```sh
lake lint
```

## Tests

Compile the downstream-style public API regression suite:

```sh
lake test
```

This includes a transitive axiom audit of all library-owned declarations
visible through the public import, including their private proof dependencies.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Unexported
modern-module declarations unreachable from the public API are outside the
audit. Small executable tests using `native_decide` are kept outside the library.

Check that every library and test module is reachable from its root import,
and that elementary modules do not depend on research or sharp synthesis:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_imports.py
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
