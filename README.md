# Algebraic

Algebraic is a small Lean 4 library for finite-arity universal algebra and
shared circuit computation over algebraic interpretations.

The library has five layers:

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

## Build

```sh
lake build --wfail
```

## License

Algebraic is available under the [MIT License](LICENSE).
