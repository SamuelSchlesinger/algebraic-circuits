# Library and API style

Algebraic is organized as a reusable circuit library with several active
research developments layered above it. These conventions keep that broad
surface navigable without forcing breaking renames on existing users.

## Imports and stability

- `import Algebraic.Core` is the stable starting point for signatures,
  programs, circuits, semantics, costs, substitution, and translation.
- `import Algebraic.Applications` exposes a small selection of ready-to-use
  compilers and flagship lower-bound endpoints under
  `Algebraic.Applications`.
- `import Algebraic` remains the complete umbrella. Focused module imports are
  preferred in reusable downstream code.
- The two facade modules are the most deliberately curated surface. Other
  public declarations remain available, but deep research namespaces may grow
  as their developments evolve.

## Names and namespaces

- Types and namespaces use `UpperCamelCase`; declarations use `lowerCamelCase`.
  Existing public names follow this convention and should not be mass-renamed.
- A theorem name should state its conclusion or principal inequality. Use a
  suffix such as `_iff`, `_eq`, `_le`, or `_lowerBound` when it makes the
  result easier to discover.
- Keep helper declarations `private` when they are proof-local. Reusable but
  non-facade machinery belongs in a descriptive nested namespace rather than
  the root `Algebraic` namespace.
- Prefer shallow aliases in `Algebraic.Applications` over moving established
  declarations out of their defining namespaces.

## Theorem and simp discipline

- State all mathematical promises explicitly: cost model, finiteness,
  bounded fan-in, semantic construction, and any circuit-local restriction.
- Document public structures, fields, definitions, and theorems. Module
  docstrings should say what is proved and where its assumptions stop.
- Mark a theorem `@[simp]` only when its left-hand side is in simplifier normal
  form and the rule is a dependable part of the API. Redundant aliases should
  remain ordinary rewrite theorems.
- Remove unused typeclass assumptions. Use `@[nolint unusedArguments]` only
  when an assumption is mathematically necessary to prove a proposition but
  cannot occur syntactically in its conclusion.

## Validation

Before submitting a change, run:

```sh
lake build Algebraic AlgebraicTests --wfail
lake test
lake lint
```

Public behavior belongs in the downstream-style `AlgebraicTests` suite.
Proof-local examples can remain near their defining module when they clarify a
construction, but they do not replace an import-level regression.
