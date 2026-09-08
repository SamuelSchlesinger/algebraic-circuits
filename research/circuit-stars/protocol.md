# Circuit-star geometry: fixed experimental protocol

This protocol is recorded before running the experiments for the five-part
geometry goal. Experimental circuit minima are distinct from Lean proofs.

## Model and domain

- Enumerate all 256 Boolean functions on three inputs.
- Truth-table bit `x` records the output on the binary input assignment `x`;
  input coordinate zero is the least significant bit.
- Count every AND, OR, NOT, constant, and identity gate as one. Inputs and
  designated output wires are free; intermediate values can be reused.
- Search shared DAG circuits by a complete bounded SAT encoding. Binary
  arguments may be ordered because AND and OR are commutative. Identity
  gates allow padding and selecting any earlier wire as the final output.
- Do not quotient by arbitrary input negations or NPN equivalence: these
  are not free operations in this native cost model.

## Recorded results

1. Determine every minimum gate count, with an independently evaluated
   circuit witness, solver/version provenance, and the search outcome at
   every smaller budget. Preserve the encoding and a reproducible checker.
2. At both constant centers and every budget, compute the face birth
   function over all 256 supports, face counts, minimal missing faces,
   and reduced simplicial Betti numbers over F2.
3. Find the first budget with a minimal missing face of cardinality at
   least three, if one exists. Preserve a concrete witness or the complete
   negative result. Do not change the endpoint after seeing the data.
4. For every budget and Hamming radius, measure the number of truth tables
   within that radius of the easy set. Compare with the union bound using
   exactly the same easy-set volume.
5. Construct the Alexander duals of the links and verify the finite
   homology/cohomology dimension correspondence, treating degenerate
   empty/full cases separately. Computational agreement is not a Lean
   proof of general Alexander duality.

## Formal work and completion requirements

- Generic and native theorems for minimal missing faces beyond pairs.
- Encoder/decoder/membership bounds for face birth, including repetition
  supports and the previously studied coordinate subcubes.
- XOR transport between arbitrary centers with explicit four-gate overhead.
- Distance to a nonempty sublevel, its metric properties and neighborhood
  bounds, and its interpretation as circuit approximation error.
- The combinatorial Alexander dual, its involution and monotonicity,
  the missing-face/facet correspondence, and a proved homological duality
  interface. Any remaining comparison boundary must be stated explicitly.
- Downstream tests, an axiom audit, full build/test/lint, generated API
  documentation, and an explanation of experimental findings and limits.

The objective includes all five directions. A partial library or a finite
dual-homology calculation alone does not complete the formal duality work.
