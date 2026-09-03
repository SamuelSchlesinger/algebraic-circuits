import AlgebraicTests.Core
import AlgebraicTests.Circuit
import AlgebraicTests.CircuitFamily
import AlgebraicTests.AC0
import AlgebraicTests.AC0DecisionTree
import AlgebraicTests.AC0CanonicalDecisionTree
import AlgebraicTests.AC0NormalForm
import AlgebraicTests.AC0RandomRestriction
import AlgebraicTests.AC0SwitchingEncoding
import AlgebraicTests.AC0CanonicalEncoding
import AlgebraicTests.PartialAssignment
import AlgebraicTests.Translation
import AlgebraicTests.LowerBounds
import AlgebraicTests.MassProduction

/-!
# Algebraic public API regression suite

This test driver compiles small downstream-style uses of the library's public
circuit, circuit-family, translation, and lower-bound interfaces.
-/
