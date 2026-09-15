module

/-!
# Imported axiom-audit fixture

This test-only modern module checks that the audit follows a public theorem's
private proof dependency using Lean's exported axiom metadata.
-/

namespace AlgebraicTests.AxiomFixtures

public axiom forbidden : True

private theorem hidden : True := forbidden

public theorem indirect : True := hidden

end AlgebraicTests.AxiomFixtures
