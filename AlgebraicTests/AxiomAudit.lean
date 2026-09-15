import Algebraic
import AlgebraicTests.AxiomFixtures
import Lean.Util.CollectAxioms

/-!
# Public-library axiom boundary

Check every library-owned declaration visible through the full `Algebraic`
import, including generated declarations and extensions in CSLib namespaces.
Ownership is determined by the declaring module, not the declaration's name.
Each check follows dependencies transitively, including private proof helpers
and dependencies in CSLib and Mathlib. Unexported declarations of modern
modules that are unreachable from the public interface are outside this audit.

This test permits only `propext`, `Classical.choice`, and `Quot.sound`. It
therefore rejects `sorryAx`, user axioms, and native-decision axioms in library
results. Tests that evaluate small circuits with `native_decide` are outside
the library and are deliberately not selected.
-/

private def assertStandardAxioms (name : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  unless (← Lean.getEnv).contains name do
    throwError "Axiom audit cannot find declaration {name}"
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for dependency in ← Lean.collectAxioms name do
    unless allowed.contains dependency do
      throwError "Declaration {name} depends on forbidden axiom {dependency}"

/- A test-only axiom and a theorem using it exercise transitive rejection.
Neither belongs to the public library or any library theorem's dependencies. -/
axiom AlgebraicTests.AxiomAudit.forbidden : True

theorem AlgebraicTests.AxiomAudit.transitiveFixture : True :=
  AlgebraicTests.AxiomAudit.forbidden

/--
error: Declaration AlgebraicTests.AxiomAudit.transitiveFixture depends on forbidden axiom AlgebraicTests.AxiomAudit.forbidden
-/
#guard_msgs in
run_cmd assertStandardAxioms `AlgebraicTests.AxiomAudit.transitiveFixture

/--
error: Declaration AlgebraicTests.AxiomFixtures.indirect depends on forbidden axiom AlgebraicTests.AxiomFixtures.forbidden
-/
#guard_msgs in
run_cmd assertStandardAxioms `AlgebraicTests.AxiomFixtures.indirect

/-- error: Axiom audit cannot find declaration AlgebraicTests.AxiomAudit.missingFixture -/
#guard_msgs in
run_cmd assertStandardAxioms `AlgebraicTests.AxiomAudit.missingFixture

set_option maxHeartbeats 10000000 in
run_cmd do
  let environment ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let owner := environment.header.moduleNames[index]!
      if (`Algebraic).isPrefixOf owner then
        checked := checked + 1
        assertStandardAxioms name
  if checked = 0 then
    throwError "Public-library axiom audit did not find any declarations"
  Lean.logInfo m!"Public-library axiom audit passed for {checked} declarations."
