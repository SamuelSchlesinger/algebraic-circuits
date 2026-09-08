import Algebraic.Basis.DeMorgan.NativeCost
import Algebraic.Basis.DeMorgan.PairIndicator
import Algebraic.Basis.DeMorgan.Threshold
import Lean.Util.CollectAxioms

/-!
# Native De Morgan bounds without the retired topology development

These downstream examples retain the native cost checks and exercise the
support/read-once lower bounds using only focused circuit imports.
-/

namespace AlgebraicTests.NativeDeMorgan

open Algebraic Algebraic.DeMorgan

example (index : Fin n) : complexity (fun input => input index) = 0 :=
  complexity_input index

example (left right : ScalarFunction Bool n) :
    complexity (fun input => Bool.xor (left input) (right input)) ≤
      complexity left + complexity right + 4 :=
  complexity_xor_le left right

example (circuit : Circuit DeMorgan.signature n g m) (input : Fin n → Bool) :
    (withSharedConstants circuit).eval DeMorgan.interpretation input =
      circuit.eval DeMorgan.interpretation input :=
  withSharedConstants_eval circuit input

example (circuit : Circuit DeMorgan.signature n g 1)
    (f : ScalarFunction Bool n)
    (computes : circuit.Computes DeMorgan.interpretation (fun input _ => f input)) :
    complexity f ≤ circuit.cost DeMorgan.standardCost + 2 :=
  complexity_le_standardCost_add_two circuit computes

example : (thresholdExpression 3 5).gateCount = 2 := by decide

example : (thresholdExpression 0 0).gateCount = 1 := rfl

example (threshold : Nat) (input : Fin 4 → Bool) :
    (thresholdExpression 4 threshold).eval input =
      decide (threshold ≤ inputRank input) :=
  thresholdExpression_eval threshold input

example (pattern : Fin 0 → Bool) (value : Bool) :
    complexity (mask ∅ pattern value) ≤ 1 := by
  simpa using complexity_mask_le ∅ pattern value

example (positive : 0 < n) (point : Fin n → Bool) (value : Bool) :
    complexity (fun input => if input = point then value else !value) ≤ n :=
  complexity_point_indicator_le positive point value

example (circuit : Circuit DeMorgan.signature n g 1)
    (f : ScalarFunction Bool n)
    (computes : circuit.Computes DeMorgan.interpretation (fun input _ => f input))
    (essential : ∀ i, EssentialAt f i) (tight : circuit.cost DeMorgan.binaryCost + 1 ≤ n) :
    ∃ expression : DeMorgan.Expression n, expression.ReadOnce ∧ expression.eval = f :=
  exists_readOnce_of_binaryCost_le circuit computes essential tight

example (circuit : Circuit DeMorgan.signature n g 1)
    (f : ScalarFunction Bool n)
    (computes : circuit.Computes DeMorgan.interpretation (fun input _ => f input))
    (essential : ∀ i, EssentialAt f i) (nonunate : ¬Unate f) : n + 1 ≤ g :=
  size_ge_of_essential_nonunate circuit computes essential nonunate

example (positive : 0 < n) (left right : Fin n → Bool) (value : Bool)
    (different : left ≠ right) :
    complexity (pairIndicator left right value) ≤ n ↔ BooleanCube.graph.Adj left right :=
  complexity_pairIndicator_le_iff positive left right value different

example (value : Bool) :
    complexity (pairIndicator (![false, false] : Fin 2 → Bool) ![true, false] value) ≤ 2 := by
  apply complexity_pairIndicator_le_of_adjacent (by decide)
  change hammingDist (![false, false] : Fin 2 → Bool) ![true, false] = 1
  decide

example (value : Bool) :
    ¬complexity (pairIndicator (![false, false] : Fin 2 → Bool) ![true, true] value) ≤ 2 := by
  have lower := complexity_pairIndicator_ge (![false, false] : Fin 2 → Bool)
    ![true, true] value (by decide)
  omega

end AlgebraicTests.NativeDeMorgan

/- Preserve the axiom audit for every declaration in the retained circuit
modules, including private helpers and generated declarations. -/
set_option maxHeartbeats 2000000 in
run_cmd do
  let environment ← Lean.getEnv
  let modules : Array Lean.Name := #[
    `Algebraic.Analysis.Frontier, `Algebraic.BooleanCube.Neighbors,
    `Algebraic.Basis.DeMorgan.Operations, `Algebraic.Basis.DeMorgan.ReadOnce,
    `Algebraic.Basis.DeMorgan.TightCircuit, `Algebraic.Basis.DeMorgan.Mask,
    `Algebraic.Basis.DeMorgan.PairIndicator, `Algebraic.Basis.DeMorgan.NativeCost,
    `Algebraic.Basis.DeMorgan.Threshold]
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index]! then
        checked := checked + 1
        for dependency in ← Lean.collectAxioms name do
          unless allowed.contains dependency do
            throwError "Native De Morgan declaration {name} depends on forbidden axiom {dependency}"
  if checked = 0 then
    throwError "Native De Morgan axiom audit did not find any declarations"
  Lean.logInfo m!"Native De Morgan axiom audit passed for {checked} declarations."
