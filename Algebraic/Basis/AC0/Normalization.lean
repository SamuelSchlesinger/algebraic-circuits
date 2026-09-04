import Algebraic.Basis.AC0
import Algebraic.Translation.Block

/-!
# Dual-rail normalization for AC0 circuits

This module implements the local compiler underlying input-negation normal
form. Every Boolean value is represented by two wires carrying the value and
its complement. A source NOT swaps the two rails without adding a gate. A
source AND or OR produces both its ordinary output and its De Morgan dual,
using exactly two target gates.

The construction is semantic rather than syntactic: the same block
translation simulates both Boolean evaluation and the logical-depth
interpretation. Thus compilation preserves logical depth exactly and doubles
the charged AND/OR cost, including at fan-in zero.
-/

namespace Algebraic
namespace AC0
namespace DualRail

/-- Encode a Boolean together with its complement. -/
def encode (value : Bool) : Fin 2 -> Bool :=
  ![value, !value]

/-- Duplicate a logical depth across both rails. -/
def duplicateDepth (depth : Nat) : Fin 2 -> Nat :=
  ![depth, depth]

/-- A NOT gate swaps the two rails without adding a gate. -/
def notCircuit : Circuit signature (1 * 2) 0 2 where
  program := .empty
  outputs := ![Block.inputWire (0 : Fin 1) (1 : Fin 2),
    Block.inputWire (0 : Fin 1) (0 : Fin 2)]

/-- The positive AND output of a dual-rail AND gadget. -/
def andPositiveLine (inputCount : Nat) :
    Line signature (inputCount * 2) 0 :=
  { op := .and inputCount
    wires := fun input => Block.inputWire input (0 : Fin 2) }

/-- The complemented output of a dual-rail AND gadget, computed by OR. -/
def andNegativeLine (inputCount : Nat) :
    Line signature (inputCount * 2) 1 :=
  { op := .or inputCount
    wires := fun input => Block.inputWire input (1 : Fin 2) }

@[simp] theorem andPositiveLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 0 -> U) :
    (andPositiveLine inputCount).eval target input gates =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold andPositiveLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

@[simp] theorem andNegativeLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 1 -> U) :
    (andNegativeLine inputCount).eval target input gates =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold andNegativeLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

/-- The two-output gadget implementing AND and its complement. -/
def andCircuit (inputCount : Nat) :
    Circuit signature (inputCount * 2) 2 2 :=
  { program := (Program.empty.gate (andPositiveLine inputCount)).gate
      (andNegativeLine inputCount)
    outputs := ![Wire.gate (0 : Fin 2), Wire.gate (1 : Fin 2)] }

/-- The positive OR output of a dual-rail OR gadget. -/
def orPositiveLine (inputCount : Nat) :
    Line signature (inputCount * 2) 0 :=
  { op := .or inputCount
    wires := fun input => Block.inputWire input (0 : Fin 2) }

/-- The complemented output of a dual-rail OR gadget, computed by AND. -/
def orNegativeLine (inputCount : Nat) :
    Line signature (inputCount * 2) 1 :=
  { op := .and inputCount
    wires := fun input => Block.inputWire input (1 : Fin 2) }

@[simp] theorem orPositiveLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 0 -> U) :
    (orPositiveLine inputCount).eval target input gates =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold orPositiveLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

@[simp] theorem orNegativeLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 1 -> U) :
    (orNegativeLine inputCount).eval target input gates =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold orNegativeLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

/-- The two-output gadget implementing OR and its complement. -/
def orCircuit (inputCount : Nat) :
    Circuit signature (inputCount * 2) 2 2 :=
  { program := (Program.empty.gate (orPositiveLine inputCount)).gate
      (orNegativeLine inputCount)
    outputs := ![Wire.gate (0 : Fin 2), Wire.gate (1 : Fin 2)] }

/-- Number of gates in a dual-rail operation gadget. -/
def gateCount : Op -> Nat
  | .not => 0
  | .and _ | .or _ => 2

/-- Dual-rail compilation of arbitrary AC0 gates. -/
def translation : BlockTranslation signature signature 2 where
  gateCount := gateCount
  operation
    | .not => notCircuit
    | .and inputCount => andCircuit inputCount
    | .or inputCount => orCircuit inputCount

@[simp] theorem notCircuit_eval_zero
    (target : Interpretation signature U)
    (input : Fin (1 * 2) -> U) :
    notCircuit.eval target input 0 = input 1 := by
  rfl

@[simp] theorem notCircuit_eval_one
    (target : Interpretation signature U)
    (input : Fin (1 * 2) -> U) :
    notCircuit.eval target input 1 = input 0 := by
  rfl

@[simp] theorem andCircuit_eval_zero
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (andCircuit inputCount).eval target input 0 =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold andCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (andPositiveLine inputCount)).gate
      (andNegativeLine inputCount)).trace
        target input (Wire.gate (0 : Fin 2)) = _
  rw [show (Wire.gate (0 : Fin 2) : Wire (inputCount * 2) 2) =
      (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1).castSucc by rfl]
  rw [Program.trace_gate_castSucc]
  rw [show (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1) =
    Fin.last (inputCount * 2 + 0) by rfl]
  rw [Program.trace_gate_last, andPositiveLine_eval]

@[simp] theorem andCircuit_eval_one
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (andCircuit inputCount).eval target input 1 =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold andCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (andPositiveLine inputCount)).gate
      (andNegativeLine inputCount)).trace
        target input (Wire.gate (1 : Fin 2)) = _
  rw [show (Wire.gate (1 : Fin 2) : Wire (inputCount * 2) 2) =
      Fin.last (inputCount * 2 + 1) by rfl]
  rw [Program.trace_gate_last]
  exact andNegativeLine_eval inputCount target input _

@[simp] theorem orCircuit_eval_zero
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (orCircuit inputCount).eval target input 0 =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold orCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (orPositiveLine inputCount)).gate
      (orNegativeLine inputCount)).trace
        target input (Wire.gate (0 : Fin 2)) = _
  rw [show (Wire.gate (0 : Fin 2) : Wire (inputCount * 2) 2) =
      (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1).castSucc by rfl]
  rw [Program.trace_gate_castSucc]
  rw [show (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1) =
    Fin.last (inputCount * 2 + 0) by rfl]
  rw [Program.trace_gate_last, orPositiveLine_eval]

@[simp] theorem orCircuit_eval_one
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (orCircuit inputCount).eval target input 1 =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold orCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (orPositiveLine inputCount)).gate
      (orNegativeLine inputCount)).trace
        target input (Wire.gate (1 : Fin 2)) = _
  rw [show (Wire.gate (1 : Fin 2) : Wire (inputCount * 2) 2) =
      Fin.last (inputCount * 2 + 1) by rfl]
  rw [Program.trace_gate_last]
  exact orNegativeLine_eval inputCount target input _

@[simp] theorem encode_zero (value : Bool) :
    encode value 0 = value := by
  simp [encode]

@[simp] theorem encode_one (value : Bool) :
    encode value 1 = !value := by
  simp [encode]

private theorem interpretation_and_eq_false
    (input : Fin n -> Bool) :
    interpretation (.and n) input = false <->
      Exists fun k => input k = false := by
  rw [Bool.eq_false_iff]
  constructor
  · intro resultNotTrue
    have notAllTrue : ¬ forall k, input k = true :=
      fun allTrue => resultNotTrue ((interpretation_and_eq_true input).2 allTrue)
    rw [Classical.not_forall] at notAllTrue
    obtain ⟨argument, argumentNotTrue⟩ := notAllTrue
    exact ⟨argument, Bool.eq_false_iff.mpr argumentNotTrue⟩
  · rintro ⟨argument, argumentFalse⟩ resultTrue
    have argumentTrue := (interpretation_and_eq_true input).1 resultTrue argument
    simp [argumentFalse] at argumentTrue

private theorem interpretation_or_eq_false
    (input : Fin n -> Bool) :
    interpretation (.or n) input = false <->
      forall k, input k = false := by
  rw [Bool.eq_false_iff]
  constructor
  · intro resultNotTrue argument
    apply Bool.eq_false_iff.mpr
    intro argumentTrue
    apply resultNotTrue
    exact (interpretation_or_eq_true input).2 ⟨argument, argumentTrue⟩
  · intro allFalse resultTrue
    obtain ⟨argument, argumentTrue⟩ :=
      (interpretation_or_eq_true input).1 resultTrue
    have argumentFalse := allFalse argument
    simp [argumentFalse] at argumentTrue

@[simp] theorem duplicateDepth_apply (depth : Nat) (rail : Fin 2) :
    duplicateDepth depth rail = depth := by
  have railCases : rail = 0 ∨ rail = 1 := by omega
  rcases railCases with rfl | rfl <;> simp [duplicateDepth]

theorem operation_encode
    (op : Op)
    (input : Fin (arity op) -> Bool) :
    encode (interpretation op input) =
      (translation.operation op).eval interpretation
        (Block.flatten (encode ∘ input)) := by
  cases op with
  | not =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change encode (!(input 0)) 0 =
          notCircuit.eval interpretation (Block.flatten (encode ∘ input)) 0
        rw [notCircuit_eval_zero]
        change encode (!(input 0)) 0 = encode (input 0) 1
        simp
      · change encode (!(input 0)) 1 =
          notCircuit.eval interpretation (Block.flatten (encode ∘ input)) 1
        rw [notCircuit_eval_one]
        change encode (!(input 0)) 1 = encode (input 0) 0
        simp
  | and inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change encode (interpretation (.and inputCount) input) 0 =
          (andCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 0
        rw [andCircuit_eval_zero]
        simp
      · change encode (interpretation (.and inputCount) input) 1 =
          (andCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 1
        rw [andCircuit_eval_one]
        simp only [encode_one, Block.flatten_apply, Function.comp_apply,
          encode_one]
        apply Bool.eq_iff_iff.mpr
        simp [interpretation_and_eq_false]
  | or inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change encode (interpretation (.or inputCount) input) 0 =
          (orCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 0
        rw [orCircuit_eval_zero]
        simp
      · change encode (interpretation (.or inputCount) input) 1 =
          (orCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 1
        rw [orCircuit_eval_one]
        simp only [encode_one, Block.flatten_apply, Function.comp_apply,
          encode_one]
        apply Bool.eq_iff_iff.mpr
        simp [interpretation_or_eq_false]

/-- Boolean dual-rail simulation. -/
def booleanSimulation :
    BlockSimulation translation interpretation interpretation :=
  BlockSimulation.ofPreserves encode operation_encode

theorem operation_duplicateDepth
    (op : Op)
    (input : Fin (arity op) -> Nat) :
    duplicateDepth (logicalDepthInterpretation op input) =
      (translation.operation op).eval logicalDepthInterpretation
        (Block.flatten (duplicateDepth ∘ input)) := by
  cases op with
  | not =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change duplicateDepth (input 0) 0 =
          notCircuit.eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 0
        rw [notCircuit_eval_zero]
        change duplicateDepth (input 0) 0 = duplicateDepth (input 0) 1
        simp
      · change duplicateDepth (input 0) 1 =
          notCircuit.eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 1
        rw [notCircuit_eval_one]
        change duplicateDepth (input 0) 1 = duplicateDepth (input 0) 0
        simp
  | and inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change duplicateDepth (logicalDepthInterpretation (.and inputCount) input) 0 =
          (andCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 0
        rw [andCircuit_eval_zero]
        simp
      · change duplicateDepth (logicalDepthInterpretation (.and inputCount) input) 1 =
          (andCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 1
        rw [andCircuit_eval_one]
        simp [logicalDepthInterpretation]
  | or inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change duplicateDepth (logicalDepthInterpretation (.or inputCount) input) 0 =
          (orCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 0
        rw [orCircuit_eval_zero]
        simp [logicalDepthInterpretation]
      · change duplicateDepth (logicalDepthInterpretation (.or inputCount) input) 1 =
          (orCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 1
        rw [orCircuit_eval_one]
        simp [logicalDepthInterpretation]

/-- Logical-depth dual-rail simulation. -/
def depthSimulation :
    BlockSimulation translation logicalDepthInterpretation
      logicalDepthInterpretation :=
  BlockSimulation.ofPreserves duplicateDepth operation_duplicateDepth

theorem pullCost_andOrCost (op : Op) :
    translation.pullCost andOrCost op = 2 * andOrCost op := by
  cases op <;> simp [translation, gateCount, notCircuit, andCircuit,
    orCircuit, andPositiveLine, andNegativeLine, orPositiveLine,
    orNegativeLine, BlockTranslation.pullCost, Circuit.cost, Program.cost,
    andOrCost]

end DualRail
end AC0
end Algebraic
