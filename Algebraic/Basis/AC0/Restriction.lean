import Algebraic.Basis.AC0
import Algebraic.PartialAssignment
import Mathlib.Data.List.OfFn

/-!
# Partial evaluation of AC0 circuits

This module rebuilds arbitrary-fan-in AC0 programs after a Boolean partial
assignment. Fixed inputs and forced gates are represented as residual Boolean
constants, while genuinely live values are represented by wires over the
compact namespace of live variables.

The local connective simplifier is deliberately algebraic. An absorbing
constant forces an AND or OR gate; otherwise neutral constants are discarded
and the remaining wires feed one residual gate. No truth-table search or
finite-circuit optimization is involved.
-/

namespace Algebraic
namespace AC0

namespace Connective

/-- The arbitrary-fan-in operation associated with a connective. -/
def operation : Connective -> Nat -> Op
  | .and => .and
  | .or => .or

/-- The neutral Boolean for a connective. -/
def neutral : Connective -> Bool
  | .and => true
  | .or => false

/-- The Boolean which forces a connective independently of other inputs. -/
def absorbing : Connective -> Bool
  | .and => false
  | .or => true

/-- Boolean semantics of an arbitrary-fan-in connective. -/
def eval : (connective : Connective) -> (Fin r -> Bool) -> Bool
  | .and, input => interpretation (.and r) input
  | .or, input => interpretation (.or r) input

@[simp] theorem operation_cost
    (connective : Connective)
    (arity : Nat) :
    andOrCost (connective.operation arity) = 1 := by
  cases connective <;> rfl

end Connective

/-- A Boolean constant or a wire in a partially evaluated AC0 program. -/
inductive ResidualValue (n g : Nat)
  | constant (value : Bool)
  | wire (wire : Wire n g)
  deriving DecidableEq

namespace ResidualValue

/-- Evaluate a residual value in a residual program. -/
def eval
    (program : Program signature n g)
    (input : Fin n -> Bool) : ResidualValue n g -> Bool
  | .constant value => value
  | .wire sourceWire => program.trace interpretation input sourceWire

/-- Transport a residual value through a wire map. -/
def mapWires
    (wireMap : Wire n g -> Wire k h) :
    ResidualValue n g -> ResidualValue k h
  | .constant value => .constant value
  | .wire sourceWire => .wire (wireMap sourceWire)

/-- Return the represented wire, if the value is nonconstant. -/
def wire? : ResidualValue n g -> Option (Wire n g)
  | .constant _ => none
  | .wire sourceWire => some sourceWire

@[simp] theorem eval_constant
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (value : Bool) :
    (constant value : ResidualValue n g).eval program input = value := rfl

@[simp] theorem eval_wire
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (wire : Wire n g) :
    (ResidualValue.wire wire).eval program input =
      program.trace interpretation input wire := rfl

@[simp] theorem mapWires_constant
    (wireMap : Wire n g -> Wire k h)
    (value : Bool) :
    (constant value : ResidualValue n g).mapWires wireMap =
      .constant value := rfl

@[simp] theorem mapWires_wire
    (wireMap : Wire n g -> Wire k h)
    (wire : Wire n g) :
    (ResidualValue.wire wire).mapWires wireMap =
      .wire (wireMap wire) := rfl

end ResidualValue

/-- The nonconstant arguments of a gate, in their original order. -/
def residualWires
    (values : Fin r -> ResidualValue n g) : List (Wire n g) :=
  (List.ofFn values).filterMap ResidualValue.wire?

@[simp] theorem mem_residualWires
    (values : Fin r -> ResidualValue n g)
    (wire : Wire n g) :
    wire ∈ residualWires values <->
      Exists fun argument => values argument = .wire wire := by
  simp only [residualWires, List.mem_filterMap, List.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨argument, rfl⟩, present⟩
    cases value_eq : values argument with
    | constant value => simp [ResidualValue.wire?, value_eq] at present
    | wire sourceWire =>
      simp [ResidualValue.wire?, value_eq] at present
      subst sourceWire
      exact ⟨argument, value_eq⟩
  · rintro ⟨argument, value_eq⟩
    exact ⟨values argument, ⟨argument, rfl⟩, by
      simp [ResidualValue.wire?, value_eq]⟩

/-- A connective gate whose constant arguments have been removed. -/
def residualLine
    (connective : Connective)
    (wires : List (Wire n g)) : Line signature n g :=
  match connective with
  | .and =>
      { op := .and wires.length
        wires := wires.get }
  | .or =>
      { op := .or wires.length
        wires := wires.get }

/-- Result of locally simplifying one charged connective gate. -/
inductive ConnectiveReduction (n g : Nat)
  | value (result : ResidualValue n g)
  | line (result : Line signature n g)

namespace ConnectiveReduction

/-- Evaluate a local gate reduction against its preceding program. -/
def eval
    (program : Program signature n g)
    (input : Fin n -> Bool) : ConnectiveReduction n g -> Bool
  | .value result => result.eval program input
  | .line result =>
      result.eval interpretation input (program.eval interpretation input)

/-- Whether the reduction retains one charged gate. -/
def cost : ConnectiveReduction n g -> Nat
  | .value _ => 0
  | .line _ => 1

@[simp] theorem cost_le_one (result : ConnectiveReduction n g) :
    result.cost <= 1 := by
  cases result <;> simp [cost]

end ConnectiveReduction

/-- Simplify one arbitrary-fan-in AND or OR from already restricted arguments. -/
noncomputable def simplifyConnective
    (connective : Connective)
    (values : Fin r -> ResidualValue n g) :
    ConnectiveReduction n g :=
  if _forced : Exists fun argument =>
      values argument = .constant connective.absorbing then
    .value (.constant connective.absorbing)
  else
    let wires := residualWires values
    if _noWires : wires = [] then
      .value (.constant connective.neutral)
    else
      .line (residualLine connective wires)

/-- If a gate is not forced, every constant argument is its connective's
neutral value. -/
theorem argument_eval_eq_neutral_of_not_forced_of_not_wire
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (notForced : Not (Exists fun argument =>
      values argument = .constant connective.absorbing))
    (argument : Fin r)
    (notWire : Not (Exists fun sourceWire =>
      values argument = .wire sourceWire)) :
    (values argument).eval program input = connective.neutral := by
  cases value_eq : values argument with
  | wire sourceWire => exact False.elim (notWire ⟨sourceWire, value_eq⟩)
  | constant value =>
      have notAbsorbing :
          values argument ≠ .constant connective.absorbing :=
        fun equal => notForced ⟨argument, equal⟩
      cases connective <;> cases value <;>
        simp_all [Connective.absorbing, Connective.neutral]

/-- Removing neutral constants from a non-forced connective preserves its
Boolean value. -/
theorem residualLine_eval_of_not_forced
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (notForced : Not (Exists fun argument =>
      values argument = .constant connective.absorbing)) :
    (residualLine connective (residualWires values)).eval interpretation input
        (program.eval interpretation input) =
      connective.eval (fun argument =>
        (values argument).eval program input) := by
  cases connective with
  | and =>
      change interpretation (.and (residualWires values).length)
          (fun argument => program.trace interpretation input
            ((residualWires values).get argument)) =
        interpretation (.and r) (fun argument =>
          (values argument).eval program input)
      rw [Bool.eq_iff_iff, interpretation_and_eq_true,
        interpretation_and_eq_true]
      constructor
      · intro residualTrue argument
        cases value_eq : values argument with
        | constant value =>
            simpa [value_eq, Connective.neutral] using
              (argument_eval_eq_neutral_of_not_forced_of_not_wire
                .and values program input notForced argument (by
                  rintro ⟨sourceWire, impossible⟩
                  simp [value_eq] at impossible))
        | wire sourceWire =>
            have present : sourceWire ∈ residualWires values :=
              (mem_residualWires values sourceWire).2
                ⟨argument, value_eq⟩
            obtain ⟨residualArgument, selected⟩ :=
              List.mem_iff_get.mp present
            have selectedTrue := residualTrue residualArgument
            change program.trace interpretation input
              ((residualWires values).get residualArgument) = true at selectedTrue
            rw [selected] at selectedTrue
            exact selectedTrue
      · intro sourceTrue residualArgument
        have present := List.get_mem (residualWires values) residualArgument
        obtain ⟨argument, value_eq⟩ :=
          (mem_residualWires values _).1 present
        have argumentTrue := sourceTrue argument
        change program.trace interpretation input
          ((residualWires values).get residualArgument) = true
        simpa [value_eq] using argumentTrue
  | or =>
      change interpretation (.or (residualWires values).length)
          (fun argument => program.trace interpretation input
            ((residualWires values).get argument)) =
        interpretation (.or r) (fun argument =>
          (values argument).eval program input)
      rw [Bool.eq_iff_iff, interpretation_or_eq_true,
        interpretation_or_eq_true]
      constructor
      · rintro ⟨residualArgument, residualTrue⟩
        have present := List.get_mem (residualWires values) residualArgument
        obtain ⟨argument, value_eq⟩ :=
          (mem_residualWires values _).1 present
        refine ⟨argument, ?_⟩
        change program.trace interpretation input
          ((residualWires values).get residualArgument) = true at residualTrue
        simpa [value_eq] using residualTrue
      · rintro ⟨argument, argumentTrue⟩
        cases value_eq : values argument with
        | constant value =>
            have neutral :=
              argument_eval_eq_neutral_of_not_forced_of_not_wire
                .or values program input notForced argument (by
                  rintro ⟨sourceWire, impossible⟩
                  simp [value_eq] at impossible)
            rw [value_eq] at argumentTrue
            simp_all [Connective.neutral]
        | wire sourceWire =>
            have present : sourceWire ∈ residualWires values :=
              (mem_residualWires values sourceWire).2
                ⟨argument, value_eq⟩
            obtain ⟨residualArgument, selected⟩ :=
              List.mem_iff_get.mp present
            refine ⟨residualArgument, ?_⟩
            rw [selected]
            simpa [value_eq] using argumentTrue

/-- An absorbing residual constant forces the original connective. -/
theorem connective_eval_eq_absorbing_of_forced
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (forced : Exists fun argument =>
      values argument = .constant connective.absorbing) :
    connective.eval (fun argument =>
      (values argument).eval program input) = connective.absorbing := by
  cases connective with
  | and =>
      change interpretation (.and r) (fun argument =>
        (values argument).eval program input) = false
      apply Bool.eq_false_iff.mpr
      intro resultTrue
      obtain ⟨argument, value_eq⟩ := forced
      have argumentTrue :=
        (interpretation_and_eq_true _).1 resultTrue argument
      rw [value_eq] at argumentTrue
      contradiction
  | or =>
      change interpretation (.or r) (fun argument =>
        (values argument).eval program input) = true
      apply (interpretation_or_eq_true _).2
      obtain ⟨argument, value_eq⟩ := forced
      exact ⟨argument, by simp [value_eq, Connective.absorbing]⟩

/-- If no argument is a wire and the connective is not forced, all arguments
are neutral and so is the gate output. -/
theorem connective_eval_eq_neutral_of_no_wires
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (notForced : Not (Exists fun argument =>
      values argument = .constant connective.absorbing))
    (noWires : residualWires values = []) :
    connective.eval (fun argument =>
      (values argument).eval program input) = connective.neutral := by
  have noWire (argument : Fin r) :
      Not (Exists fun sourceWire => values argument = .wire sourceWire) := by
    rintro ⟨sourceWire, value_eq⟩
    have present : sourceWire ∈ residualWires values :=
      (mem_residualWires values sourceWire).2 ⟨argument, value_eq⟩
    rw [noWires] at present
    simp at present
  cases connective with
  | and =>
      change interpretation (.and r) (fun argument =>
        (values argument).eval program input) = true
      apply (interpretation_and_eq_true _).2
      intro argument
      exact argument_eval_eq_neutral_of_not_forced_of_not_wire
        .and values program input notForced argument (noWire argument)
  | or =>
      change interpretation (.or r) (fun argument =>
        (values argument).eval program input) = false
      apply Bool.eq_false_iff.mpr
      intro resultTrue
      obtain ⟨argument, argumentTrue⟩ :=
        (interpretation_or_eq_true _).1 resultTrue
      have neutral := argument_eval_eq_neutral_of_not_forced_of_not_wire
        .or values program input notForced argument (noWire argument)
      rw [neutral] at argumentTrue
      contradiction

/-- The local simplifier exactly preserves the value of an arbitrary-fan-in
AND or OR gate. -/
theorem simplifyConnective_eval
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool) :
    (simplifyConnective connective values).eval program input =
      connective.eval (fun argument =>
        (values argument).eval program input) := by
  unfold simplifyConnective
  split
  · rename_i forced
    exact (connective_eval_eq_absorbing_of_forced
      connective values program input forced).symm
  · rename_i notForced
    dsimp only
    split
    · rename_i noWires
      exact (connective_eval_eq_neutral_of_no_wires
        connective values program input notForced noWires).symm
    · exact residualLine_eval_of_not_forced
        connective values program input notForced

end AC0
end Algebraic
