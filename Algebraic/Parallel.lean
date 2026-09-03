import Algebraic.Substitution
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Input reindexing and parallel circuits

This file provides the structural circuit operations used by simultaneous
evaluation arguments. `Circuit.mapInputs` rewires the original inputs without
adding gates, `Circuit.mapOutputs` selects or repeats designated outputs, and
`Circuit.parallel` places two circuits with the same input namespace side by
side. Parallel composition preserves sharing within each operand and has
exactly additive cost.
-/

namespace Algebraic

open scoped BigOperators

/-- Transport a circuit along equalities of its input, gate, and output
counts. This is a structural cast; it changes no gate or wire. -/
def Circuit.castCounts
    {n g m n' g' m' : Nat}
    (inputCount : n = n')
    (gateCount : g = g')
    (outputCount : m = m')
    (circuit : Circuit σ n g m) : Circuit σ n' g' m' := by
  subst n'
  subst g'
  subst m'
  exact circuit

/-- Casting circuit counts transports inputs and outputs by the corresponding
finite-index equalities and otherwise preserves evaluation. -/
@[simp] theorem Circuit.eval_castCounts
    {n g m n' g' m' : Nat}
    (inputCount : n = n')
    (gateCount : g = g')
    (outputCount : m = m')
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U) :
    (circuit.castCounts inputCount gateCount outputCount).eval
        interpretation input =
      fun output =>
        circuit.eval interpretation
          (input ∘ Fin.cast inputCount) (Fin.cast outputCount.symm output) := by
  subst n'
  subst g'
  subst m'
  rfl

/-- Casting circuit counts preserves weighted cost. -/
@[simp] theorem Circuit.cost_castCounts
    {n g m n' g' m' : Nat}
    (inputCount : n = n')
    (gateCount : g = g')
    (outputCount : m = m')
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost σ) :
    (circuit.castCounts inputCount gateCount outputCount).cost operationCost =
      circuit.cost operationCost := by
  subst n'
  subst g'
  subst m'
  rfl

/-- Casting circuit counts transports the gate count exactly. -/
@[simp] theorem Circuit.size_castCounts
    {n g m n' g' m' : Nat}
    (inputCount : n = n')
    (gateCount : g = g')
    (outputCount : m = m')
    (circuit : Circuit σ n g m) :
    (circuit.castCounts inputCount gateCount outputCount).size =
      circuit.size := by
  subst n'
  subst g'
  subst m'
  rfl

/-- Reindex the original inputs of a wire while leaving its gate index
unchanged. -/
def Wire.mapInputs
    (inputMap : Fin n -> Fin n') : Wire n g -> Wire n' g :=
  Fin.addCases (Wire.input ∘ inputMap) Wire.gate

@[simp] theorem Wire.mapInputs_input
    (inputMap : Fin n -> Fin n')
    (input : Fin n) :
    Wire.mapInputs (g := g) inputMap (Wire.input input) =
      Wire.input (inputMap input) := by
  simp [Wire.mapInputs]

@[simp] theorem Wire.mapInputs_gate
    (inputMap : Fin n -> Fin n')
    (gate : Fin g) :
    Wire.mapInputs inputMap (Wire.gate gate) =
      (Wire.gate gate : Wire n' g) := by
  simp [Wire.mapInputs]

/-- Reindex every original input of a program without changing its gates. -/
def Program.mapInputs
    (inputMap : Fin n -> Fin n') :
    Program σ n g -> Program σ n' g
  | .empty => .empty
  | .gate program line =>
      .gate (program.mapInputs inputMap)
        (line.mapWires (Wire.mapInputs inputMap))

/-- Input reindexing evaluates a program after precomposing its input. -/
theorem Program.eval_mapInputs
    (program : Program σ n g)
    (inputMap : Fin n -> Fin n')
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U) :
    (program.mapInputs inputMap).eval interpretation input =
      program.eval interpretation (input ∘ inputMap) := by
  induction program with
  | empty =>
      funext gate
      exact Fin.elim0 gate
  | @gate g program line ih =>
      funext gate
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · simp only [Program.mapInputs, Program.eval_gate_last]
        apply Line.eval_mapWires
        intro wire
        refine Fin.addCases (fun sourceInput => ?_)
          (fun sourceGate => ?_) wire
        · simp [Function.comp_apply]
        · simpa using congrFun ih sourceGate
      · simp only [Program.mapInputs, Program.eval_gate_castSucc]
        exact congrFun ih priorGate

/-- Input reindexing preserves the value of every mapped wire. -/
theorem Program.trace_mapInputs
    (program : Program σ n g)
    (inputMap : Fin n -> Fin n')
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U)
    (wire : Wire n g) :
    (program.mapInputs inputMap).trace interpretation input
        (Wire.mapInputs inputMap wire) =
      program.trace interpretation (input ∘ inputMap) wire := by
  refine Fin.addCases (fun sourceInput => ?_) (fun sourceGate => ?_) wire
  · simp [Function.comp_apply]
  · simp [Program.trace, Program.eval_mapInputs]

/-- Input reindexing leaves every gate label, and hence every weighted cost,
unchanged. -/
@[simp] theorem Program.cost_mapInputs
    (program : Program σ n g)
    (inputMap : Fin n -> Fin n')
    (operationCost : OperationCost σ) :
    (program.mapInputs inputMap).cost operationCost =
      program.cost operationCost := by
  induction program with
  | empty => rfl
  | gate program line ih =>
      simp [Program.mapInputs, Program.cost, ih]

/-- Rewire the original inputs of a circuit without adding gates. The map may
identify, duplicate, permute, or discard inputs. -/
def Circuit.mapInputs
    (circuit : Circuit σ n g m)
    (inputMap : Fin n -> Fin n') : Circuit σ n' g m where
  program := circuit.program.mapInputs inputMap
  outputs := Wire.mapInputs inputMap ∘ circuit.outputs

@[simp] theorem Circuit.eval_mapInputs
    (circuit : Circuit σ n g m)
    (inputMap : Fin n -> Fin n')
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U) :
    (circuit.mapInputs inputMap).eval interpretation input =
      circuit.eval interpretation (input ∘ inputMap) := by
  funext output
  exact circuit.program.trace_mapInputs inputMap interpretation input
    (circuit.outputs output)

@[simp] theorem Circuit.cost_mapInputs
    (circuit : Circuit σ n g m)
    (inputMap : Fin n -> Fin n')
    (operationCost : OperationCost σ) :
    (circuit.mapInputs inputMap).cost operationCost =
      circuit.cost operationCost := by
  exact circuit.program.cost_mapInputs inputMap operationCost

@[simp] theorem Circuit.size_mapInputs
    (circuit : Circuit σ n g m)
    (inputMap : Fin n -> Fin n') :
    (circuit.mapInputs inputMap).size = circuit.size := rfl

/-- Select, reorder, or repeat the designated outputs of a circuit without
changing its gates. -/
def Circuit.mapOutputs
    (circuit : Circuit σ n g m)
    (outputMap : Fin m' -> Fin m) : Circuit σ n g m' where
  program := circuit.program
  outputs := circuit.outputs ∘ outputMap

@[simp] theorem Circuit.eval_mapOutputs
    (circuit : Circuit σ n g m)
    (outputMap : Fin m' -> Fin m)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U) :
    (circuit.mapOutputs outputMap).eval interpretation input =
      circuit.eval interpretation input ∘ outputMap := rfl

@[simp] theorem Circuit.cost_mapOutputs
    (circuit : Circuit σ n g m)
    (outputMap : Fin m' -> Fin m)
    (operationCost : OperationCost σ) :
    (circuit.mapOutputs outputMap).cost operationCost =
      circuit.cost operationCost := rfl

@[simp] theorem Circuit.size_mapOutputs
    (circuit : Circuit σ n g m)
    (outputMap : Fin m' -> Fin m) :
    (circuit.mapOutputs outputMap).size = circuit.size := rfl

/-- Place two circuits with the same original inputs side by side and
concatenate their designated outputs. -/
def Circuit.parallel
    (left : Circuit σ n g m)
    (right : Circuit σ n h k) : Circuit σ n (g + h) (m + k) where
  program := right.program.instantiate left.program Wire.input
  outputs := Fin.addCases
    (fun output => Wire.Renaming.castAdd h (left.outputs output))
    (fun output =>
      Wire.Substitution.append (fun input => Wire.input input) h
        (right.outputs output))

/-- Parallel composition concatenates the two output vectors. -/
@[simp] theorem Circuit.eval_parallel
    (left : Circuit σ n g m)
    (right : Circuit σ n h k)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U) :
    (left.parallel right).eval interpretation input =
      Fin.append (left.eval interpretation input)
        (right.eval interpretation input) := by
  funext output
  refine Fin.addCases (fun leftOutput => ?_) (fun rightOutput => ?_) output
  · simp only [Fin.append_left, Circuit.eval, Circuit.parallel,
      Function.comp_apply, Fin.addCases_left]
    exact right.program.instantiate_trace_ambient left.program Wire.input
      interpretation input (left.outputs leftOutput)
  · simp only [Fin.append_right, Circuit.eval, Circuit.parallel,
      Function.comp_apply, Fin.addCases_right]
    change
      (right.program.instantiate left.program Wire.input).trace
          interpretation input
          (Wire.Substitution.append Wire.input h
            (right.outputs rightOutput)) =
        right.program.trace interpretation input (right.outputs rightOutput)
    rw [right.program.instantiate_trace left.program Wire.input
      interpretation input (right.outputs rightOutput)]
    have mappedInputs :
        left.program.trace interpretation input ∘
            (fun sourceInput : Fin n => Wire.input sourceInput) = input := by
      funext sourceInput
      simp [Function.comp_apply]
    rw [mappedInputs]

/-- Parallel composition has exactly additive weighted cost. -/
@[simp] theorem Circuit.cost_parallel
    (left : Circuit σ n g m)
    (right : Circuit σ n h k)
    (operationCost : OperationCost σ) :
    (left.parallel right).cost operationCost =
      left.cost operationCost + right.cost operationCost := by
  exact right.program.cost_instantiate left.program Wire.input operationCost

/-- Parallel composition has exactly additive gate count. -/
@[simp] theorem Circuit.size_parallel
    (left : Circuit σ n g m)
    (right : Circuit σ n h k) :
    (left.parallel right).size = left.size + right.size := rfl

/-- Put two equally wide output vectors into the row-major two-block layout
`Fin (2 * width)`. -/
def Circuit.parallelPair
    (left : Circuit σ n g width)
    (right : Circuit σ n h width) :
    Circuit σ n (g + h) (2 * width) :=
  (left.parallel right).mapOutputs (Fin.cast (Nat.two_mul width))

/-- Evaluation of `parallelPair` selects the indicated row-major block. -/
@[simp] theorem Circuit.eval_parallelPair_apply
    (left : Circuit σ n g width)
    (right : Circuit σ n h width)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U)
    (side : Fin 2)
    (coordinate : Fin width) :
    (left.parallelPair right).eval interpretation input
        (finProdFinEquiv (side, coordinate)) =
      Fin.cases (left.eval interpretation input coordinate)
        (fun _ => right.eval interpretation input coordinate) side := by
  rw [Circuit.parallelPair, Circuit.eval_mapOutputs,
    Function.comp_apply, Circuit.eval_parallel]
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · rw [show Fin.cast (Nat.two_mul width)
          (finProdFinEquiv ((0 : Fin 2), coordinate)) =
        Fin.castAdd width coordinate by
      apply Fin.ext
      simp [finProdFinEquiv]]
    rw [Fin.append_left]
    rfl
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    rw [show Fin.cast (Nat.two_mul width)
          (finProdFinEquiv ((Fin.succ 0 : Fin 2), coordinate)) =
        Fin.natAdd width coordinate by
      apply Fin.ext
      simp [finProdFinEquiv]]
    rw [Fin.append_right]
    rfl

@[simp] theorem Circuit.cost_parallelPair
    (left : Circuit σ n g width)
    (right : Circuit σ n h width)
    (operationCost : OperationCost σ) :
    (left.parallelPair right).cost operationCost =
      left.cost operationCost + right.cost operationCost := by
  simp [Circuit.parallelPair]

/-- Place a finite family of scalar circuits with a common input namespace
side by side. Each member may have a different gate count; the resulting gate
count is their finite sum. -/
def Circuit.parallelFin :
    (outputs : Nat) ->
    (gateCounts : Fin outputs -> Nat) ->
    ((output : Fin outputs) -> Circuit σ n (gateCounts output) 1) ->
      Circuit σ n (∑ output, gateCounts output) outputs
  | 0, _, _ => (Circuit.id σ n).mapOutputs Fin.elim0
  | outputs + 1, gateCounts, circuits =>
      let prefixCounts : Fin outputs -> Nat :=
        fun output => gateCounts output.castSucc
      let prefixCircuits : (output : Fin outputs) ->
          Circuit σ n (prefixCounts output) 1 :=
        fun output => circuits output.castSucc
      let prefixCircuit :=
        Circuit.parallelFin outputs prefixCounts prefixCircuits
      let suffix := circuits (Fin.last outputs)
      (prefixCircuit.parallel suffix).castCounts rfl
        (Fin.sum_univ_castSucc gateCounts).symm rfl

/-- `parallelFin` returns, at each output coordinate, the corresponding
member circuit's scalar value. -/
@[simp] theorem Circuit.eval_parallelFin
    (outputs : Nat)
    (gateCounts : Fin outputs -> Nat)
    (circuits : (output : Fin outputs) ->
      Circuit σ n (gateCounts output) 1)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U)
    (output : Fin outputs) :
    (Circuit.parallelFin outputs gateCounts circuits).eval
        interpretation input output =
      (circuits output).eval interpretation input 0 := by
  induction outputs with
  | zero => exact Fin.elim0 output
  | succ outputs inductionHypothesis =>
      refine Fin.lastCases ?_ (fun prefixOutput => ?_) output
      · simp only [Circuit.parallelFin, Circuit.eval_castCounts,
          Fin.cast_refl, Circuit.eval_parallel]
        rw [show Fin.last outputs = Fin.natAdd outputs (0 : Fin 1) by
          apply Fin.ext
          simp]
        simp only [Function.comp_id, id_eq]
        rw [Fin.append_right]
      · simp only [Circuit.parallelFin, Circuit.eval_castCounts,
          Fin.cast_refl, Circuit.eval_parallel]
        rw [show prefixOutput.castSucc = Fin.castAdd 1 prefixOutput by rfl]
        simp only [Function.comp_id, id_eq]
        rw [Fin.append_left]
        exact inductionHypothesis
          (fun selected : Fin outputs => gateCounts selected.castSucc)
          (fun selected : Fin outputs => circuits selected.castSucc)
          prefixOutput

/-- Exact weighted cost of a finite parallel family. -/
@[simp] theorem Circuit.cost_parallelFin
    (outputs : Nat)
    (gateCounts : Fin outputs -> Nat)
    (circuits : (output : Fin outputs) ->
      Circuit σ n (gateCounts output) 1)
    (operationCost : OperationCost σ) :
    (Circuit.parallelFin outputs gateCounts circuits).cost operationCost =
      ∑ output, (circuits output).cost operationCost := by
  induction outputs with
  | zero =>
      simp only [Circuit.parallelFin]
      rfl
  | succ outputs inductionHypothesis =>
      simp only [Circuit.parallelFin, Circuit.cost_castCounts,
        Circuit.cost_parallel]
      rw [inductionHypothesis]
      exact (Fin.sum_univ_castSucc
        (fun output => (circuits output).cost operationCost)).symm

/-- Place a finite family of equally wide vector circuits side by side in
row-major `(member, coordinate)` order. -/
def Circuit.parallelFinVector :
    (members width : Nat) ->
    (gateCounts : Fin members -> Nat) ->
    ((member : Fin members) ->
      Circuit σ n (gateCounts member) width) ->
      Circuit σ n (∑ member, gateCounts member) (members * width)
  | 0, width, _, _ =>
      (Circuit.id σ n).mapOutputs fun output =>
        Fin.elim0 (Fin.cast (Nat.zero_mul width) output)
  | members + 1, width, gateCounts, circuits =>
      let prefixCounts : Fin members -> Nat :=
        fun member => gateCounts member.castSucc
      let prefixCircuits : (member : Fin members) ->
          Circuit σ n (prefixCounts member) width :=
        fun member => circuits member.castSucc
      let prefixCircuit :=
        Circuit.parallelFinVector members width prefixCounts prefixCircuits
      let suffix := circuits (Fin.last members)
      (prefixCircuit.parallel suffix).castCounts rfl
        (Fin.sum_univ_castSucc gateCounts).symm (Nat.succ_mul members width).symm

/-- `parallelFinVector` evaluates the indicated member and coordinate. -/
@[simp] theorem Circuit.eval_parallelFinVector
    (members width : Nat)
    (gateCounts : Fin members -> Nat)
    (circuits : (member : Fin members) ->
      Circuit σ n (gateCounts member) width)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U)
    (member : Fin members)
    (coordinate : Fin width) :
    (Circuit.parallelFinVector members width gateCounts circuits).eval
        interpretation input (finProdFinEquiv (member, coordinate)) =
      (circuits member).eval interpretation input coordinate := by
  induction members with
  | zero => exact Fin.elim0 member
  | succ members inductionHypothesis =>
      refine Fin.lastCases ?_ (fun prefixMember => ?_) member
      · simp only [Circuit.parallelFinVector, Circuit.eval_castCounts,
          Fin.cast_refl, Function.comp_id, Circuit.eval_parallel]
        rw [show Fin.cast (Nat.succ_mul members width)
              (finProdFinEquiv (Fin.last members, coordinate)) =
            Fin.natAdd (members * width) coordinate by
          apply Fin.ext
          simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]]
        rw [Fin.append_right]
      · simp only [Circuit.parallelFinVector, Circuit.eval_castCounts,
          Fin.cast_refl, Function.comp_id, Circuit.eval_parallel]
        rw [show Fin.cast (Nat.succ_mul members width)
              (finProdFinEquiv (prefixMember.castSucc, coordinate)) =
            Fin.castAdd width (finProdFinEquiv
              (prefixMember, coordinate)) by
          apply Fin.ext
          simp [finProdFinEquiv]]
        rw [Fin.append_left]
        exact inductionHypothesis
          (fun selected : Fin members => gateCounts selected.castSucc)
          (fun selected : Fin members => circuits selected.castSucc)
          prefixMember

/-- Exact weighted cost of a finite parallel vector family. -/
@[simp] theorem Circuit.cost_parallelFinVector
    (members width : Nat)
    (gateCounts : Fin members -> Nat)
    (circuits : (member : Fin members) ->
      Circuit σ n (gateCounts member) width)
    (operationCost : OperationCost σ) :
    (Circuit.parallelFinVector members width gateCounts circuits).cost
        operationCost =
      ∑ member, (circuits member).cost operationCost := by
  induction members with
  | zero =>
      simp only [Circuit.parallelFinVector]
      rfl
  | succ members inductionHypothesis =>
      simp only [Circuit.parallelFinVector, Circuit.cost_castCounts,
        Circuit.cost_parallel]
      rw [inductionHypothesis]
      exact (Fin.sum_univ_castSucc
        (fun member => (circuits member).cost operationCost)).symm

end Algebraic
