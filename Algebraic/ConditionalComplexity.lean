import Algebraic.Complexity.Relative

/-!
# Conditional circuit complexity

For a target `f` and a finite family `given` of functions of the same input,
`Circuit.conditionalGateComplexity interpretation f given` is the minimum
number of gates in a circuit `h` satisfying `h(x, given(x)) = f(x)`.
The original input coordinates and the supplied values are free; only the
gates of `h` are charged. Correctness is required on these consistent tuples,
with no restriction on `h(x, y)` when `y ≠ given(x)`.

The family is represented as `given : Target U n k`, so a list of scalar
functions `g : Fin k → ScalarFunction U n` is supplied as `fun x i => g i x`.
Targets may have multiple outputs and share gates. The weighted version is
`Circuit.conditionalCostComplexity`; both measures take values in `ℕ∞`, with
`⊤` for targets that cannot be computed even with the supplied values.

CSLib's Boolean `Synthesis` instead bounds additional gates relative to every
program already making a source family available, while preserving all of
that program's available functions. It is a budget predicate, not this
minimum over circuits with formal supplied inputs. The implication from a
conditional gate bound to `Synthesis` is in
`Algebraic.ConditionalComplexity.Boolean`.

## References

Stephen Wayne Boyack, *The Robustness of Combinatorial Measures of Boolean
Matrix Complexity*, MIT PhD thesis (1985), p. 30, defines circuit complexity
relative to supplied functions and proves the triangle inequality in
Proposition 2.2. Here the original coordinates are always supplied as well:
our `C(f | G)` corresponds to supplying `(id, G)` in that convention.
See https://hdl.handle.net/1721.1/15322.
-/

open Algebraic

namespace Cslib.Circuits.Circuit

/-- Compute `target` from the original inputs and the free values of `given`.
Only inputs of the form `(x, given x)` constrain the circuit. -/
def ComputesGiven (circuit : Circuit σ (n + k) gates m)
    (interpretation : Interpretation σ U)
    (target : Target U n m) (given : Target U n k) : Prop :=
  circuit.ComputesFrom interpretation target (fun input => Fin.append input (given input))

/-- Minimum weighted cost of computing `target` with the values of `given`
supplied as free extra inputs. Unrepresentable targets have value `⊤`. -/
noncomputable def conditionalCostComplexity
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) : ℕ∞ :=
  relativeCostComplexity interpretation operationCost target
    (fun input => Fin.append input (given input))

/-- Minimum number of gates computing `target` from the original inputs and
the free values of `given`. -/
noncomputable def conditionalGateComplexity
    (interpretation : Interpretation σ U)
    (target : Target U n m) (given : Target U n k) : ℕ∞ :=
  conditionalCostComplexity interpretation OperationCost.unit target given

/-- A concrete conditional implementation bounds the minimum weighted cost. -/
theorem conditionalCostComplexity_le
    {circuit : Circuit σ (n + k) gates m}
    {interpretation : Interpretation σ U}
    {target : Target U n m} {given : Target U n k}
    (operationCost : OperationCost σ)
    (computes : circuit.ComputesGiven interpretation target given) :
    conditionalCostComplexity interpretation operationCost target given ≤
      circuit.cost operationCost :=
  relativeCostComplexity_le operationCost computes

/-- A bound holding for every conditional implementation bounds the minimum. -/
theorem le_conditionalCostComplexity
    {interpretation : Interpretation σ U}
    {target : Target U n m} {given : Target U n k}
    (operationCost : OperationCost σ) (bound : ℕ∞)
    (lowerBound : ∀ {gates} (circuit : Circuit σ (n + k) gates m),
      circuit.ComputesGiven interpretation target given →
        bound ≤ circuit.cost operationCost) :
    bound ≤ conditionalCostComplexity interpretation operationCost target given :=
  le_relativeCostComplexity operationCost bound lowerBound

/-- A finite budget bounds conditional complexity exactly when some circuit
meets that budget. In particular, every finite minimum is attained. -/
theorem conditionalCostComplexity_le_iff
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) (budget : Nat) :
    conditionalCostComplexity interpretation operationCost target given ≤ budget ↔
      ∃ gates, ∃ circuit : Circuit σ (n + k) gates m,
        circuit.ComputesGiven interpretation target given ∧
          circuit.cost operationCost ≤ budget :=
  relativeCostComplexity_le_iff interpretation operationCost target
    (fun input => Fin.append input (given input)) budget

/-- Conditional complexity is finite exactly when some conditional
implementation exists; the supplied functions need not be representable. -/
theorem conditionalCostComplexity_lt_top_iff
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) :
    conditionalCostComplexity interpretation operationCost target given < ⊤ ↔
      ∃ gates, ∃ circuit : Circuit σ (n + k) gates m,
        circuit.ComputesGiven interpretation target given :=
  relativeCostComplexity_lt_top_iff interpretation operationCost target
    (fun input => Fin.append input (given input))

/-- An impossible conditional computation has complexity `⊤`. -/
@[simp] theorem conditionalCostComplexity_eq_top_iff
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) :
    conditionalCostComplexity interpretation operationCost target given = ⊤ ↔
      ¬ ∃ gates, ∃ circuit : Circuit σ (n + k) gates m,
        circuit.ComputesGiven interpretation target given :=
  relativeCostComplexity_eq_top_iff interpretation operationCost target
    (fun input => Fin.append input (given input))

/-- Equivalently, minimize ordinary complexity over all functions `h` with
`h(x, given(x)) = target(x)`. Values outside these consistent tuples are free. -/
theorem conditionalCostComplexity_eq_iInf
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) :
    conditionalCostComplexity interpretation operationCost target given =
      ⨅ h : Target U (n + k) m,
        ⨅ _ : ∀ input, h (Fin.append input (given input)) = target input,
          costComplexity interpretation operationCost h :=
  relativeCostComplexity_eq_iInf interpretation operationCost target
    (fun input => Fin.append input (given input))

/-- A conditional circuit gives an upper bound on conditional gate count. -/
theorem conditionalGateComplexity_le
    {circuit : Circuit σ (n + k) gates m}
    {interpretation : Interpretation σ U}
    {target : Target U n m} {given : Target U n k}
    (computes : circuit.ComputesGiven interpretation target given) :
    conditionalGateComplexity interpretation target given ≤ circuit.size := by
  simpa [conditionalGateComplexity] using
    conditionalCostComplexity_le OperationCost.unit computes

/-- A conditional gate bound is equivalent to a circuit with that many gates. -/
theorem conditionalGateComplexity_le_iff
    (interpretation : Interpretation σ U)
    (target : Target U n m) (given : Target U n k) (budget : Nat) :
    conditionalGateComplexity interpretation target given ≤ budget ↔
      ∃ gates ≤ budget, ∃ circuit : Circuit σ (n + k) gates m,
        circuit.ComputesGiven interpretation target given :=
  relativeGateComplexity_le_iff interpretation target
    (fun input => Fin.append input (given input)) budget

/-- Zero conditional gate complexity means that each output is a fixed
selection from the original input coordinates and the supplied functions.
No input-dependent selection is possible without gates. -/
theorem conditionalGateComplexity_eq_zero_iff
    (interpretation : Interpretation σ U)
    (target : Target U n m) (given : Target U n k) :
    conditionalGateComplexity interpretation target given = 0 ↔
      ∃ select : Fin m → Fin (n + k),
        ∀ input, Fin.append input (given input) ∘ select = target input :=
  relativeGateComplexity_eq_zero_iff interpretation target
    (fun input => Fin.append input (given input))

/-- Supplying extra values cannot increase the cost: they may be ignored. -/
theorem conditionalCostComplexity_le_costComplexity
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) :
    conditionalCostComplexity interpretation operationCost target given ≤
      costComplexity interpretation operationCost target :=
  relativeCostComplexity_mono_sources interpretation operationCost target
    (fun input => input) (fun input => Fin.append input (given input))
    (Fin.castAdd k) (fun input i => Fin.append_left input (given input) i)

/-- Conditioning on the empty family recovers ordinary weighted complexity. -/
@[simp] theorem conditionalCostComplexity_empty
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n 0) :
    conditionalCostComplexity interpretation operationCost target given =
      costComplexity interpretation operationCost target := by
  apply le_antisymm (conditionalCostComplexity_le_costComplexity ..)
  apply relativeCostComplexity_mono_sources interpretation operationCost target
    (fun input => Fin.append input (given input)) (fun input => input)
    (Fin.cast (Nat.add_zero n))
  intro input i
  exact Fin.addCases (fun j => (Fin.append_left input (given input) j).symm)
    (fun j => Fin.elim0 j) i

/-- Selecting any of the supplied outputs needs no gates. -/
theorem conditionalCostComplexity_select
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (given : Target U n k) (select : Fin m → Fin k) :
    conditionalCostComplexity interpretation operationCost
      (fun input output => given input (select output)) given = 0 := by
  simpa only [conditionalCostComplexity, Function.comp_apply, Fin.append_right] using
    relativeCostComplexity_select interpretation operationCost
      (fun input => Fin.append input (given input)) (Fin.natAdd n ∘ select)

/-- A supplied target has zero conditional cost, whether or not it has an
ordinary circuit over the chosen basis. -/
@[simp] theorem conditionalCostComplexity_self
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) :
    conditionalCostComplexity interpretation operationCost target target = 0 :=
  conditionalCostComplexity_select interpretation operationCost target (fun i => i)

/-- Reordering, duplicating, or extending the supplied family cannot increase
conditional complexity if all the old values remain accessible. -/
theorem conditionalCostComplexity_mono_given
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) (more : Target U n l)
    (select : Fin k → Fin l) (agrees : ∀ input i, more input (select i) = given input i) :
    conditionalCostComplexity interpretation operationCost target more ≤
      conditionalCostComplexity interpretation operationCost target given := by
  apply relativeCostComplexity_mono_sources interpretation operationCost target
    (fun input => Fin.append input (given input)) (fun input => Fin.append input (more input))
    (Fin.addCases (Fin.castAdd l) (Fin.natAdd n ∘ select))
  intro input i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
  · simpa only [Fin.addCases_right, Function.comp_apply, Fin.append_right] using agrees input j

/-- Free supplied values cannot increase gate complexity. -/
theorem conditionalGateComplexity_le_gateComplexity
    (interpretation : Interpretation σ U)
    (target : Target U n m) (given : Target U n k) :
    conditionalGateComplexity interpretation target given ≤
      gateComplexity interpretation target :=
  conditionalCostComplexity_le_costComplexity interpretation OperationCost.unit target given

/-- Empty conditioning recovers ordinary gate complexity. -/
@[simp] theorem conditionalGateComplexity_empty
    (interpretation : Interpretation σ U)
    (target : Target U n m) (given : Target U n 0) :
    conditionalGateComplexity interpretation target given =
      gateComplexity interpretation target :=
  conditionalCostComplexity_empty interpretation OperationCost.unit target given

/-- A supplied target requires zero gates. -/
@[simp] theorem conditionalGateComplexity_self
    (interpretation : Interpretation σ U) (target : Target U n m) :
    conditionalGateComplexity interpretation target target = 0 :=
  conditionalCostComplexity_self interpretation OperationCost.unit target

/-- Boyack's triangle inequality (Proposition 2.2), with the original inputs
always available and arbitrary natural-number operation costs: compute the
intermediate supplied family, then the target. -/
theorem conditionalCostComplexity_triangle
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (middle : Target U n l) (given : Target U n k) :
    conditionalCostComplexity interpretation operationCost target given ≤
      conditionalCostComplexity interpretation operationCost target middle +
        conditionalCostComplexity interpretation operationCost middle given := by
  let sources := fun input => Fin.append input (given input)
  have free : relativeCostComplexity interpretation operationCost
      (fun input : Fin n → U => input) sources = 0 := by
    simpa only [sources, Fin.append_left] using
      relativeCostComplexity_select interpretation operationCost sources (Fin.castAdd k)
  have triangle := relativeCostComplexity_triangle interpretation operationCost target
    (fun input => Fin.append input (middle input)) sources
  rw [relativeCostComplexity_pair_eq_of_left_eq_zero interpretation operationCost
    (fun input => input) middle sources free] at triangle
  exact triangle

/-- Boyack's triangle inequality specialized to unit gate cost. -/
theorem conditionalGateComplexity_triangle
    (interpretation : Interpretation σ U)
    (target : Target U n m) (middle : Target U n l) (given : Target U n k) :
    conditionalGateComplexity interpretation target given ≤
      conditionalGateComplexity interpretation target middle +
        conditionalGateComplexity interpretation middle given :=
  conditionalCostComplexity_triangle interpretation OperationCost.unit target middle given

/-- Supplying a family can save at most its ordinary computation cost. -/
theorem costComplexity_le_conditional_add
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) :
    costComplexity interpretation operationCost target ≤
      conditionalCostComplexity interpretation operationCost target given +
        costComplexity interpretation operationCost given := by
  simpa using conditionalCostComplexity_triangle interpretation operationCost
    target given (fun _ => Fin.elim0)

/-- A family that is already free to compute gives no complexity advantage. -/
theorem conditionalCostComplexity_eq_of_costComplexity_eq_zero
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k)
    (free : costComplexity interpretation operationCost given = 0) :
    conditionalCostComplexity interpretation operationCost target given =
      costComplexity interpretation operationCost target := by
  apply le_antisymm (conditionalCostComplexity_le_costComplexity ..)
  simpa only [free, add_zero] using
    costComplexity_le_conditional_add interpretation operationCost target given

/-- The chain upper bound: compute the supplied family, then the target,
retaining both as outputs. Equality need not hold because a joint circuit can
share intermediate wires that are absent from the supplied output family. -/
theorem costComplexity_pair_le
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (given : Target U n k) :
    costComplexity interpretation operationCost (fun input =>
      Fin.append (target input) (given input)) ≤
      conditionalCostComplexity interpretation operationCost target given +
        costComplexity interpretation operationCost given := by
  have pairBound := relativeCostComplexity_pair_le interpretation operationCost target given
    (fun input => Fin.append input (given input))
  change conditionalCostComplexity interpretation operationCost
      (fun input => Fin.append (target input) (given input)) given ≤
      conditionalCostComplexity interpretation operationCost target given +
        conditionalCostComplexity interpretation operationCost given given at pairBound
  rw [conditionalCostComplexity_self, add_zero] at pairBound
  exact (costComplexity_le_conditional_add interpretation operationCost _ given).trans
    (add_le_add pairBound le_rfl)

/-- The chain upper bound for gate complexity. -/
theorem gateComplexity_pair_le
    (interpretation : Interpretation σ U)
    (target : Target U n m) (given : Target U n k) :
    gateComplexity interpretation (fun input => Fin.append (target input) (given input)) ≤
      conditionalGateComplexity interpretation target given + gateComplexity interpretation given :=
  costComplexity_pair_le interpretation OperationCost.unit target given

end Cslib.Circuits.Circuit

namespace Algebraic.Circuit

export Cslib.Circuits.Circuit
  (ComputesGiven conditionalCostComplexity conditionalGateComplexity
   conditionalCostComplexity_le le_conditionalCostComplexity
   conditionalCostComplexity_le_iff conditionalCostComplexity_lt_top_iff
   conditionalCostComplexity_eq_top_iff conditionalCostComplexity_eq_iInf
   conditionalGateComplexity_le conditionalGateComplexity_le_iff
   conditionalGateComplexity_eq_zero_iff
   conditionalCostComplexity_le_costComplexity conditionalCostComplexity_empty
   conditionalCostComplexity_select conditionalCostComplexity_self
   conditionalCostComplexity_mono_given conditionalGateComplexity_le_gateComplexity
   conditionalGateComplexity_empty conditionalGateComplexity_self
   conditionalCostComplexity_triangle conditionalGateComplexity_triangle
   costComplexity_le_conditional_add conditionalCostComplexity_eq_of_costComplexity_eq_zero
   costComplexity_pair_le gateComplexity_pair_le)

end Algebraic.Circuit
