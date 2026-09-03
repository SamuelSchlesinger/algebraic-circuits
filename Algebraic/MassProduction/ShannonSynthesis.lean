import Algebraic.MassProduction.ShannonCircuit
import Algebraic.MassProduction.Statement
import Mathlib.Data.Nat.Log

/-!
# Uniform Shannon synthesis

This module specializes the native Shannon circuit to the standard
`O(2^N / N)` parameter choice and connects it to Boolean mass complexity.
-/

namespace Algebraic
namespace MassProduction
namespace ShannonSynthesis

/-! ## A uniform `O(2^N / N)` specialization

The parameter choice and arithmetic below follow the full-column-library
proof in [`ShannonUpper.lean`](https://github.com/SamuelSchlesinger/complexitylib/blob/dev/Complexitylib/Circuits/Internal/ShannonUpper.lean).
The circuit construction above is new to Algebraic; only the elementary
choice `k = floor(log_2 N) - 1` and its inequalities are reused.
-/

/-- Number of short address variables in the uniform specialization. -/
def shannonAddressWidth (inputs : Nat) : Nat :=
  Nat.log 2 inputs - 1

/-- Number of remaining data variables. -/
def shannonDataWidth (inputs : Nat) : Nat :=
  inputs - shannonAddressWidth inputs

private theorem log_ge_one
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    1 <= Nat.log 2 inputs :=
  Nat.le_log_of_pow_le (by omega) (by omega)

private theorem log_lt_inputs
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    Nat.log 2 inputs < inputs :=
  Nat.log_lt_of_lt_pow (by omega)
    (@Nat.lt_pow_self inputs 2 (by omega))

theorem shannonAddressWidth_ge_three
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    3 <= shannonAddressWidth inputs := by
  unfold shannonAddressWidth
  have := Nat.le_log_of_pow_le (by omega : 1 < 2)
    (show 2 ^ 4 <= inputs by omega)
  omega

theorem shannonDataWidth_pos
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    0 < shannonDataWidth inputs := by
  unfold shannonDataWidth shannonAddressWidth
  have := log_lt_inputs inputs inputsLarge
  omega

private theorem shannonAddressWidth_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    shannonAddressWidth inputs <= inputs := by
  unfold shannonAddressWidth
  have := log_lt_inputs inputs inputsLarge
  omega

/-- The selected address/data split has exactly the original input width. -/
theorem shannonAddressDataSum
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    shannonAddressWidth inputs + shannonDataWidth inputs = inputs := by
  unfold shannonDataWidth
  have := shannonAddressWidth_le inputs inputsLarge
  omega

private theorem shannonPowSplit
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    2 ^ shannonDataWidth inputs * 2 ^ shannonAddressWidth inputs =
      2 ^ inputs := by
  rw [← Nat.pow_add]
  congr 1
  rw [Nat.add_comm]
  exact shannonAddressDataSum inputs inputsLarge

private theorem two_mul_pow_address_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    2 * 2 ^ shannonAddressWidth inputs <= inputs := by
  unfold shannonAddressWidth
  have logPositive := log_ge_one inputs inputsLarge
  have powerIdentity :
      2 * 2 ^ (Nat.log 2 inputs - 1) = 2 ^ Nat.log 2 inputs := by
    conv_rhs =>
      rw [show Nat.log 2 inputs = (Nat.log 2 inputs - 1) + 1 by omega]
    rw [Nat.pow_succ]
    ring
  rw [powerIdentity]
  exact Nat.pow_log_le_self 2 (by omega)

private theorem inputs_lt_four_mul_pow_address
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    inputs < 4 * 2 ^ shannonAddressWidth inputs := by
  unfold shannonAddressWidth
  have logPositive := log_ge_one inputs inputsLarge
  have powerIdentity :
      4 * 2 ^ (Nat.log 2 inputs - 1) =
        2 ^ (Nat.log 2 inputs + 1) := by
    conv_rhs =>
      rw [show Nat.log 2 inputs + 1 =
        (Nat.log 2 inputs - 1) + 2 by omega]
    rw [Nat.pow_add]
    omega
  rw [powerIdentity]
  exact Nat.lt_pow_succ_log_self (by omega) inputs

private theorem two_inputs_plus_one_le_pow
    (inputs : Nat) (inputsAtLeastFour : 4 <= inputs) :
    2 * inputs + 1 <= 2 ^ inputs := by
  induction inputs with
  | zero => omega
  | succ prior inductionHypothesis =>
      cases Nat.lt_or_ge prior 4 with
      | inl below =>
          have : prior = 3 := by omega
          subst prior
          norm_num
      | inr above =>
          have priorBound := inductionHypothesis (by omega)
          calc
            2 * (prior + 1) + 1 = 2 * prior + 1 + 2 := by ring
            _ <= 2 ^ prior + 2 := by omega
            _ <= 2 ^ prior + 2 ^ prior := by
              nlinarith [@Nat.lt_pow_self prior 2 (by omega)]
            _ = 2 ^ (prior + 1) := by ring

private theorem square_le_pow
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    inputs * inputs <= 2 ^ inputs := by
  induction inputs with
  | zero => omega
  | succ prior inductionHypothesis =>
      cases Nat.lt_or_ge prior 16 with
      | inl below =>
          have : prior = 15 := by omega
          subst prior
          norm_num
      | inr above =>
          have priorSquare := inductionHypothesis (by omega)
          have linearBound := two_inputs_plus_one_le_pow prior (by omega)
          calc
            (prior + 1) * (prior + 1) =
                prior * prior + 2 * prior + 1 := by ring
            _ <= 2 ^ prior + (2 * prior + 1) := by omega
            _ <= 2 ^ prior + 2 ^ prior := by omega
            _ = 2 ^ (prior + 1) := by ring

private theorem dataTerm
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    6 * 2 ^ shannonDataWidth inputs * inputs <= 24 * 2 ^ inputs := by
  have inputBound := inputs_lt_four_mul_pow_address inputs inputsLarge
  calc
    6 * 2 ^ shannonDataWidth inputs * inputs <=
        6 * 2 ^ shannonDataWidth inputs *
          (4 * 2 ^ shannonAddressWidth inputs) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 24 * (2 ^ shannonDataWidth inputs *
        2 ^ shannonAddressWidth inputs) := by ring
    _ = 24 * 2 ^ inputs := by rw [shannonPowSplit inputs inputsLarge]

private theorem addressTerm
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    4 * 2 ^ shannonAddressWidth inputs * inputs <= 2 * 2 ^ inputs := by
  have addressBound := two_mul_pow_address_le inputs inputsLarge
  have squareBound := square_le_pow inputs inputsLarge
  calc
    4 * 2 ^ shannonAddressWidth inputs * inputs =
        2 * ((2 * 2 ^ shannonAddressWidth inputs) * inputs) := by ring
    _ <= 2 * (inputs * inputs) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right inputs addressBound)
    _ <= 2 * 2 ^ inputs := Nat.mul_le_mul_left 2 squareBound

private theorem pow_ge_four_mul
    (exponent : Nat) (atLeastFour : 4 <= exponent) :
    4 * exponent <= 2 ^ exponent := by
  induction exponent with
  | zero => omega
  | succ prior inductionHypothesis =>
      cases Nat.lt_or_ge prior 4 with
      | inl below =>
          have : prior = 3 := by omega
          subst prior
          norm_num
      | inr above =>
          have priorBound := inductionHypothesis (by omega)
          calc
            4 * (prior + 1) = 4 * prior + 4 := by ring
            _ <= 2 ^ prior + 4 := by omega
            _ <= 2 ^ prior + 2 ^ prior := by
              nlinarith [@Nat.lt_pow_self prior 2 (by omega)]
            _ = 2 ^ (prior + 1) := by ring

private theorem log_le_quarter
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    4 * Nat.log 2 inputs <= inputs := by
  have logAtLeastFour : 4 <= Nat.log 2 inputs :=
    Nat.le_log_of_pow_le (by omega) (by omega)
  calc
    4 * Nat.log 2 inputs <= 2 ^ Nat.log 2 inputs :=
      pow_ge_four_mul (Nat.log 2 inputs) logAtLeastFour
    _ <= inputs := Nat.pow_log_le_self 2 (by omega)

private theorem addressPowerPlusAddress_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    2 ^ shannonAddressWidth inputs + shannonAddressWidth inputs +
        (Nat.log 2 inputs + 1) <= inputs := by
  unfold shannonAddressWidth
  have logPositive : 1 <= Nat.log 2 inputs :=
    Nat.le_log_of_pow_le (by omega) (by omega)
  have powerIdentity :
      2 * 2 ^ (Nat.log 2 inputs - 1) = 2 ^ Nat.log 2 inputs := by
    conv_rhs =>
      rw [show Nat.log 2 inputs = (Nat.log 2 inputs - 1) + 1 by omega]
    rw [Nat.pow_succ]
    ring
  have addressPowerBound :
      2 * 2 ^ (Nat.log 2 inputs - 1) <= inputs := by
    rw [powerIdentity]
    exact Nat.pow_log_le_self 2 (by omega)
  have logarithmBound := log_le_quarter inputs inputsLarge
  omega

private theorem libraryTerm
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    (2 ^ (2 ^ shannonAddressWidth inputs) *
        2 ^ shannonAddressWidth inputs) * inputs <= 2 ^ inputs := by
  have exponentBound := addressPowerPlusAddress_le inputs inputsLarge
  have remainingBound : Nat.log 2 inputs + 1 <=
      inputs - (2 ^ shannonAddressWidth inputs +
        shannonAddressWidth inputs) := by
    omega
  have inputPowerBound : inputs <
      2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
        shannonAddressWidth inputs)) :=
    calc
      inputs < 2 ^ (Nat.log 2 inputs + 1) :=
        Nat.lt_pow_succ_log_self (by omega) inputs
      _ <= 2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs)) :=
        Nat.pow_le_pow_right (by omega) remainingBound
  have powerSplit :
      2 ^ (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs) *
        2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs)) = 2 ^ inputs := by
    rw [← Nat.pow_add]
    congr 1
    omega
  calc
    (2 ^ (2 ^ shannonAddressWidth inputs) *
        2 ^ shannonAddressWidth inputs) * inputs =
      2 ^ (2 ^ shannonAddressWidth inputs +
        shannonAddressWidth inputs) * inputs := by
        rw [Nat.pow_add]
    _ <= 2 ^ (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs) *
        2 ^ (inputs - (2 ^ shannonAddressWidth inputs +
          shannonAddressWidth inputs)) :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt inputPowerBound)
    _ = 2 ^ inputs := powerSplit

/-- The full native Shannon cost ledger, multiplied by `N`, is bounded by
`27 * 2^N`. -/
theorem shannonArithmetic
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    costBound (shannonAddressWidth inputs) (shannonDataWidth inputs) *
        inputs <= 27 * 2 ^ inputs := by
  have dataBound := dataTerm inputs inputsLarge
  have addressBound := addressTerm inputs inputsLarge
  have libraryBound := libraryTerm inputs inputsLarge
  unfold costBound
  calc
    (4 * 2 ^ shannonAddressWidth inputs +
        4 * 2 ^ shannonDataWidth inputs +
        2 ^ 2 ^ shannonAddressWidth inputs *
          2 ^ shannonAddressWidth inputs +
        2 * 2 ^ shannonDataWidth inputs) * inputs =
      4 * 2 ^ shannonAddressWidth inputs * inputs +
        6 * 2 ^ shannonDataWidth inputs * inputs +
        (2 ^ 2 ^ shannonAddressWidth inputs *
          2 ^ shannonAddressWidth inputs) * inputs := by ring
    _ <= 2 * 2 ^ inputs + 24 * 2 ^ inputs + 2 ^ inputs := by
      omega
    _ = 27 * 2 ^ inputs := by ring

/-- The selected finite cost ledger is at most `27 * 2^N / N`. -/
theorem shannonCostBound_le
    (inputs : Nat) (inputsLarge : 16 <= inputs) :
    costBound (shannonAddressWidth inputs) (shannonDataWidth inputs) <=
      27 * 2 ^ inputs / inputs := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  exact shannonArithmetic inputs inputsLarge

/-- Reindex a function along an equality of finite input counts. -/
def reindexFunction
    (inputCount : splitInputs = inputs)
    (function : ScalarFunction Bool inputs) :
    ScalarFunction Bool splitInputs :=
  fun input => function (input ∘ Fin.cast inputCount.symm)

/-- Uniform native Shannon circuit for an arbitrary `N`-input Boolean
function. -/
noncomputable def shannonCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    Circuit DeMorgan.signature inputs
      (synthesisGateCount
        (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      1 :=
  (circuit (addressWidth := shannonAddressWidth inputs)
    (dataWidth := shannonDataWidth inputs)
    (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      |>.castCounts (shannonAddressDataSum inputs inputsLarge) rfl rfl

@[simp] theorem shannonCircuit_eval
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (input : Fin inputs -> Bool) :
    (shannonCircuit inputs inputsLarge function).eval
        DeMorgan.interpretation input 0 = function input := by
  rw [shannonCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, id_eq]
  rw [circuit_eval]
  unfold reindexFunction
  apply congrArg function
  funext index
  simp [Function.comp_apply]

theorem shannonCircuit_computes
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    (shannonCircuit inputs inputsLarge function).Computes
      DeMorgan.interpretation (scalarTarget function) := by
  intro input
  funext output
  have outputZero : output = 0 := Fin.eq_zero output
  subst output
  exact shannonCircuit_eval inputs inputsLarge function input

theorem shannonCircuit_cost_le
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    (shannonCircuit inputs inputsLarge function).cost
        DeMorgan.standardCost <= 27 * 2 ^ inputs / inputs := by
  rw [shannonCircuit, Circuit.cost_castCounts]
  exact (circuit_cost_le
    (reindexFunction (shannonAddressDataSum inputs inputsLarge) function)).trans
      (shannonCostBound_le inputs inputsLarge)

/-- The concrete independently replicated Shannon circuit. -/
noncomputable def replicatedShannonCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    Circuit DeMorgan.signature (copies * inputs)
      (copies * synthesisGateCount
        (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      copies :=
  (shannonCircuit inputs inputsLarge function).replicateScalar copies

theorem replicatedShannonCircuit_computes
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    (replicatedShannonCircuit inputs inputsLarge function copies).Computes
      DeMorgan.interpretation (directProduct function copies) := by
  intro input
  rw [replicatedShannonCircuit, Circuit.eval_replicateScalar]
  funext copy
  exact shannonCircuit_eval inputs inputsLarge function
    (directProductInput input copy)

/-- A minimum-cost realization of a finite Boolean direct product, selected
from the nonempty implementation family witnessed by Shannon replication. -/
noncomputable def minimumMassCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    Circuit.Minimum DeMorgan.standardCost DeMorgan.interpretation
      (directProduct function copies) :=
  Circuit.minimum DeMorgan.standardCost
    (replicatedShannonCircuit inputs inputsLarge function copies)
    DeMorgan.interpretation (directProduct function copies)
    (replicatedShannonCircuit_computes inputs inputsLarge function copies)

/-- The selected minimum circuit realizes `booleanMassComplexity` exactly. -/
theorem minimumMassCircuit_cost_eq_complexity
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    booleanMassComplexity function copies =
      ((minimumMassCircuit inputs inputsLarge function copies).circuit.cost
        DeMorgan.standardCost : ENat) := by
  unfold booleanMassComplexity
  exact Circuit.costComplexity_eq DeMorgan.standardCost
    (minimumMassCircuit inputs inputsLarge function copies).computes
    (minimumMassCircuit inputs inputsLarge function copies).minimal.cost

theorem minimumMassCircuit_cost_le
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies bound : Nat)
    (complexityBound : booleanMassComplexity function copies <=
      (bound : Nat)) :
    (minimumMassCircuit inputs inputsLarge function copies).circuit.cost
        DeMorgan.standardCost <= bound := by
  have castBound :
      ((minimumMassCircuit inputs inputsLarge function copies).circuit.cost
          DeMorgan.standardCost : ENat) <= (bound : Nat) := by
    rw [← minimumMassCircuit_cost_eq_complexity]
    exact complexityBound
  exact_mod_cast castBound

/-- Naive replication of native Shannon synthesis bounds any finite number
of independent copies.  This is the base finite upper bound used before the
mass-production composition improves the dependence on `copies`. -/
theorem booleanMassComplexity_le_replicatedShannon
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    booleanMassComplexity function copies <=
      (copies * (27 * 2 ^ inputs / inputs) : Nat) := by
  let base := shannonCircuit inputs inputsLarge function
  let replicated := base.replicateScalar copies
  have computes : replicated.Computes DeMorgan.interpretation
      (directProduct function copies) := by
    intro input
    rw [show replicated = base.replicateScalar copies by rfl,
      Circuit.eval_replicateScalar]
    funext copy
    exact shannonCircuit_eval inputs inputsLarge function
      (directProductInput input copy)
  have complexityBound := replicated.costComplexity_le
    DeMorgan.standardCost computes
  have finiteBound : replicated.cost DeMorgan.standardCost <=
      copies * (27 * 2 ^ inputs / inputs) := by
    rw [show replicated = base.replicateScalar copies by rfl,
      Circuit.cost_replicateScalar]
    apply Nat.mul_le_mul_left
    exact shannonCircuit_cost_le inputs inputsLarge function
  unfold booleanMassComplexity
  exact complexityBound.trans (by exact_mod_cast finiteBound)

end ShannonSynthesis
end MassProduction
end Algebraic
