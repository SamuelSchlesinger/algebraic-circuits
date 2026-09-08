import Algebraic.Basis.DeMorgan.StarBirth
import Algebraic.Basis.DeMorgan.NativeCost
import Algebraic.LowerBound.Counting.Shannon
import Algebraic.MassProduction.ShannonSynthesis
import Algebraic.MassProduction.Growth

/-!
# Exponential first contact of the constant stars

The finite star inequalities combine with the library's Shannon counting
and synthesis theorems. The conclusion is denominator-free: eventually
`2^n <= 4*n*tau(n)` and `n*tau(n) <= 32*2^n`. Thus first contact has order
`2^n/n`, although the constants already connect by paths at budget `n+1`.
-/

namespace Algebraic.DeMorgan

open Filter

/-- Native worst-case complexity inherits the explicit Shannon synthesis bound. -/
theorem maximumComplexity_le_shannon (large : 16 ≤ n) :
    maximumComplexity n ≤ 27 * 2 ^ n / n + 2 := by
  apply Finset.sup_le
  intro function _
  exact (complexity_le_standardCost_add_two
    (MassProduction.ShannonSynthesis.shannonCircuit n large function)
    (MassProduction.ShannonSynthesis.shannonCircuit_computes n large function)).trans
      (Nat.add_le_add_right
        (MassProduction.ShannonSynthesis.shannonCircuit_cost_le n large function) 2)

/-- The existing closed Shannon counting theorem supplies hard functions at every sufficiently large width. -/
theorem eventually_pow_div_lt_maximumComplexity :
    ∀ᶠ n in atTop, 2 ^ n / n < maximumComplexity n := by
  have maximum : signature.HasMaximumArity 2 := by
    constructor
    · intro op
      cases op <;> decide
    · exact ⟨.and, rfl⟩
  have hard := Circuit.asymptoticallyAlmostAllHard_shannon interpretation maximum
    (by decide : 2 ≤ Fintype.card Bool) (by decide : 2 ≤ 2) (by decide : 0 < 1)
  have witnesses := hard.eventually_exists_hard (Eventually.of_forall (fun n => by
    simp [Circuit.card_fullFamily, Target.count, Nat.card_eq_fintype_card]))
  filter_upwards [witnesses] with n witness
  obtain ⟨target, _, hardTarget⟩ := witness
  let function : ScalarFunction Bool n := fun input => target input 0
  have equal : (fun input (_ : Fin 1) => function input) = target := by
    funext input output
    have zero : output = 0 := Subsingleton.elim _ _
    simp [function, zero]
  rw [← equal] at hardTarget
  have lower := (gateHard_iff function _).mp hardTarget
  have upper := complexity_le_maximumComplexity function
  simpa using lower.trans_le upper

/-- First contact of the constant stars has exponential order `2^n/n`, with explicit comparison constants. -/
theorem eventually_constantStarMeeting_bounds :
    ∀ᶠ n in atTop,
      2 ^ n ≤ 4 * n * constantStarMeeting n ∧
        n * constantStarMeeting n ≤ 32 * 2 ^ n := by
  filter_upwards [eventually_pow_div_lt_maximumComplexity,
    MassProduction.Growth.eventually_const_mul_pow_le_two_pow 4 1,
    eventually_ge_atTop 17] with n hard exponential large
  simp only [pow_one] at exponential
  have positive : 0 < n := by omega
  have intersection := maximumComplexity_le_twice_constantStarMeeting n
  have quotientLarge : 4 ≤ 2 ^ n / n := (Nat.le_div_iff_mul_le positive).mpr (by simpa [Nat.mul_comm] using exponential)
  have meetingPositive : 1 ≤ constantStarMeeting n := by omega
  constructor
  · have quotientSmall : 2 ^ n / n < 2 * constantStarMeeting n + 2 := by omega
    have bound := (Nat.div_lt_iff_lt_mul positive).mp quotientSmall
    nlinarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have previous := maximumComplexity_le_shannon (show 16 ≤ m by omega)
    have contact := constantStarMeeting_succ_le m
    have bounded : constantStarMeeting (m + 1) ≤ 27 * 2 ^ m / m + 3 := by omega
    have multiplied := Nat.mul_le_mul_left m bounded
    have division := Nat.div_mul_le_self (27 * 2 ^ m) m
    rw [pow_succ] at exponential ⊢
    have scale : m + 1 ≤ 2 * m := by omega
    have scaled := Nat.mul_le_mul_right (constantStarMeeting (m + 1)) scale
    nlinarith

/-- The two constants already admit a simple path at the linear budget `n+1`. -/
theorem exists_constant_path (positive : 0 < n) :
    ∃ path : BooleanCube.graph.Walk (fun _ : Fin n → Bool => false) (fun _ => true),
      path.IsPath ∧ BooleanCube.Within complexity (n + 1) path := by
  simpa [Nat.add_comm] using exists_connecting_path_of_complexity_le positive
    (fun _ => false) (fun _ => true) 1 (complexity_constant_le n false) (complexity_constant_le n true)

end Algebraic.DeMorgan
