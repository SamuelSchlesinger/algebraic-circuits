import Algebraic.Applications

/-!
# Circuit hierarchy public API regressions

These checks exercise the actual circuit-complexity measure, zero-width and
free-output conventions, the exact finite interval, real exponents, and the
bridge from size-class membership to concrete circuit families.
-/

namespace AlgebraicTests.Hierarchy

open Algebraic

/-- Output projections require no gates. -/
example : DeMorgan.complexity (fun input : Fin 1 → Bool => input 0) = 0 := by
  have bound := DeMorgan.complexity_le (Circuit.id DeMorgan.signature 1)
    (function := fun input => input 0) (by
      intro input
      funext output
      have equal : output = 0 := Subsingleton.elim _ _
      simp [equal])
  omega

/-- At zero inputs every scalar function costs exactly one internal gate. -/
example (function : ScalarFunction Bool 0) : DeMorgan.complexity function = 1 := by
  have upper := DeMorgan.complexity_le_add_hammingDist (fun _ => false) function
  have constant := DeMorgan.complexity_constant_le 0 false
  have valid := ((DeMorgan.minimumCircuit function).circuit.outputs 0).isLt
  change _ < 0 + DeMorgan.complexity function at valid
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at upper
  omega

/-- The natural measure has exactly the generic circuit-minimum semantics. -/
example (function : ScalarFunction Bool n) :
    (DeMorgan.complexity function : ENat) =
      Circuit.gateComplexity (σ := DeMorgan.signature) DeMorgan.interpretation
        (fun input (_ : Fin 1) => function input) :=
  DeMorgan.complexity_eq_gateComplexity function

/-- The Lipschitz bound uses the Hamming distance of whole truth tables. -/
example (left right : ScalarFunction Bool 3) :
    Nat.dist (DeMorgan.complexity left) (DeMorgan.complexity right) ≤
      6 * hammingDist left right :=
  DeMorgan.complexity_dist_le left right

/-- Every sufficiently large width simultaneously supports all the finite
thresholds through the Shannon scale, with the exact additive overhead. -/
example : ∀ᶠ n in Filter.atTop, ∀ s : Nat, 1 ≤ s → s ≤ 2 ^ n / n →
    ∃ function : ScalarFunction Bool n,
      s < DeMorgan.complexity function ∧ DeMorgan.complexity function ≤ s + 2 * n :=
  Applications.eventually_exists_complexity_between

/-- The theorem handles fractional exponents, not only natural degrees. -/
example : DeMorgan.polynomialSize 1 ⊂ DeMorgan.polynomialSize (3 / 2) :=
  Applications.polynomialSize_ssubset (by norm_num) (by norm_num)

/-- Constant factors are part of both sides of the hierarchy. -/
example : DeMorgan.sizeClass (fun n => n) ⊂ DeMorgan.sizeClass (fun n => n ^ 2) := by
  simpa only [pow_one] using
    Applications.sizeClass_pow_ssubset (a := 1) (b := 2) (by decide) (by decide)

/-- A class member provides a family of native shared circuits. -/
example (family : DeMorgan.FunctionFamily)
    (member : family ∈ DeMorgan.polynomialSize 2) :
    ∃ circuits : Circuit.Family DeMorgan.signature 1,
      circuits.Computes DeMorgan.interpretation (Target.scalarFamily family) ∧
        ∃ constant : Nat, ∀ᶠ n in Filter.atTop, circuits.size n ≤ constant * n ^ 2 := by
  apply (DeMorgan.mem_sizeClass_iff family (fun n => n ^ 2)).mp
  simpa only [DeMorgan.polynomialSize, show (2 : Real) = (2 : Nat) by norm_num,
    DeMorgan.polynomialBudget_natCast] using member

/-- Floors do not change the standard asymptotic meaning of real exponents. -/
example (family : DeMorgan.FunctionFamily) :
    family ∈ DeMorgan.polynomialSize (3 / 2) ↔
      ∃ constant : Real, ∀ᶠ n in Filter.atTop,
        (DeMorgan.complexity (family n) : Real) ≤ constant * (n : Real) ^ (3 / 2 : Real) :=
  DeMorgan.mem_polynomialSize_iff family (by norm_num)

end AlgebraicTests.Hierarchy
