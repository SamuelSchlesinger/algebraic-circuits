import Algebraic.Applications.Waring

/-!
# Waring bounds from an ordinary sum equality

No circuit syntax or Fusion structure appears in these downstream premises.
The examples check a concrete four-variable bound and the zero-variable edge
case, where the target is one and an empty sum cannot represent it.
-/

open scoped BigOperators
open Algebraic

example (scale : Fin r → ℚ) (coefficients : Fin r → Fin 4 → ℚ)
    (represents :
      ∑ i, MvPolynomial.C (scale i) *
          (∑ j, MvPolynomial.C (coefficients i j) * MvPolynomial.X j) ^ 4 =
        ∏ j : Fin 4, (MvPolynomial.X j : MvPolynomial (Fin 4) ℚ)) :
    6 ≤ r := by
  have bound := Applications.waringSum_lowerBound 2 Finset.univ scale coefficients represents
  norm_num [Nat.centralBinom] at bound
  exact bound

example (scale : Fin r → ℚ) (coefficients : Fin r → Fin 0 → ℚ)
    (represents :
      ∑ i, MvPolynomial.C (scale i) *
          (∑ j, MvPolynomial.C (coefficients i j) * MvPolynomial.X j) ^ 0 =
        ∏ j : Fin 0, (MvPolynomial.X j : MvPolynomial (Fin 0) ℚ)) :
    1 ≤ r := by
  have bound := Applications.waringSum_lowerBound 0 Finset.univ scale coefficients represents
  simpa [Nat.centralBinom] using bound
