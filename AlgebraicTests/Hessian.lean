import Algebraic.Applications.Hessian

/-!
# A downstream polynomial lower bound

The polynomial `X₀ * X₁` needs a multiplication over the rationals. The proof
computes its two-by-two Hessian and applies the focused API without constructing
a Fusion certificate or a construction problem.
-/

namespace AlgebraicTests.Hessian

open Algebraic
open Algebraic.Fusion.Arithmetic.Interaction

private theorem product_hessian :
    Hessian.matrix (fun _ : Fin 2 => (0 : ℚ))
      (MvPolynomial.X 0 * MvPolynomial.X 1) = !![0, 1; 1, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Hessian.matrix, MvPolynomial.pderiv_mul]

example (circuit : Circuit (Arithmetic.signature ℚ) 2 g 1)
    (computes : circuit.eval (Arithmetic.interpretation MvPolynomial.C) MvPolynomial.X 0 =
      MvPolynomial.X 0 * MvPolynomial.X 1) :
    1 ≤ circuit.cost Arithmetic.multiplicationCost := by
  have bound := Applications.hessianRank_lowerBound id (fun _ => (0 : ℚ))
    (MvPolynomial.X 0 * MvPolynomial.X 1) circuit computes
  rw [product_hessian, Matrix.rank_of_det_ne_zero (by norm_num [Matrix.det_fin_two])] at bound
  simpa using bound

end AlgebraicTests.Hessian
