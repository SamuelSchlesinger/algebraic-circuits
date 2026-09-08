import Algebraic.Basis.DeMorgan.Geometry

/-!
# Coarea and boundary bands for circuit complexity

The generic finite cube identities specialize to the minimum number of
internal De Morgan gates. The bound on total perimeter uses the proved
`2*n` Lipschitz estimate and the exact number of truth-table cube edges.
-/

namespace Algebraic.DeMorgan

/-- Exact coarea for all circuit-complexity sublevels at a fixed input width. -/
theorem complexity_coarea (n : Nat) :
    ∑ threshold ∈ Finset.range (BooleanCube.maximumCost (@complexity n)),
      (BooleanCube.edgeBoundary (@complexity n) threshold).card =
        ∑ edge ∈ BooleanCube.edges (ι := Fin n → Bool),
          Nat.dist (complexity edge.1) (complexity (BooleanCube.edgeEnd edge)) :=
  BooleanCube.sum_edgeBoundary_eq (@complexity n) _
    (BooleanCube.cost_le_maximumCost (@complexity n))

/-- The sum of all boundary sizes is at most `2*n` times the number of cube edges. -/
theorem complexity_totalBoundary_le (n : Nat) :
    ∑ threshold ∈ Finset.range (BooleanCube.maximumCost (@complexity n)),
      (BooleanCube.edgeBoundary (@complexity n) threshold).card ≤
        2 * n * 2 ^ n * 2 ^ (2 ^ n - 1) := by
  have bound := BooleanCube.sum_edgeBoundary_le (@complexity n) _ (2 * n)
    (BooleanCube.cost_le_maximumCost complexity) (by
      intro edge member
      have step := complexity_dist_le edge.1 (BooleanCube.edgeEnd edge)
      simpa only [BooleanCube.hammingDist_edgeEnd member, Nat.mul_one] using step)
  simpa [BooleanCube.card_edges, Fintype.card_fun, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using bound

/-- Both endpoints of a crossing edge lie in the `2*n` bands adjoining the threshold. -/
theorem complexity_boundary_band (threshold : Nat)
    {edge : ScalarFunction Bool n × (Fin n → Bool)}
    (member : edge ∈ BooleanCube.edgeBoundary complexity threshold) :
    threshold < min (complexity edge.1) (complexity (BooleanCube.edgeEnd edge)) + 2 * n ∧
      max (complexity edge.1) (complexity (BooleanCube.edgeEnd edge)) ≤ threshold + 2 * n := by
  apply BooleanCube.edgeBoundary_band complexity threshold (2 * n) member
  have step := complexity_dist_le edge.1 (BooleanCube.edgeEnd edge)
  simpa only [BooleanCube.hammingDist_edgeEnd (Finset.mem_filter.mp member).1,
    Nat.mul_one] using step

end Algebraic.DeMorgan
