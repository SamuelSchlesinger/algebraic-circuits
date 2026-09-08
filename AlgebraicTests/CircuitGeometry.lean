import Algebraic.CircuitGeometry

/-!
# Circuit geometry public API regressions

The examples check exact gate counts, zero-dimensional conventions,
canonical edge counting, budgeted simple paths, the distinction between
filled cube faces and convex hulls, and actual singular homology maps.
-/

namespace AlgebraicTests.CircuitGeometry

open Algebraic

/-- The numerical threshold `101` compiles to two binary gates. -/
example : (DeMorgan.thresholdExpression 3 5).gateCount = 2 := by decide

/-- Threshold endpoints still count the constant gate. -/
example : (DeMorgan.thresholdExpression 0 0).gateCount = 1 := rfl

/-- Every threshold, including values beyond the truth table, has the advertised semantics. -/
example (threshold : Nat) (input : Fin 4 → Bool) :
    (DeMorgan.thresholdExpression 4 threshold).eval input =
      decide (threshold ≤ DeMorgan.inputRank input) :=
  DeMorgan.thresholdExpression_eval threshold input

/-- The empty coordinate cube has no edges. -/
example : (BooleanCube.edges (ι := Fin 0)).card = 0 := by
  simp [BooleanCube.card_edges]

/-- The two-coordinate square has four unoriented edges. -/
example : (BooleanCube.edges (ι := Fin 2)).card = 4 := by
  norm_num [BooleanCube.card_edges]

/-- Erasure costs the input width, independently of the erased prefix length. -/
example (function : ScalarFunction Bool 5) (threshold : Nat) :
    DeMorgan.complexity (BooleanCube.erase DeMorgan.inputRank threshold function) ≤
      DeMorgan.complexity function + 5 :=
  DeMorgan.complexity_erase_le (by decide) function threshold

/-- Old vertices join in the enlarged budget by paths without repeated vertices. -/
example (left right : ScalarFunction Bool 3) (budget : Nat)
    (hl : DeMorgan.complexity left ≤ budget) (hr : DeMorgan.complexity right ≤ budget) :
    ∃ path : BooleanCube.graph.Walk left right,
      path.IsPath ∧ BooleanCube.Within DeMorgan.complexity (budget + 3) path :=
  DeMorgan.exists_connecting_path_of_complexity_le (by decide) left right budget hl hr

/-- The larger budget attains ambient Hamming distance exactly. -/
example (left right : ScalarFunction Bool 3) (budget : Nat)
    (hl : DeMorgan.complexity left ≤ budget) (hr : DeMorgan.complexity right ≤ budget) :
    ∃ path : BooleanCube.graph.Walk left right,
      path.IsPath ∧ BooleanCube.Within DeMorgan.complexity (2 * budget + 4) path ∧
        path.length = hammingDist left right := by
  simpa [Nat.add_assoc] using
    DeMorgan.exists_geodesic_of_complexity_le (by decide) left right budget hl hr

/-- A square with a missing corner does not acquire its interior by convexification. -/
example : (fun _ : Fin 2 => (1 / 2 : Real)) ∉
    BooleanCube.cubical {vertex | ¬(vertex 0 = true ∧ vertex 1 = true)} := by
  intro member
  have contradiction := member.2 (fun _ => true) (by
    intro i
    constructor <;> intro equal <;> norm_num at equal)
  exact contradiction ⟨rfl, rfl⟩

/-- Once all corners are present the square interior is included. -/
example : (fun _ : Fin 2 => (1 / 2 : Real)) ∈ BooleanCube.cubical Set.univ := by
  constructor
  · intro i
    norm_num
  · intro vertex _
    trivial

/-- The generic contraction includes the zero-coordinate cube. -/
example : (BooleanCube.inclusion (fun _ : Fin 0 → Bool => 0) 0 0).Nullhomotopic := by
  apply BooleanCube.inclusion_nullhomotopic (fun _ : Fin 0 => 0)
    (fun _ _ _ => Subsingleton.elim _ _) 0 (fun i => Fin.elim0 i)
  · intros
    rfl
  · rfl

/-- The contraction is a continuous-map theorem on the actual cubical sublevels. -/
example (budget : Nat) :
    (BooleanCube.inclusion (@DeMorgan.complexity 4) budget 4).Nullhomotopic :=
  DeMorgan.sublevel_inclusion_nullhomotopic (by decide) budget

/-- Coarea specializes without an assumed circuit-size upper bound. -/
example (n : Nat) :
    ∑ s ∈ Finset.range (BooleanCube.maximumCost (@DeMorgan.complexity n)),
      (BooleanCube.edgeBoundary (@DeMorgan.complexity n) s).card ≤
        2 * n * 2 ^ n * 2 ^ (2 ^ n - 1) :=
  DeMorgan.complexity_totalBoundary_le n

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

/-- Positive-degree persistence maps vanish for arbitrary admissible coefficients. -/
example {C : Type} [Category C] [Preadditive C] [HasCoproducts.{0} C]
    [CategoryWithHomology C] (coefficients : C) (budget degree : Nat) (nonzero : degree ≠ 0) :
    ((singularHomologyFunctor C degree).obj coefficients).map
      (TopCat.ofHom (BooleanCube.inclusion (@DeMorgan.complexity 3) budget 3)) = 0 :=
  DeMorgan.sublevel_homologyMap_eq_zero (by decide) budget coefficients degree nonzero

end AlgebraicTests.CircuitGeometry

/- Check every declaration owned by the new library modules, including private
helpers and generated declarations, against Lean's ordinary logical axioms. -/
set_option maxHeartbeats 2000000 in
run_cmd do
  let environment ← Lean.getEnv
  let modules : Array Lean.Name := #[
    `Algebraic.BooleanCube.Sweep, `Algebraic.BooleanCube.Boundary,
    `Algebraic.BooleanCube.Cubical, `Algebraic.BooleanCube.Homology,
    `Algebraic.Basis.DeMorgan.Threshold, `Algebraic.Basis.DeMorgan.Geometry,
    `Algebraic.Basis.DeMorgan.Boundary, `Algebraic.Basis.DeMorgan.Topology,
    `Algebraic.Basis.DeMorgan.Homology,
    `Algebraic.BooleanCube.Face, `Algebraic.BooleanCube.Chains,
    `Algebraic.BooleanCube.ChainSupport, `Algebraic.BooleanCube.Betti,
    `Algebraic.BooleanCube.RelativeRank, `Algebraic.BooleanCube.FaceRealization,
    `Algebraic.Basis.DeMorgan.Betti]
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index]! then
        checked := checked + 1
        for dependency in ← Lean.collectAxioms name do
          unless allowed.contains dependency do
            throwError "Circuit geometry declaration {name} depends on forbidden axiom {dependency}"
  if checked = 0 then
    throwError "Circuit geometry axiom audit did not find any declarations"
  Lean.logInfo m!"Circuit geometry axiom audit passed for {checked} declarations."
