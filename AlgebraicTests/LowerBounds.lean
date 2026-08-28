import Algebraic.Applications
import Algebraic.LowerBound.Fusion
import AlgebraicTests.Circuit

/-!
# Lower-bound API regressions

These tests apply one public endpoint from each lower-bound branch: bounded
fan-in support bounds, the sharp Shannon theorem, De Morgan gate elimination,
exact cyclic Fusion completeness, the middle-layer rectangle-cover tradeoff,
homomorphic transport, crown-graph collision, and the exponential monotone
CLIQUE lower bound.
-/

namespace AlgebraicTests.LowerBounds

open Algebraic
open Algebraic.Fusion
open Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant

private theorem sharedFanInTwo :
    Circuit.sharedCircuit.FanInAtMost 2 := by
  decide

example :
    Circuit.sharedCircuit.inputSupport.card ≤
      3 * (max 1 2) ^ Circuit.sharedCircuit.depth :=
  Applications.card_inputSupport_le_depth
    Circuit.sharedCircuit sharedFanInTwo

example :
    Circuit.sharedCircuit.inputSupport.card ≤
      3 + (2 - 1) * Circuit.sharedCircuit.size :=
  Applications.card_inputSupport_le_size
    Circuit.sharedCircuit sharedFanInTwo

example {n g : Nat}
    (circuit : Algebraic.Circuit DeMorgan.signature n g 1)
    (computes : circuit.Computes DeMorgan.interpretation
      (GateElimination.Xor.parityTarget n)) :
    3 * (n - 1) ≤ circuit.cost DeMorgan.binaryCost :=
  Applications.xor_lowerBound circuit computes

example {σ : Signature} {U : Type}
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {r m : Nat}
    (maximum : σ.HasMaximumArity r)
    (universeNontrivial : 2 ≤ Fintype.card U)
    (arityAtLeastTwo : 2 ≤ r)
    (outputsPositive : 0 < m) :
    Algebraic.Circuit.AsymptoticallyAlmostAllHard
      interpretation m
      (Algebraic.Circuit.fullFamily U m)
      (Applications.gateBudget (Fintype.card U) r m) :=
  Applications.asymptoticallyAlmostAllHard_shannon interpretation
    maximum universeNontrivial arityAtLeastTwo outputsPositive

example {Γ : Type}
    (problem : SetProblem Γ)
    [Finite Γ]
    (generatorsCover : problem.GeneratorsCover) :
    pairCoverComplexity problem SemifilterClass.all =
      andOrCyclicComplexity problem :=
  Applications.pairCoverComplexity_eq_andOrCyclicComplexity
    problem generatorsCover

example {K C : Type}
    [Field K] [CharZero K]
    (constant : C → K)
    (n : Nat)
    (nBig : 4 ≤ n)
    (coverBudget : Nat)
    (circuit : Algebraic.Circuit
      (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (Rectangular.problem K (2 * n)).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (covered : Rectangular.Cover.Occurrence.AtOccurrences constant
      (2 * n) n circuit (fun _ ↦ coverBudget)) :
    4 ^ n < n *
      (circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        coverBudget) :=
  Rectangular.Cover.Exponential.four_pow_lt_n_mul_cost_mul_coverBudget
    constant n nBig coverBudget circuit constructs covered

example {σ : Signature} {U₁ U₂ : Type}
    {i₁ : Interpretation σ U₁} {i₂ : Interpretation σ U₂}
    {operationCost : OperationCost σ}
    {problem : Fusion.Problem U₁}
    (h : Homomorphism i₁ i₂)
    {model : Fusion.Model operationCost i₂ (problem.map h.map)}
    (framework : Fusion.Framework model)
    (circuit : Algebraic.Circuit σ problem.inputCount g 1)
    (constructs : problem.Constructs circuit i₁) :
    framework.bound ≤ circuit.cost operationCost :=
  Fusion.Framework.lowerBound_of_map h framework circuit constructs

example
    (circuit : Algebraic.Circuit AndOr.signature
      ((2 ^ n) + (2 ^ n)) g 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        Fusion.CrownCollision.function assignment) :
    n ≤ circuit.cost AndOr.andCost :=
  Fusion.CrownCollision.and_lowerBound circuit computes

example
    (w : Nat)
    (sixteen_le : 16 ≤ w)
    (circuit : Algebraic.Circuit AndOr.signature
      (Fusion.Clique.edgeCount (w ^ 20)) g 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        Fusion.Clique.function (w ^ 20) (w ^ 4) assignment) :
    w ^ w < circuit.size :=
  Applications.powSelf_lt_circuitSize w sixteen_le circuit computes

end AlgebraicTests.LowerBounds
