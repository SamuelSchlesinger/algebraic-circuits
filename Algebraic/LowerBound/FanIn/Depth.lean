import Algebraic.Fin
import Algebraic.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Depth lower bounds from bounded fan-in

At depth `d`, a fan-in-`r` output can depend on at most `r ^ d` inputs.
Essential inputs therefore give a lower bound on circuit depth.
-/

namespace Algebraic

private theorem Line.card_inputSupport_le_depth
    (line : Line σ n g)
    (wireSupport : Wire n g → Finset (Fin n))
    (wireDepths : Wire n g → Nat)
    (r : Nat)
    (positive : 1 ≤ r)
    (arity : σ.Arity line.op ≤ r)
    (wireBound : ∀ wire,
      (wireSupport wire).card ≤ r ^ wireDepths wire) :
    (line.inputSupport wireSupport).card ≤ r ^ line.depth wireDepths := by
  let maxDepth := Fin.foldl (σ.Arity line.op)
    (fun result argument => max result (wireDepths (line.wires argument))) 0
  have argumentBound (argument : Fin (σ.Arity line.op)) :
      (wireSupport (line.wires argument)).card ≤ r ^ maxDepth :=
    (wireBound (line.wires argument)).trans <|
      Nat.pow_le_pow_right (by omega) <|
        Fin.le_foldl_max
          (fun argument => wireDepths (line.wires argument)) 0 argument
  calc
    (line.inputSupport wireSupport).card ≤
        σ.Arity line.op * r ^ maxDepth := by
      simpa [Line.inputSupport] using
        Finset.card_biUnion_le_card_mul
          (Finset.univ : Finset (Fin (σ.Arity line.op)))
          (fun argument => wireSupport (line.wires argument))
          (r ^ maxDepth) (fun argument _ => argumentBound argument)
    _ ≤ r * r ^ maxDepth := Nat.mul_le_mul_right (r ^ maxDepth) arity
    _ = r ^ line.depth wireDepths := by
      simp [Line.depth, maxDepth, Nat.pow_succ, Nat.mul_comm]

private theorem Program.card_gateSupport_le_depth
    (program : Program σ n g)
    (r : Nat)
    (positive : 1 ≤ r)
    (bounded : program.FanInAtMost r)
    (k : Fin g) :
    (program.gateSupport k).card ≤ r ^ program.depths k := by
  induction program with
  | empty => exact Fin.elim0 k
  | @gate g program line ih =>
      obtain ⟨programBounded, lineBounded⟩ := bounded
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [Program.gateSupport, Program.depths, Fin.lastCases_last]
        let wireSupport : Wire n g → Finset (Fin n) :=
          Fin.addCases (fun k => {k}) program.gateSupport
        let wireDepths : Wire n g → Nat :=
          Fin.addCases (fun _ => 0) program.depths
        apply line.card_inputSupport_le_depth wireSupport wireDepths r positive
          lineBounded
        intro wire
        refine Fin.addCases ?_ ?_ wire
        · intro i
          simp [wireSupport, wireDepths]
        · intro j
          simpa [wireSupport, wireDepths] using ih programBounded j
      · simp only [Program.gateSupport, Program.depths, Fin.lastCases_castSucc]
        exact ih programBounded j

private theorem Circuit.card_inputSupport_le_depth_of_pos
    (c : Circuit σ n g m)
    (r : Nat)
    (positive : 1 ≤ r)
    (bounded : c.FanInAtMost r) :
    c.inputSupport.card ≤ m * r ^ c.depth := by
  obtain ⟨programBounded, outputsBounded⟩ := bounded
  have outputBound (output : Fin m) :
      (c.outputSupport output).card ≤ r ^ c.outputDepths output := by
    let line := c.outputs output
    let wireSupport : Wire n g → Finset (Fin n) := c.program.wireSupport
    let wireDepths : Wire n g → Nat := c.program.wireDepths
    change (line.inputSupport wireSupport).card ≤ r ^ line.depth wireDepths
    apply line.card_inputSupport_le_depth wireSupport wireDepths r positive
      (outputsBounded output)
    intro wire
    refine Fin.addCases ?_ ?_ wire
    · intro i
      simp [wireSupport, wireDepths, Program.wireDepths]
    · intro j
      simpa [wireSupport, wireDepths, Program.wireSupport,
        Program.wireDepths] using
        c.program.card_gateSupport_le_depth r positive programBounded j
  have supportBound := Finset.card_biUnion_le_card_mul
    (Finset.univ : Finset (Fin m)) c.outputSupport (r ^ c.depth)
    (fun output _ => (outputBound output).trans <|
      Nat.pow_le_pow_right (by omega) (Fin.le_foldl_max c.outputDepths 0 output))
  simpa [Circuit.inputSupport] using supportBound

/-- A fan-in-`r` circuit has at most `m * r ^ c.depth` supporting inputs. -/
theorem Circuit.card_inputSupport_le_depth
    (c : Circuit σ n g m)
    {r : Nat}
    (bounded : c.FanInAtMost r) :
    c.inputSupport.card ≤ m * r ^ c.depth := by
  by_cases positive : 1 ≤ r
  · exact c.card_inputSupport_le_depth_of_pos r positive bounded
  · have zero : r = 0 := by omega
    subst r
    rw [c.inputSupport_eq_empty_of_fanIn_zero bounded]
    simp

/-- If a circuit has fan-in at most `r`, computes `target`, and every input in
`selected` is essential to `target`, then `selected` has at most
`m * r ^ c.depth` elements. -/
theorem Circuit.essential_le_depth
    (c : Circuit σ n g m)
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    {selected : Finset (Fin n)}
    {r : Nat}
    (computes : c.Computes interpretation target)
    (essential : ∀ k ∈ selected, EssentialAt target k)
    (bounded : c.FanInAtMost r) :
    selected.card ≤ m * r ^ c.depth := by
  have targetDepends := computes.dependsOnlyOn
  exact (Finset.card_le_card fun k hk =>
    (essential k hk).mem_support targetDepends).trans
      (c.card_inputSupport_le_depth bounded)

end Algebraic
