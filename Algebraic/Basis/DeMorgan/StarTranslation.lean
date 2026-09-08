import Algebraic.Basis.DeMorgan.StarBirth
import Algebraic.BooleanCube.Translation

/-!
# Circuit-cost control under XOR translation

The two source DAGs are evaluated once each and a four-gate XOR gadget is
appended. The resulting bound applies to whole face-birth profiles, so all
cheap centers have link filtrations close to the constant-center filtration.
-/

namespace Algebraic.DeMorgan

/-- XOR combines two shared circuits with four additional native gates. -/
theorem complexity_xor_le (left right : ScalarFunction Bool n) :
    complexity (fun input => Bool.xor (left input) (right input)) ≤
      complexity left + complexity right + 4 := by
  let operation : Expression 2 := .xor (.input 0) (.input 1)
  let result := operation.circuit.comp
    ((minimumCircuit left).circuit.parallel (minimumCircuit right).circuit)
  have computes : result.Computes interpretation (fun input _ => Bool.xor (left input) (right input)) := by
    intro input
    funext output
    have outputZero : output = 0 := Subsingleton.elim _ _
    rw [outputZero]
    dsimp only [result]
    rw [Circuit.eval_comp, Expression.circuit_eval, Circuit.eval_parallel]
    have l : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (0 : Fin 2) = left input :=
      congrFun ((minimumCircuit left).computes input) 0
    have r : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (1 : Fin 2) = right input :=
      congrFun ((minimumCircuit right).computes input) 0
    simp [operation, Expression.xor_eval, Expression.eval, l, r, Bool.add_eq_xor]
  simpa [result, operation, complexity, Expression.xor, Expression.gateCount] using complexity_le result computes

/-- Translation by a fixed truth table raises vertex complexity by at most its complexity plus four. -/
theorem complexity_translate_le (shift vertex : ScalarFunction Bool n) :
    complexity (BooleanCube.translate shift vertex) ≤ complexity vertex + (complexity shift + 4) := by
  change complexity (fun input => Bool.xor (vertex input) (shift input)) ≤ _
  simpa only [Nat.add_assoc] using complexity_xor_le vertex shift

/-- The same additive overhead controls every face at an arbitrary translated center. -/
theorem faceBirth_translate_le (shift base : ScalarFunction Bool n) (directions : Finset (Fin n → Bool)) :
    BooleanCube.faceBirth complexity (BooleanCube.translate shift base) directions ≤
      BooleanCube.faceBirth complexity base directions + (complexity shift + 4) :=
  BooleanCube.faceBirth_translate_le complexity shift base _ (complexity_translate_le shift) directions

/-- Every center's birth profile differs from the zero-center profile by at most `C(center)+4`. -/
theorem faceBirth_dist_constant_le (center : ScalarFunction Bool n) (directions : Finset (Fin n → Bool)) :
    Nat.dist (BooleanCube.faceBirth complexity center directions) (constantFaceBirth n false directions) ≤
      complexity center + 4 := by
  have forward := faceBirth_translate_le center (fun _ => false) directions
  have backward := faceBirth_translate_le center center directions
  have self : BooleanCube.translate center center = fun _ => false := by
    funext input
    simp [BooleanCube.translate]
  simp only [BooleanCube.translate_zero] at forward
  rw [self] at backward
  change BooleanCube.faceBirth complexity center directions ≤ constantFaceBirth n false directions + _ at forward
  change constantFaceBirth n false directions ≤ BooleanCube.faceBirth complexity center directions + _ at backward
  unfold Nat.dist
  omega

/-- Every constant-link face transfers to a cheap center with the uniform XOR overhead. -/
theorem constantLink_subset_center (center : ScalarFunction Bool n) (budget : Nat) :
    constantLink n budget false ⊆
      BooleanCube.link {f | complexity f ≤ budget + (complexity center + 4)} center := by
  simpa only [constantLink, BooleanCube.translate_zero] using
    BooleanCube.link_subset_translate complexity center (fun _ => false) budget _
    (complexity_translate_le center)

/-- Every face at an arbitrary center transfers back to the constant at the same overhead. -/
theorem centerLink_subset_constant (center : ScalarFunction Bool n) (budget : Nat) :
    BooleanCube.link {f | complexity f ≤ budget} center ⊆
      constantLink n (budget + (complexity center + 4)) false := by
  have self : BooleanCube.translate center center = fun _ => false := by
    funext input
    simp [BooleanCube.translate]
  simpa only [self, constantLink] using BooleanCube.link_subset_translate complexity center center budget _
    (complexity_translate_le center)

end Algebraic.DeMorgan
