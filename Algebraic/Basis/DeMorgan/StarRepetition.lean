import Algebraic.Basis.DeMorgan.StarEncoding
import Algebraic.Basis.DeMorgan.StarSubcube

/-!
# Repetition supports and coordinate embeddings

Duplicating the input uses no gates. Recognizing the duplicated-input image
uses at most `5*m+1` native gates, including the constant at the start of the
conjunction. Thus every Boolean pattern on this support appears by budget
`M(m)+5*m+3`, and the whole face cannot appear before budget `M(m)`.
-/

namespace Algebraic.DeMorgan

/-- Duplicate every input wire, with no internal gates. -/
def repetitionEncoder (m : Nat) : Circuit signature m 0 (m + m) :=
  (Circuit.id signature m).parallel (Circuit.id signature m)

/-- Read the first half of a doubled input, with no internal gates. -/
def repetitionDecoder (m : Nat) : Circuit signature (m + m) 0 m where
  program := .empty
  outputs := fun i => Wire.input (Fin.castAdd m i)

/-- Repetition is exactly concatenation of an input with itself. -/
@[simp] theorem repetitionEncoder_eval (input : Fin m → Bool) :
    (repetitionEncoder m).eval interpretation input = Fin.append input input := by
  simp [repetitionEncoder]

/-- The decoder reads the first block. -/
@[simp] theorem repetitionDecoder_eval (input : Fin (m + m) → Bool) :
    (repetitionDecoder m).eval interpretation input = input ∘ Fin.castAdd m := by
  funext i
  simp [repetitionDecoder, Circuit.eval, Program.trace_input]

/-- Repetition is injective. -/
theorem repetitionEncoder_injective (m : Nat) :
    Function.Injective ((repetitionEncoder m).eval interpretation) := by
  intro left right equal
  funext i
  simpa using congrFun equal (Fin.castAdd m i)

/-- The support consisting of inputs with two equal halves. -/
def repetitionSupport (m : Nat) : Finset (Fin (m + m) → Bool) :=
  encodingSupport ((repetitionEncoder m).eval interpretation)

/-- Repetition supplies one truth-table direction for every smaller input. -/
@[simp] theorem card_repetitionSupport (m : Nat) : (repetitionSupport m).card = 2 ^ m :=
  card_encodingSupport _ (repetitionEncoder_injective m)

/-- Membership is equality between corresponding coordinates in the two blocks. -/
theorem mem_repetitionSupport_iff (input : Fin (m + m) → Bool) :
    input ∈ repetitionSupport m ↔ ∀ i, input (Fin.castAdd m i) = input (Fin.natAdd m i) := by
  constructor
  · rintro member
    obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp member
    rw [repetitionEncoder_eval]
    intro i
    rw [Fin.append_left, Fin.append_right]
  · intro equal
    refine Finset.mem_image.mpr ⟨input ∘ Fin.castAdd m, Finset.mem_univ _, ?_⟩
    rw [repetitionEncoder_eval]
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; rw [Fin.append_right]; exact equal j

private def equalityTerm (i : Fin m) : Expression (m + m) :=
  .or (.and (.input (Fin.castAdd m i)) (.input (Fin.natAdd m i)))
    (.not (.or (.input (Fin.castAdd m i)) (.input (Fin.natAdd m i))))

private theorem equalityTerm_eval (i : Fin m) (input : Fin (m + m) → Bool) :
    (equalityTerm i).eval input = decide (input (Fin.castAdd m i) = input (Fin.natAdd m i)) := by
  simp only [equalityTerm, Expression.eval]
  cases input (Fin.castAdd m i) <;> cases input (Fin.natAdd m i) <;> rfl

private theorem finAnd_gateCount (terms : Fin count → Expression n) :
    (Expression.finAnd count terms).gateCount = 1 + ∑ i, (terms i).gateCount + count := by
  induction count with
  | zero => simp [Expression.finAnd]
  | succ count ih =>
    rw [Expression.finAnd, Expression.gateCount, ih, Fin.sum_univ_castSucc]
    omega

/-- A native circuit recognizing the image of the repetition encoder. -/
def repetitionTester (m : Nat) :
    Circuit signature (m + m) (Expression.finAnd m equalityTerm).gateCount 1 :=
  (Expression.finAnd m equalityTerm).circuit

/-- The repetition membership circuit includes four gates per equality and one per conjunction. -/
theorem repetitionTester_gateCount (m : Nat) :
    (Expression.finAnd m equalityTerm).gateCount = 5 * m + 1 := by
  rw [finAnd_gateCount]
  simp [equalityTerm, Expression.gateCount]
  omega

/-- The tester recognizes precisely the repetition support. -/
@[simp] theorem repetitionTester_eval (input : Fin (m + m) → Bool) :
    (repetitionTester m).eval interpretation input 0 = decide (input ∈ repetitionSupport m) := by
  apply Bool.eq_iff_iff.mpr
  simp [repetitionTester, equalityTerm_eval, Expression.finAndValue_eq_true_iff,
    mem_repetitionSupport_iff]

/-- Repetition preserves the smaller worst-case complexity as a lower bound for full-face birth. -/
theorem maximumComplexity_le_repetition_birth (m : Nat) (value : Bool) :
    maximumComplexity m ≤ constantFaceBirth (m + m) value (repetitionSupport m) := by
  simpa [repetitionSupport] using
    maximumComplexity_le_faceBirth_add_encoder (repetitionEncoder m) (repetitionEncoder_injective m) value

/-- Every exception pattern on the repetition support is available with linear membership overhead. -/
theorem repetition_birth_le (m : Nat) (value : Bool) :
    constantFaceBirth (m + m) value (repetitionSupport m) ≤ maximumComplexity m + 5 * m + 3 := by
  have bound := constantFaceBirth_encodingSupport_le ((repetitionEncoder m).eval interpretation)
    (repetitionDecoder m) (repetitionTester m)
    (by intro input; simp only [repetitionDecoder_eval, repetitionEncoder_eval]; funext i; exact Fin.append_left _ _ i)
    (by intro input; exact repetitionTester_eval input) value
  simpa only [repetitionSupport, repetitionTester_gateCount, Nat.add_zero, Nat.add_assoc] using bound

/-- Append a fixed prefix using two shared constant gates, independently of prefix length. -/
def subcubeEncoder (fixed : Fin k → Bool) (d : Nat) : Circuit signature d 2 (k + d) :=
  (((Expression.constant false : Expression d).circuit.parallel (Expression.constant true).circuit).parallel
    (Circuit.id signature d)).mapOutputs
      (Fin.addCases (fun i => Fin.castAdd d (if fixed i then (1 : Fin 2) else 0)) (Fin.natAdd 2))

/-- The coordinate-subcube encoder prepends the specified constant word. -/
@[simp] theorem subcubeEncoder_eval (fixed : Fin k → Bool) (input : Fin d → Bool) :
    (subcubeEncoder fixed d).eval interpretation input = Fin.append fixed input := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [subcubeEncoder, Circuit.eval_mapOutputs, Circuit.eval_parallel, Circuit.eval_id,
      Function.comp_apply, Fin.addCases_left, Fin.append_left]
    cases fixed j <;> change (Expression.constant _).circuit.eval interpretation input 0 = _ <;>
      rw [Expression.circuit_eval] <;> rfl
  · intro j
    simp [subcubeEncoder]

/-- Restriction to a coordinate subcube costs at most two shared constant gates. -/
theorem maximumComplexity_le_inputSubcube_birth_add_two (fixed : Fin k → Bool) (d : Nat) (value : Bool) :
    maximumComplexity d ≤ constantFaceBirth (k + d) value (inputSubcube fixed d) + 2 := by
  have injective : Function.Injective ((subcubeEncoder fixed d).eval interpretation) := by
    intro left right equal
    funext i
    simpa using congrFun equal (Fin.natAdd k i)
  have bound := maximumComplexity_le_faceBirth_add_encoder (subcubeEncoder fixed d) injective value
  have encoderEq : (subcubeEncoder fixed d).eval interpretation = Fin.append fixed :=
    funext (subcubeEncoder_eval fixed)
  simpa only [encodingSupport, encoderEq, inputSubcube] using bound

end Algebraic.DeMorgan
