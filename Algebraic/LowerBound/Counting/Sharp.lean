import Algebraic.LowerBound.Counting.Normalization
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Factorial-improved Shannon counting

After semantic normalization, all internal gate functions are distinct. Each
computed function can therefore be encoded under all `g!` gate relabelings,
and those encodings are distinct. This removes the artificial topological
ordering from the leading Shannon count.
-/

namespace Algebraic

/-! ## Loose presentations and relabeling -/

/-- A circuit presentation whose internal gates need not be topologically ordered. -/
structure LooseCircuit (σ : Signature) (n g m : Nat) where
  /-- One defining line for every labeled internal gate. -/
  internal : Fin g → Line σ n g
  /-- One terminal line for every output. -/
  outputs : Fin m → Line σ n g

/-- A loose circuit is equivalently a pair of indexed line collections. -/
def looseCircuitEquiv (σ : Signature) (n g m : Nat) :
    LooseCircuit σ n g m ≃
      (Fin g → Line σ n g) × (Fin m → Line σ n g) where
  toFun circuit := (circuit.internal, circuit.outputs)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [Fintype σ.Op] : Fintype (LooseCircuit σ n g m) :=
  Fintype.ofEquiv
    ((Fin g → Line σ n g) × (Fin m → Line σ n g))
    (looseCircuitEquiv σ n g m).symm

/-- Exact count of loose labeled circuit presentations. -/
theorem card_looseCircuit [Fintype σ.Op] :
    Fintype.card (LooseCircuit σ n g m) =
      σ.lineCount (n + g) ^ (g + m) := by
  rw [Fintype.card_congr (looseCircuitEquiv σ n g m), Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin, card_line,
    Signature.lineCount]
  exact (Nat.pow_add _ _ _).symm

/-- A loose circuit valuation solves all of its internal gate equations. -/
def LooseCircuit.Satisfies
    (circuit : LooseCircuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (values : Fin g → U) : Prop :=
  ∀ gate, values gate =
    (circuit.internal gate).eval interpretation input values

/-- Read terminal outputs under a chosen internal-gate valuation. -/
def LooseCircuit.evalOutputs
    (circuit : LooseCircuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (values : Fin g → U) : Fin m → U :=
  fun output => (circuit.outputs output).eval interpretation input values

theorem Wire.value_permutation
    (permutation : Equiv.Perm (Fin g))
    (inputs : Fin n → U)
    (values : Fin g → U)
    (wire : Wire n g) :
    (Fin.addCases inputs (values ∘ permutation.symm) : Wire n g → U)
        (Wire.Renaming.ofPermutation permutation wire) =
      (Fin.addCases inputs values : Wire n g → U) wire := by
  apply Wire.Renaming.value_apply
  intro gate
  simp [Wire.Renaming.ofPermutation, Function.comp_apply]

/-- Forget topological order, then rename every internal gate. -/
def Circuit.relabel
    (circuit : Circuit σ n g m)
    (permutation : Equiv.Perm (Fin g)) : LooseCircuit σ n g m where
  internal := fun gate =>
    (circuit.program.lines (permutation.symm gate)).mapWires
      (Wire.Renaming.ofPermutation permutation)
  outputs := fun output =>
    (circuit.outputs output).mapWires
      (Wire.Renaming.ofPermutation permutation)

theorem Circuit.relabel_satisfies
    (circuit : Circuit σ n g m)
    (permutation : Equiv.Perm (Fin g))
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (circuit.relabel permutation).Satisfies interpretation input
      (circuit.program.eval interpretation input ∘ permutation.symm) := by
  intro gate
  unfold Circuit.relabel
  simp only [Function.comp_apply]
  rw [Line.eval_mapWires]
  · exact (circuit.program.lines_eval interpretation input
      (permutation.symm gate)).symm
  · intro wire
    exact Wire.value_permutation permutation input
      (circuit.program.eval interpretation input) wire

theorem Circuit.relabel_evalOutputs
    (circuit : Circuit σ n g m)
    (permutation : Equiv.Perm (Fin g))
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (circuit.relabel permutation).evalOutputs interpretation input
        (circuit.program.eval interpretation input ∘ permutation.symm) =
      circuit.eval interpretation input := by
  funext output
  unfold Circuit.relabel LooseCircuit.evalOutputs Circuit.eval
  apply Line.eval_mapWires
  intro wire
  exact Wire.value_permutation permutation input
    (circuit.program.eval interpretation input) wire

/-! ## Acyclicity and unique valuations -/

/-- Inputs are always available; a gate wire is below a numeric rank bound. -/
def Wire.Below
    (rank : Fin g → Nat)
    (bound : Nat)
    (wire : Wire n g) : Prop :=
  Fin.addCases (fun _ => True) (fun gate => rank gate < bound) wire

theorem Wire.below_castSucc
    (wire : Wire n g)
    (gate : Fin g) :
    Wire.Below (fun gate : Fin (g + 1) => gate.val) gate.castSucc.val
        wire.castSucc ↔
      Wire.Below (fun gate : Fin g => gate.val) gate.val wire := by
  refine Fin.addCases (fun input => ?_) (fun priorGate => ?_) wire
  · simp [Wire.Below, Fin.castSucc_castAdd]
  · simp [Wire.Below]

theorem Wire.below_last
    (wire : Wire n g) :
    Wire.Below (fun gate : Fin (g + 1) => gate.val) (Fin.last g).val
      wire.castSucc := by
  refine Fin.addCases (fun input => ?_) (fun priorGate => ?_) wire
  · simp [Wire.Below, Fin.castSucc_castAdd]
  · simp [Wire.Below]

theorem Program.lines_below
    (program : Program σ n g)
    (gate : Fin g)
    (argument : Fin (σ.Arity (program.lines gate).op)) :
    Wire.Below (fun gate : Fin g => gate.val) gate.val
      ((program.lines gate).wires argument) := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate g program line ih =>
      revert argument
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · rw [Program.lines_gate_last]
        intro argument
        change Wire.Below (fun gate : Fin (g + 1) => gate.val)
          (Fin.last g).val
          (Wire.Renaming.castSucc (line.wires argument))
        rw [Wire.Renaming.castSucc_apply]
        exact Wire.below_last (line.wires argument)
      · rw [Program.lines_gate_castSucc]
        intro argument
        change Wire.Below (fun gate : Fin (g + 1) => gate.val)
          priorGate.castSucc.val
          (Wire.Renaming.castSucc
            ((program.lines priorGate).wires argument))
        rw [Wire.Renaming.castSucc_apply, Wire.below_castSucc]
        exact ih priorGate argument

/-- A rank strictly decreases along every internal gate dependency. -/
def LooseCircuit.AcyclicUnder
    (circuit : LooseCircuit σ n g m)
    (rank : Fin g → Nat) : Prop :=
  ∀ gate argument,
    Wire.Below rank (rank gate) ((circuit.internal gate).wires argument)

theorem Wire.below_permutation
    (permutation : Equiv.Perm (Fin g))
    (gate : Fin g)
    (wire : Wire n g) :
    Wire.Below (fun renamed => (permutation.symm renamed).val)
        (permutation.symm gate).val
        (Wire.Renaming.ofPermutation permutation wire) ↔
      Wire.Below (fun original : Fin g => original.val)
        (permutation.symm gate).val wire := by
  refine Fin.addCases (fun input => ?_) (fun original => ?_) wire
  · simp [Wire.Below, Wire.Renaming.ofPermutation,
      Wire.Renaming.apply]
  · simp [Wire.Below, Wire.Renaming.ofPermutation,
      Wire.Renaming.apply]

theorem Circuit.relabel_acyclic
    (circuit : Circuit σ n g m)
    (permutation : Equiv.Perm (Fin g)) :
    (circuit.relabel permutation).AcyclicUnder
      (fun gate => (permutation.symm gate).val) := by
  intro gate
  change ∀ argument : Fin
      (σ.Arity (circuit.program.lines (permutation.symm gate)).op), _
  intro argument
  change Wire.Below (fun gate => (permutation.symm gate).val)
    (permutation.symm gate).val
    (Wire.Renaming.ofPermutation permutation
      ((circuit.program.lines (permutation.symm gate)).wires argument))
  rw [Wire.below_permutation]
  exact circuit.program.lines_below (permutation.symm gate) argument

theorem Wire.values_eq_of_below
    (rank : Fin g → Nat)
    (bound : Nat)
    (wire : Wire n g)
    (below : wire.Below rank bound)
    (inputs : Fin n → U)
    (left right : Fin g → U)
    (agree : ∀ gate, rank gate < bound → left gate = right gate) :
    (Fin.addCases inputs left : Wire n g → U) wire =
      (Fin.addCases inputs right : Wire n g → U) wire := by
  revert below
  refine Fin.addCases (fun originalInput _ => ?_)
    (fun dependency below => ?_) wire
  · simp
  · simpa using agree dependency (by simpa [Wire.Below] using below)

/-- An acyclic loose presentation has at most one solution to its gate equations. -/
theorem LooseCircuit.satisfies_unique
    (circuit : LooseCircuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (rank : Fin g → Nat)
    (acyclic : circuit.AcyclicUnder rank)
    {left right : Fin g → U}
    (leftSatisfies : circuit.Satisfies interpretation input left)
    (rightSatisfies : circuit.Satisfies interpretation input right) :
    left = right := by
  have agreeBelow : ∀ bound, ∀ gate,
      rank gate < bound → left gate = right gate := by
    intro bound
    induction bound with
    | zero =>
        intro gate impossible
        omega
    | succ bound ih =>
        intro gate gateBelow
        calc
          left gate =
              (circuit.internal gate).eval interpretation input left :=
            leftSatisfies gate
          _ = (circuit.internal gate).eval interpretation input right := by
            unfold Line.eval
            congr 1
            funext argument
            let wire := (circuit.internal gate).wires argument
            have below := acyclic gate argument
            exact Wire.values_eq_of_below rank (rank gate) wire
              (by simpa [wire] using below) input left right fun dependency lower =>
                ih dependency <|
                  Nat.lt_of_lt_of_le lower (Nat.le_of_lt_succ gateBelow)
          _ = right gate := (rightSatisfies gate).symm
  funext gate
  exact agreeBelow (rank gate + 1) gate (Nat.lt_succ_self _)

/-! ## The factorial encoding -/

/-- A target together with evidence that an irredundant `g`-gate circuit
computes it. -/
abbrev Circuit.IrredundantTarget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n g m : Nat) :=
  { target : Target U n m //
    target ∈ Circuit.irredundantFunctions interpretation n g m }

/-- Choose one irredundant representative circuit for a target. -/
noncomputable def Circuit.irredundantRepresentative
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m) :
    Circuit σ n g m :=
  Classical.choose
    (Circuit.mem_irredundantFunctions_iff.mp target.property)

theorem Circuit.irredundantRepresentative_irredundant
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m) :
    (Circuit.irredundantRepresentative interpretation target).Irredundant
      interpretation :=
  (Classical.choose_spec
    (Circuit.mem_irredundantFunctions_iff.mp target.property)).1

theorem Circuit.irredundantRepresentative_eval
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m) :
    (Circuit.irredundantRepresentative interpretation target).eval interpretation =
      target.val :=
  (Classical.choose_spec
    (Circuit.mem_irredundantFunctions_iff.mp target.property)).2

/-- Encode one chosen irredundant circuit for a function under a gate renaming. -/
noncomputable def Circuit.sharpEncoding
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) :
    Circuit.IrredundantTarget interpretation n g m × Equiv.Perm (Fin g) →
      LooseCircuit σ n g m :=
    fun pair =>
      (Circuit.irredundantRepresentative interpretation pair.1).relabel pair.2

/-- The target fixes the unique acyclic valuation of an encoded presentation;
irredundancy then makes its gate permutation recoverable. -/
theorem Circuit.sharpEncoding_injective
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) :
    Function.Injective (Circuit.sharpEncoding (n := n) (g := g) (m := m)
      interpretation) := by
  classical
  rintro ⟨leftTarget, leftPermutation⟩ ⟨rightTarget, rightPermutation⟩ encodedEqual
  let leftCircuit := Circuit.irredundantRepresentative interpretation leftTarget
  let rightCircuit := Circuit.irredundantRepresentative interpretation rightTarget
  have relabelEqual :
      leftCircuit.relabel leftPermutation =
        rightCircuit.relabel rightPermutation := by
    simpa only [Circuit.sharpEncoding, leftCircuit, rightCircuit] using encodedEqual
  have valuationEqual (input : Fin n → U) :
      leftCircuit.program.eval interpretation input ∘ leftPermutation.symm =
        rightCircuit.program.eval interpretation input ∘ rightPermutation.symm := by
    apply LooseCircuit.satisfies_unique
      (leftCircuit.relabel leftPermutation) interpretation input
      (fun gate => (leftPermutation.symm gate).val)
      (leftCircuit.relabel_acyclic leftPermutation)
      (leftCircuit.relabel_satisfies leftPermutation interpretation input)
    rw [relabelEqual]
    exact rightCircuit.relabel_satisfies rightPermutation interpretation input
  have circuitEvalEqual :
      leftCircuit.eval interpretation = rightCircuit.eval interpretation := by
    funext input
    rw [← leftCircuit.relabel_evalOutputs leftPermutation interpretation input,
      ← rightCircuit.relabel_evalOutputs rightPermutation interpretation input,
      relabelEqual, valuationEqual input]
  have targetValueEqual : leftTarget.val = rightTarget.val := by
    calc
      leftTarget.val = leftCircuit.eval interpretation :=
        (Circuit.irredundantRepresentative_eval interpretation leftTarget).symm
      _ = rightCircuit.eval interpretation := circuitEvalEqual
      _ = rightTarget.val :=
        Circuit.irredundantRepresentative_eval interpretation rightTarget
  have targetEqual : leftTarget = rightTarget := Subtype.ext targetValueEqual
  subst rightTarget
  have permutationEqual : leftPermutation = rightPermutation := by
    apply Equiv.ext
    intro gate
    have gateFunctionsEqual :
        leftCircuit.program.gateFunction interpretation gate =
          leftCircuit.program.gateFunction interpretation
            (rightPermutation.symm (leftPermutation gate)) := by
      funext input
      have atRenamedGate := congrFun (valuationEqual input) (leftPermutation gate)
      simpa only [leftCircuit, rightCircuit, Function.comp_apply,
        Equiv.symm_apply_apply, Program.gateFunction] using atRenamedGate
    have gateEqual :=
      Circuit.irredundantRepresentative_irredundant interpretation leftTarget
        gateFunctionsEqual
    have renamedEqual := congrArg rightPermutation gateEqual
    simpa using renamedEqual.symm
  subst rightPermutation
  rfl

/-! ## Counting consequences -/

/-- Sharp fixed-size Shannon count, including the full `g!` relabeling gain. -/
theorem Circuit.card_irredundantFunctions_mul_factorial_le
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n g m : Nat) :
    (Circuit.irredundantFunctions interpretation n g m).card * g.factorial ≤
      σ.lineCount (n + g) ^ (g + m) := by
  classical
  have encoded := Fintype.card_le_of_injective
    (Circuit.sharpEncoding (n := n) (g := g) (m := m) interpretation)
    (Circuit.sharpEncoding_injective (n := n) (g := g) (m := m)
      interpretation)
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    card_looseCircuit] at encoded
  simpa only [Fintype.card_coe] using encoded

/-- Sharp number of possible functions at exactly `g` internal gates. -/
def Signature.sharpCount
    (σ : Signature) [Fintype σ.Op]
    (n g m : Nat) : Nat :=
  σ.lineCount (n + g) ^ (g + m) / g.factorial

theorem Circuit.card_irredundantFunctions_le_sharpCount
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n g m : Nat) :
    (Circuit.irredundantFunctions interpretation n g m).card ≤
      σ.sharpCount n g m := by
  apply (Nat.le_div_iff_mul_le (Nat.factorial_pos g)).2
  exact Circuit.card_irredundantFunctions_mul_factorial_le
    interpretation n g m

/-- Sharp Shannon budget for all circuits with at most `G` internal gates. -/
def Signature.sharpBudget
    (σ : Signature) [Fintype σ.Op]
    (n m G : Nat) : Nat :=
  ∑ g ∈ Finset.range (G + 1), σ.sharpCount n g m

theorem Circuit.card_functionsAtMost_le_sharpBudget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m G : Nat) :
    (Circuit.functionsAtMost interpretation n m G).card ≤
      σ.sharpBudget n m G := by
  refine (Circuit.card_functionsAtMost_le_sum_irredundant
    interpretation n m G).trans ?_
  unfold Signature.sharpBudget
  exact Finset.sum_le_sum fun g _ =>
    Circuit.card_irredundantFunctions_le_sharpCount interpretation n g m

/-- A family larger than the sharp budget contains a size-hard function. -/
theorem Circuit.exists_hard_in_family_sharp
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (large : σ.sharpBudget n m G < family.card) :
    ∃ target ∈ family,
      ∀ g ≤ G, ∀ circuit : Circuit σ n g m,
        ¬circuit.Computes interpretation target := by
  apply Circuit.exists_hard_in_family_of_card_lt interpretation family
  exact (Circuit.card_functionsAtMost_le_sharpBudget
    interpretation n m G).trans_lt large

/-- Full-universe sharp Shannon lower bound. -/
theorem Circuit.exists_hard_sharp
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (large :
      σ.sharpBudget n m G <
        Fintype.card U ^ (m * Fintype.card U ^ n)) :
    ∃ target : Target U n m,
      ∀ g ≤ G, ∀ circuit : Circuit σ n g m,
        ¬circuit.Computes interpretation target := by
  apply Circuit.exists_hard_of_card_lt interpretation
  exact (Circuit.card_functionsAtMost_le_sharpBudget
    interpretation n m G).trans_lt large

/-- Under functional completeness, a target outside the sharp budget is both
hard below `G` and computable at some finite size. -/
theorem Circuit.exists_hard_sharp_of_complete
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (complete : interpretation.FunctionallyComplete)
    (large :
      σ.sharpBudget n m G <
        Fintype.card U ^ (m * Fintype.card U ^ n)) :
    ∃ target : Target U n m,
      (∀ g ≤ G, ∀ circuit : Circuit σ n g m,
        ¬circuit.Computes interpretation target) ∧
      ∃ g, ∃ circuit : Circuit σ n g m,
        circuit.Computes interpretation target := by
  obtain ⟨target, hard⟩ := Circuit.exists_hard_sharp interpretation large
  exact ⟨target, hard, complete n m target⟩

/-- Boolean specialization of the sharp Shannon theorem. -/
theorem Circuit.exists_boolean_hard_sharp
    [Fintype σ.Op]
    (interpretation : Interpretation σ Bool)
    (large : σ.sharpBudget n m G < 2 ^ (m * 2 ^ n)) :
    ∃ target : Target Bool n m,
      ∀ g ≤ G, ∀ circuit : Circuit σ n g m,
        ¬circuit.Computes interpretation target := by
  simpa using Circuit.exists_hard_sharp interpretation large

end Algebraic
