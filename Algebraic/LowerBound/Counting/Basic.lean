import Algebraic.Counting.Syntax
import Algebraic.Semantics

/-!
# Shannon counting bounds

Exact ordered-syntax counts are converted here into semantic bounds for an
arbitrary finite interpretation and an arbitrary finite family of targets.
-/

namespace Algebraic

/-- A circuit with a gate count chosen from `0, ..., G`. -/
abbrev BoundedCircuit (σ : Signature) (n m G : Nat) :=
  Σ g : Fin (G + 1), Circuit σ n g m

/-- Evaluate a circuit whose internal gate count is bounded by `G`. -/
def BoundedCircuit.eval
    (circuit : BoundedCircuit σ n m G)
    (interpretation : Interpretation σ U) : Target U n m :=
  circuit.2.eval interpretation

/-- Functions computed by circuits with at most `G` internal gates. -/
noncomputable def Circuit.functionsAtMost
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m G : Nat) : Finset (Target U n m) := by
  classical
  exact Finset.univ.image fun circuit : BoundedCircuit σ n m G =>
    circuit.eval interpretation

/-- Number of topologically ordered circuit descriptions with at most `G`
internal gates. -/
def Signature.orderedBudget
    (σ : Signature) [Fintype σ.Op]
    (n m G : Nat) : Nat :=
  ∑ g ∈ Finset.range (G + 1),
    (∏ j ∈ Finset.range g, σ.lineCount (n + j)) *
      (n + g) ^ m

theorem Circuit.mem_functionsAtMost_iff
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {target : Target U n m} :
    target ∈ Circuit.functionsAtMost interpretation n m G ↔
      ∃ g ≤ G, ∃ circuit : Circuit σ n g m,
        circuit.Computes interpretation target := by
  classical
  constructor
  · intro present
    rw [Circuit.functionsAtMost, Finset.mem_image] at present
    obtain ⟨circuit, _, equal⟩ := present
    exact ⟨circuit.1, Nat.le_of_lt_succ circuit.1.isLt, circuit.2,
      fun input => by
        simpa [BoundedCircuit.eval] using congrFun equal input⟩
  · rintro ⟨g, bounded, circuit, computes⟩
    rw [Circuit.functionsAtMost, Finset.mem_image]
    let index : Fin (G + 1) := ⟨g, Nat.lt_succ_iff.mpr bounded⟩
    refine ⟨⟨index, circuit⟩, Finset.mem_univ _, ?_⟩
    simpa [BoundedCircuit.eval] using computes.eval_eq

/-- Being absent from the easy-function set is exactly gate hardness at the
corresponding budget. -/
theorem Circuit.not_mem_functionsAtMost_iff
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {target : Target U n m} :
    target ∉ Circuit.functionsAtMost interpretation n m G ↔
      Circuit.GateHard interpretation G target := by
  simpa [Circuit.GateHard] using not_congr
    (Circuit.mem_functionsAtMost_iff
      (interpretation := interpretation) (target := target) (G := G))

/-- Exact number of ordered circuits with at most `G` internal gates. -/
theorem BoundedCircuit.card [Fintype σ.Op] :
    Fintype.card (BoundedCircuit σ n m G) =
      σ.orderedBudget n m G := by
  unfold Signature.orderedBudget Signature.lineCount
  rw [Fintype.card_sigma]
  simp_rw [card_circuit]
  exact Fin.sum_univ_eq_sum_range
    (fun g : Nat =>
      (∏ j ∈ Finset.range g,
        ∑ op : σ.Op, (n + j) ^ σ.Arity op) *
      (n + g) ^ m)
    (G + 1)

/-- Semantic functions are no more numerous than their ordered descriptions. -/
theorem Circuit.card_functionsAtMost_le
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) :
    (Circuit.functionsAtMost interpretation n m G).card ≤
      σ.orderedBudget n m G := by
  classical
  exact Finset.card_image_le.trans_eq BoundedCircuit.card

/-- Any family larger than the set of functions available within budget contains
a target outside that budget. -/
theorem Circuit.exists_hard_in_family_of_card_lt
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (large :
      (Circuit.functionsAtMost interpretation n m G).card < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target := by
  classical
  obtain ⟨target, inFamily, notComputable⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card large
  exact ⟨target, inFamily,
    Circuit.not_mem_functionsAtMost_iff.mp notComputable⟩

/-- If the easy functions do not fill the whole target space, some target lies
outside the gate budget. -/
theorem Circuit.exists_hard_of_card_lt
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (small :
      (Circuit.functionsAtMost interpretation n m G).card <
        Target.count U n m) :
    ∃ target : Target U n m,
      Circuit.GateHard interpretation G target := by
  classical
  have targetCard : Fintype.card (Target U n m) =
      Target.count U n m := by
    rw [Target.count, Nat.card_eq_fintype_card]
  obtain ⟨target, _, hard⟩ := Circuit.exists_hard_in_family_of_card_lt
    (G := G) interpretation (Finset.univ : Finset (Target U n m))
    (by simpa only [Finset.card_univ, targetCard] using small)
  exact ⟨target, hard⟩

/-- A family larger than the ordered-syntax budget contains a hard target. -/
theorem Circuit.exists_hard_in_family
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (large : σ.orderedBudget n m G < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_in_family_of_card_lt interpretation family
  exact (Circuit.card_functionsAtMost_le interpretation).trans_lt large

end Algebraic
