import Algebraic.LowerBound.AC0.CanonicalDecisionTree
import Algebraic.LowerBound.AC0.Switching.Encoding

/-!
# Canonical switching-path advice

This module turns a typed canonical DNF path trace into the local data used by
the switching-lemma injection. Each query is annotated with

* its position in the selected source term,
* whether it closes the current term block,
* the original path bit, and
* the value satisfying that source literal.

Only the first three fields become finite advice. The queried coordinate and
satisfying value remain internal witnesses used to define the output
restriction and prove reconstruction. No paths or circuits are enumerated.
-/

namespace Algebraic
namespace AC0
namespace Switching

/-- One symbol of switching advice. The position names a variable within the
currently selected source term. -/
structure QueryAdvice (widthBound : Nat) where
  /-- Zero-based position in the selected source term's ordered support. -/
  position : Fin widthBound
  /-- Whether this query is the last one in the current source-term block. -/
  closesBlock : Bool
  /-- Branch bit followed by the original canonical path. -/
  pathValue : Bool
  deriving DecidableEq, Fintype

/-- Fixed-length switching advice. -/
abbrev Advice (widthBound pathLength : Nat) :=
  Fin pathLength → QueryAdvice widthBound

/-- Internal annotation of one canonical query. The source term, coordinate,
and satisfying value are deliberately not part of the finite advice. -/
structure QueryRecord (n widthBound : Nat) where
  /-- Source term selected for this block. -/
  term : Term n
  /-- Coordinate queried at this step. -/
  index : Fin n
  /-- Value that satisfies the source literal at `index`. -/
  satisfyingValue : Bool
  /-- Finite symbol retained by the switching encoding. -/
  advice : QueryAdvice widthBound
  deriving DecidableEq

/-- The two local facts needed to decode an internal query record: its hidden
value satisfies the named literal, and its public position selects the hidden
coordinate from the source term. -/
def QueryRecord.WellFormed
    (record : QueryRecord n widthBound) : Prop :=
  record.term.requirements record.index = some record.satisfyingValue ∧
    record.term.orderedSupport[record.advice.position.val]? =
      some record.index

/-- The internal query record's satisfying assignment step. -/
def QueryRecord.satisfyingStep
    (record : QueryRecord n widthBound) : DecisionTree.PathStep n :=
  ⟨record.index, record.satisfyingValue⟩

/-- Forget the internal fields of a query record. -/
def QueryRecord.toAdvice
    (record : QueryRecord n widthBound) : QueryAdvice widthBound :=
  record.advice

/-- Query advice is exactly a bounded position and two bits. -/
def QueryAdvice.equivProduct (widthBound : Nat) :
    QueryAdvice widthBound ≃ Fin widthBound × Bool × Bool where
  toFun advice := (advice.position, advice.closesBlock, advice.pathValue)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv advice := by cases advice; rfl
  right_inv fields := by rcases fields with ⟨position, closes, value⟩; rfl

/-- There are exactly `4 * widthBound` possible symbols per query. -/
theorem card_queryAdvice (widthBound : Nat) :
    Fintype.card (QueryAdvice widthBound) = 4 * widthBound := by
  rw [Fintype.card_congr (QueryAdvice.equivProduct widthBound)]
  simp
  omega

/-- Fixed-length advice has the exact cardinality used by the weighted
switching calculation. -/
theorem card_advice (widthBound pathLength : Nat) :
    Fintype.card (Advice widthBound pathLength) =
      (4 * widthBound) ^ pathLength := by
  simp [Advice, card_queryAdvice]

/-- Reindex a list of known length as a fixed finite function. -/
def listToFn
    (values : List α)
    {length : Nat}
    (length_eq : values.length = length) : Fin length → α :=
  fun index => values.get (Fin.cast length_eq.symm index)

/-- Reindexing a list and then listing the function loses no information. -/
theorem ofFn_listToFn
    (values : List α)
    {length : Nat}
    (length_eq : values.length = length) :
    List.ofFn (listToFn values length_eq) = values := by
  subst length
  exact List.ofFn_get values

end Switching

namespace LiteralSet

/-- Deterministic Boolean value extracted from a literal requirement. On the
support of the literal set this is its unique satisfying value. -/
def satisfyingValue
    (set : LiteralSet n)
    (index : Fin n) : Bool :=
  (set.requirements index).getD false

/-- Position of a coordinate in a source term, reduced into the declared
width bound. Valid traced queries are proved below to lie below the bound, so
the reduction does not change their position. -/
def sourcePosition
    [NeZero widthBound]
    (set : LiteralSet n)
    (index : Fin n) : Fin widthBound :=
  Fin.ofNat widthBound (set.orderedSupport.idxOf index)

/-- A support coordinate's extracted Boolean value is its literal's required
value. -/
theorem requirements_satisfyingValue_of_mem_support
    (set : LiteralSet n)
    (index : Fin n)
    (present : index ∈ set.support) :
    set.requirements index = some (set.satisfyingValue index) := by
  rw [mem_support] at present
  unfold satisfyingValue
  cases required : set.requirements index with
  | none => exact False.elim (present required)
  | some value => rfl

/-- The ordered support lists each support coordinate exactly once, so its
length is the literal-set width. -/
theorem length_orderedSupport (set : LiteralSet n) :
    set.orderedSupport.length = set.width := by
  rw [← List.toFinset_card_of_nodup set.nodup_orderedSupport]
  congr 1
  ext index
  simp

/-- For a valid bounded term coordinate, reduction modulo the width bound is
inert. -/
theorem sourcePosition_val_of_mem_support
    [NeZero widthBound]
    (set : LiteralSet n)
    (index : Fin n)
    (bounded : set.width ≤ widthBound)
    (present : index ∈ set.support) :
    (set.sourcePosition (widthBound := widthBound) index).val =
      set.orderedSupport.idxOf index := by
  have orderedPresent : index ∈ set.orderedSupport :=
    (mem_orderedSupport set index).2 present
  have belowWidth : set.orderedSupport.idxOf index < set.width := by
    rw [← set.length_orderedSupport]
    exact List.idxOf_lt_length_iff.mpr orderedPresent
  simp [sourcePosition,
    Nat.mod_eq_of_lt (belowWidth.trans_le bounded)]

/-- Decoding a valid bounded source position recovers its coordinate. -/
theorem getElem?_sourcePosition_of_mem_support
    [NeZero widthBound]
    (set : LiteralSet n)
    (index : Fin n)
    (bounded : set.width ≤ widthBound)
    (present : index ∈ set.support) :
    set.orderedSupport[
        (set.sourcePosition (widthBound := widthBound) index).val]? =
      some index := by
  rw [set.sourcePosition_val_of_mem_support index bounded present]
  exact List.getElem?_idxOf ((mem_orderedSupport set index).2 present)

end LiteralSet

namespace DNF

mutual

/-- Annotate all queries in a canonical trace. -/
def CanonicalTrace.queryRecords
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    List (Switching.QueryRecord n widthBound) :=
  match trace with
  | .nil _ => []
  | .start _ _ _ block => block.queryRecords

/-- Annotate the queries remaining in one canonical source-term block. -/
def CanonicalBlockTrace.queryRecords
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps) :
    List (Switching.QueryRecord n widthBound) :=
  match trace with
  | .nil _ _ _ => []
  | .takeMore (index := index) (value := value) tail =>
      ⟨term, index, term.satisfyingValue index,
        ⟨term.sourcePosition index, false, value⟩⟩ ::
        tail.queryRecords
  | .takeLast (index := index) (value := value) tail =>
      ⟨term, index, term.satisfyingValue index,
        ⟨term.sourcePosition index, true, value⟩⟩ ::
        tail.queryRecords

end

/-- The satisfying query transcript underlying the output assignment. -/
def CanonicalTrace.satisfyingSteps
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    List (DecisionTree.PathStep n) :=
  trace.queryRecords (widthBound := widthBound) |>.map
    Switching.QueryRecord.satisfyingStep

/-- Satisfying assignment placed into the injection's output restriction. -/
def CanonicalTrace.satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) : PartialAssignment n :=
  DecisionTree.PathStep.assignment
    (trace.satisfyingSteps (widthBound := widthBound))

/-- Variable-length advice before it is reindexed by the prescribed path
length. -/
def CanonicalTrace.adviceList
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    List (Switching.QueryAdvice widthBound) :=
  trace.queryRecords.map Switching.QueryRecord.toAdvice

mutual

/-- Query-record coordinates agree exactly with the original path
coordinates. -/
theorem CanonicalTrace.queryRecords_indices
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    (trace.queryRecords (widthBound := widthBound)).map
        Switching.QueryRecord.index =
      DecisionTree.PathStep.indices steps :=
  match trace with
  | .nil _ => rfl
  | .start _ _ _ block => block.queryRecords_indices

/-- The same coordinate agreement while traversing a source-term block. -/
theorem CanonicalBlockTrace.queryRecords_indices
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps) :
    (trace.queryRecords (widthBound := widthBound)).map
        Switching.QueryRecord.index =
      DecisionTree.PathStep.indices steps :=
  match trace with
  | .nil _ _ _ => rfl
  | .takeMore tail => congrArg (List.cons _) tail.queryRecords_indices
  | .takeLast tail => congrArg (List.cons _) tail.queryRecords_indices

end

mutual

/-- Every record extracted from a width-bounded canonical trace carries a
genuine satisfying literal value and a correctly decodable source position.
-/
theorem CanonicalTrace.queryRecords_wellFormed
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    ∀ record ∈ trace.queryRecords (widthBound := widthBound),
      Switching.QueryRecord.WellFormed record :=
  match trace with
  | .nil _ => by simp [CanonicalTrace.queryRecords]
  | @CanonicalTrace.start _ _ rho term indices steps found support_eq
      _ block =>
      block.queryRecords_wellFormed
        bounded
        (bounded term (firstSurvivingIn_mem rho formula.terms found))
        (fun index present =>
          (mem_liveSupport term rho index).1 (by
            simpa [support_eq] using present) |>.1)

/-- The record invariant while traversing one source-term block. -/
theorem CanonicalBlockTrace.queryRecords_wellFormed
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps)
    (bounded : formula.WidthAtMost widthBound)
    (termBound : term.width ≤ widthBound)
    (supported : ∀ index, index ∈ indices → index ∈ term.support) :
    ∀ record ∈ trace.queryRecords (widthBound := widthBound),
      Switching.QueryRecord.WellFormed record :=
  match trace with
  | .nil _ _ _ => by simp [CanonicalBlockTrace.queryRecords]
  | @CanonicalBlockTrace.takeMore _ _ _ _ index next rest value steps tail =>
      by
        intro record present
        simp only [CanonicalBlockTrace.queryRecords,
          List.mem_cons] at present
        rcases present with rfl | present
        · exact ⟨term.requirements_satisfyingValue_of_mem_support index
              (supported index (by simp)),
            term.getElem?_sourcePosition_of_mem_support index termBound
              (supported index (by simp))⟩
        · exact tail.queryRecords_wellFormed bounded termBound
            (fun current currentPresent =>
              supported current (by simp [currentPresent])) record present
  | @CanonicalBlockTrace.takeLast _ _ _ _ index value steps tail =>
      by
        intro record present
        simp only [CanonicalBlockTrace.queryRecords,
          List.mem_cons] at present
        rcases present with rfl | present
        · exact ⟨term.requirements_satisfyingValue_of_mem_support index
              (supported index (by simp)),
            term.getElem?_sourcePosition_of_mem_support index termBound
              (supported index (by simp))⟩
        · exact tail.queryRecords_wellFormed bounded record present

end

/-- The satisfying transcript queries precisely the original path's
coordinates, changing only their Boolean values. -/
theorem CanonicalTrace.satisfyingSteps_indices
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    DecisionTree.PathStep.indices
        (trace.satisfyingSteps (widthBound := widthBound)) =
      DecisionTree.PathStep.indices steps := by
  simpa [CanonicalTrace.satisfyingSteps,
    DecisionTree.PathStep.indices, List.map_map,
    Function.comp_def, Switching.QueryRecord.satisfyingStep] using
    trace.queryRecords_indices (widthBound := widthBound)

/-- The satisfying assignment fixes the same coordinates as the original
path assignment. -/
theorem CanonicalTrace.satisfyingAssignment_fixedVariables
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    (trace.satisfyingAssignment (widthBound := widthBound)).fixedVariables =
      (DecisionTree.PathStep.assignment steps).fixedVariables := by
  unfold CanonicalTrace.satisfyingAssignment
  rw [DecisionTree.PathStep.fixedVariables_assignment,
    DecisionTree.PathStep.fixedVariables_assignment]
  exact congrArg List.toFinset
    (trace.satisfyingSteps_indices (widthBound := widthBound))

/-- Variable-length advice has one symbol per original path query. -/
theorem CanonicalTrace.length_adviceList
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    (trace.adviceList (widthBound := widthBound)).length = steps.length := by
  have equalLengths := congrArg List.length
    (trace.queryRecords_indices (widthBound := widthBound))
  simpa [CanonicalTrace.adviceList,
    DecisionTree.PathStep.indices] using equalLengths

/-- Fixed-length advice associated to a trace whose path has the prescribed
length. -/
def CanonicalTrace.advice
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    {pathLength : Nat}
    (trace : DNF.CanonicalTrace formula rho steps)
    (length_eq : steps.length = pathLength) :
    Switching.Advice widthBound pathLength :=
  Switching.listToFn trace.adviceList
    ((trace.length_adviceList (widthBound := widthBound)).trans length_eq)

/-- Listing fixed-length trace advice recovers the original advice list. -/
theorem CanonicalTrace.ofFn_advice
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    {pathLength : Nat}
    (trace : DNF.CanonicalTrace formula rho steps)
    (length_eq : steps.length = pathLength) :
    List.ofFn (trace.advice (widthBound := widthBound) length_eq) =
      trace.adviceList := by
  unfold CanonicalTrace.advice
  apply Switching.ofFn_listToFn

/-- A traced satisfying assignment fixes exactly the prescribed canonical
path length. -/
theorem CanonicalPath.satisfyingAssignment_fixedCount
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : DNF.CanonicalPath formula rho pathLength)
    (trace : DNF.CanonicalTrace formula rho path.steps) :
    (trace.satisfyingAssignment (widthBound := widthBound)).fixedCount =
      pathLength := by
  calc
    (trace.satisfyingAssignment (widthBound := widthBound)).fixedCount =
        (DecisionTree.PathStep.assignment path.steps).fixedCount := by
      unfold PartialAssignment.fixedCount
      rw [trace.satisfyingAssignment_fixedVariables]
    _ = pathLength := path.assignment_fixedCount

/-- A traced satisfying assignment fixes only variables live before the path
began. -/
theorem CanonicalPath.satisfyingAssignment_fixesOnlyLive
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : DNF.CanonicalPath formula rho pathLength)
    (trace : DNF.CanonicalTrace formula rho path.steps) :
    (trace.satisfyingAssignment
        (widthBound := widthBound)).fixedVariables ⊆ rho.liveVariables := by
  rw [trace.satisfyingAssignment_fixedVariables]
  exact path.assignment_fixesOnlyLive

end DNF
end AC0
end Algebraic
