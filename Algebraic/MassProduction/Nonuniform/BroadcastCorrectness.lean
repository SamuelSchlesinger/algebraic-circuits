import Algebraic.MassProduction.Nonuniform.BroadcastCircuit
import Algebraic.MassProduction.RoutingCorrectness

/-!
# Broadcast correctness with repeated destinations

Sorting a unique source before all same-key destinations creates one linked
run. The shared propagation circuit carries its payload to every destination
in that run. The number of destinations is unrestricted.
-/

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting Routing

/-- The concrete broadcast bit has a source connected by adjacent links. -/
theorem payloadCircuit_eq_true_iff
    (bit : Fin payloadWidth)
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (record : Fin (networkRecords depth)) :
    (payloadCircuit depth keyWidth payloadWidth bit).eval
        DeMorgan.interpretation input record = true ↔
      ∃ start : Fin (networkRecords depth), start ≤ record ∧
        recordTag input start = false ∧ recordPayload input start bit = true ∧
        ∀ index : Fin (networkRecords depth), start < index → index ≤ record →
          (linkExpression depth keyWidth payloadWidth index).eval input = true := by
  rw [payloadCircuit_eval, Propagation.value_eq_true_iff]
  constructor
  · rintro ⟨start, startsBefore, starts, links⟩
    have startFits : start < networkRecords depth := by omega
    have source : recordTag input ⟨start, startFits⟩ = false ∧
        recordPayload input ⟨start, startFits⟩ bit = true := by
      simpa only [Propagation.sourceInput, dif_pos startFits, inputExpression,
        Fin.addCases_left, sourceExpression_eval, Bool.and_eq_true, Bool.not_eq_true']
        using starts
    refine ⟨⟨start, startFits⟩, by exact Nat.le_of_lt_succ startsBefore,
      source.1, source.2, ?_⟩
    intro index after before
    have linked := links index.val after (Nat.lt_succ_of_le before)
    simpa only [Propagation.linkInput, dif_pos index.isLt, inputExpression,
      Fin.addCases_right] using linked
  · rintro ⟨start, startsBefore, sourceTag, sourcePayload, links⟩
    refine ⟨start.val, Nat.lt_succ_of_le startsBefore, ?_, ?_⟩
    · simpa only [Propagation.sourceInput, dif_pos start.isLt, inputExpression,
        Fin.addCases_left, sourceExpression_eval, Bool.and_eq_true, Bool.not_eq_true']
        using And.intro sourceTag sourcePayload
    · intro index after before
      have indexFits : index < networkRecords depth := by omega
      have linked := links ⟨index, indexFits⟩ after (Nat.le_of_lt_succ before)
      simpa only [Propagation.linkInput, dif_pos indexFits, inputExpression,
        Fin.addCases_right] using linked

/-- Adjacent links force the key at the source and destination to agree. -/
theorem sameKeyOfLinked
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (start finish : Fin (networkRecords depth)) (ordered : start ≤ finish)
    (links : ∀ index : Fin (networkRecords depth), start < index → index ≤ finish →
      (linkExpression depth keyWidth payloadWidth index).eval input = true) :
    recordKey input start = recordKey input finish := by
  have connected : ∀ index, start.val ≤ index →
      ∀ fits : index < networkRecords depth, index ≤ finish.val →
        recordKey input start = recordKey input ⟨index, fits⟩ := by
    intro index after
    induction index, after using Nat.le_induction with
    | base => intro _ _; rfl
    | succ index after ih =>
        intro fits before
        have linked := links ⟨index + 1, fits⟩ (by exact Nat.lt_succ_of_le after) before
        have adjacent := (linkExpression_eval_eq_true_iff input
          ⟨index + 1, fits⟩ (Nat.zero_lt_succ index)).mp linked
        exact (ih (by omega) (by omega)).trans adjacent
  exact connected finish.val ordered finish.isLt le_rfl

/-- A unique source supplies every record in its linked interval. Only the
source is required to be unique; repeated destinations are permitted. -/
theorem payloadCircuit_routesInterval
    (bit : Fin payloadWidth)
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (source destination : Fin (networkRecords depth))
    (ordered : source ≤ destination)
    (sourceTag : recordTag input source = false)
    (sourceUnique : ∀ index, recordKey input index = recordKey input source →
      recordTag input index = false → index = source)
    (interval : ∀ index, source ≤ index → index ≤ destination →
      recordKey input index = recordKey input source) :
    (payloadCircuit depth keyWidth payloadWidth bit).eval
        DeMorgan.interpretation input destination = recordPayload input source bit := by
  apply Bool.eq_iff_iff.mpr
  rw [payloadCircuit_eq_true_iff]
  constructor
  · rintro ⟨start, startsBefore, startTag, starts, links⟩
    have same := sameKeyOfLinked input start destination startsBefore links
    have equalSource := sourceUnique start
      (same.trans (interval destination ordered le_rfl)) startTag
    simpa only [equalSource] using starts
  · intro starts
    refine ⟨source, ordered, sourceTag, starts, ?_⟩
    intro index after before
    have positive : 0 < index.val := by exact Nat.lt_of_le_of_lt (Nat.zero_le _) after
    apply (linkExpression_eval_eq_true_iff input index positive).mpr
    exact (interval (predecessor index positive) (by
        change source.val ≤ index.val - 1
        exact Nat.le_sub_one_of_lt after) (by
        change index.val - 1 ≤ destination.val
        exact (Nat.sub_le _ _).trans before)).trans
      (interval index after.le before).symm

/-- In a sorted array, the source and every same-key destination enclose
only records having that key. This follows from the covered tag pair. -/
theorem sourceIntervalOfSorted
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (sorted : FlatKeysSorted (keyAndTagFitsRecord keyWidth payloadWidth) true input)
    (source destination : Fin (networkRecords depth))
    (sameKey : recordKey input source = recordKey input destination)
    (sourceTag : recordTag input source = false)
    (destinationTag : recordTag input destination = true) :
    source ≤ destination ∧ ∀ index, source ≤ index → index ≤ destination →
      recordKey input index = recordKey input source := by
  have increasing : Sorting.Semantics.SequenceIncreasing (recordKeyAndTag input) := sorted
  have covered := recordKeyAndTag_covBy_of_sameKey input source destination
    sameKey sourceTag destinationTag
  have monotone : Monotone (recordKeyAndTag input) := by
    intro left right ordered
    rcases ordered.eq_or_lt with rfl | strict
    · exact le_rfl
    · exact increasing left right strict
  have ordered : source < destination := by
    by_contra wrong
    exact (not_le_of_gt covered.lt) (monotone (le_of_not_gt wrong))
  refine ⟨ordered.le, ?_⟩
  intro index after before
  rcases covered.eq_or_eq (monotone after) (monotone before) with first | last
  · exact ((recordKeyAndTag_eq_iff input index source).mp first).1
  · exact ((recordKeyAndTag_eq_iff input index destination).mp last).1.trans sameKey.symm

/-- Sorted broadcasting routes one unique source to any same-key destination.
No uniqueness premise is imposed on destination keys. -/
theorem payloadCircuit_routesSorted
    (bit : Fin payloadWidth)
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (sorted : FlatKeysSorted (keyAndTagFitsRecord keyWidth payloadWidth) true input)
    (source destination : Fin (networkRecords depth))
    (sameKey : recordKey input source = recordKey input destination)
    (sourceTag : recordTag input source = false)
    (destinationTag : recordTag input destination = true)
    (sourceUnique : ∀ index, recordKey input index = recordKey input source →
      recordTag input index = false → index = source) :
    (payloadCircuit depth keyWidth payloadWidth bit).eval
        DeMorgan.interpretation input destination = recordPayload input source bit := by
  obtain ⟨ordered, interval⟩ := sourceIntervalOfSorted input sorted source destination
    sameKey sourceTag destinationTag
  exact payloadCircuit_routesInterval bit input source destination ordered
    sourceTag sourceUnique interval

end Algebraic.MassProduction.Nonuniform.Broadcast
