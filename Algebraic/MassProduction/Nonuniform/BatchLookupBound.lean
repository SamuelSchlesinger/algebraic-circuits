import Algebraic.MassProduction.Nonuniform.BatchLookup
import Algebraic.MassProduction.FiniteParameters

/-!
# Batched lookup with canonical padding and a compact size bound

For `T = 2^keyWidth + requests`, the next-power-of-two layout contains fewer
than `2*T` records. The complete lookup circuit has at most
`256*T*(ceil(log2 T) + keyWidth + valueWidth + 2)^5` charged gates.
-/

namespace Algebraic.MassProduction.Nonuniform.BatchLookup

open Sorting RoutingMetadata

/-- A compact polynomial bound retaining linear dependence on record count. -/
theorem circuit_cost_le_polynomial
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth) :
    (circuit table recordCount).cost DeMorgan.standardCost ≤
      128 * networkRecords depth * (depth + keyWidth + valueWidth + 2) ^ 5 := by
  let width := depth + keyWidth + valueWidth + 2
  have widthPositive : 1 ≤ width := by dsimp [width]; omega
  have depthLe : depth ≤ width := by dsimp [width]; omega
  have valueLe : valueWidth ≤ width := by dsimp [width]; omega
  have keyLe : keyWidth ≤ width := by dsimp [width]; omega
  have recordLe : recordWidth keyWidth (depth + 1) valueWidth ≤ width := by
    dsimp [recordWidth, Routing.recordWidth, width]
    omega
  have sorterBound (key : Nat) (keyLe : key ≤ width) :
      depth * depth * networkRecords depth *
        ((2 * recordWidth keyWidth (depth + 1) valueWidth) *
          (2 * (key * (6 * key + 4)) + 4)) ≤
        48 * networkRecords depth * width ^ 5 := by
    calc
      _ ≤ width * width * networkRecords depth *
          ((2 * width) * (2 * (width * (6 * width + 4)) + 4)) := by gcongr
      _ ≤ width * width * networkRecords depth * ((2 * width) * (24 * width ^ 2)) := by
        gcongr
        nlinarith
      _ = _ := by ring
  have firstSort := sorterBound (keyWidth + 1) (by dsimp [width]; omega)
  have lastSort := sorterBound (depth + 2) (by dsimp [width]; omega)
  have scan : networkRecords depth * (valueWidth * (6 * keyWidth + 4)) ≤
      10 * networkRecords depth * width ^ 2 := by
    calc
      _ ≤ networkRecords depth * (width * (6 * width + 4)) := by gcongr
      _ ≤ 10 * networkRecords depth * width ^ 2 := by
        have localBound : width * (6 * width + 4) ≤ 10 * width ^ 2 := by nlinarith
        nlinarith [Nat.mul_le_mul_left (networkRecords depth) localBound]
  have wiring : networkBits depth (recordWidth keyWidth (depth + 1) valueWidth) ≤
      networkRecords depth * width := Nat.mul_le_mul_left _ recordLe
  have squareLe : width ^ 2 ≤ width ^ 5 := Nat.pow_le_pow_right widthPositive (by decide)
  have linearLe : width ≤ width ^ 5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right widthPositive (by decide : 1 ≤ 5)
  have scanLarge := scan.trans (Nat.mul_le_mul_left (10 * networkRecords depth) squareLe)
  have wiringLarge := wiring.trans (Nat.mul_le_mul_left (networkRecords depth) linearLe)
  have raw := circuit_cost_le table recordCount
  change _ ≤ 128 * networkRecords depth * width ^ 5
  calc
    _ ≤ (48 * networkRecords depth * width ^ 5 + 10 * networkRecords depth * width ^ 5) +
        (networkRecords depth * width ^ 5 + 48 * networkRecords depth * width ^ 5) :=
      raw.trans (Nat.add_le_add (Nat.add_le_add firstSort scanLarge)
        (Nat.add_le_add wiringLarge lastSort))
    _ ≤ _ := by nlinarith

/-- The concrete lookup bound holds for every table and every query count,
using canonical padding. Constants in the source table are hardwired. -/
theorem existsCircuit
    (keyWidth valueWidth requests : Nat)
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool) :
    ∃ gates, ∃ lookup : Circuit DeMorgan.signature (requests * keyWidth) gates
        (requests * valueWidth),
      (∀ input request bit, lookup.eval DeMorgan.interpretation input
        (finProdFinEquiv (request, bit)) =
          table (fun addressBit => input (finProdFinEquiv (request, addressBit))) bit) ∧
      lookup.cost DeMorgan.standardCost ≤
        256 * (2 ^ keyWidth + requests) *
          (FiniteParameters.binaryDepth (2 ^ keyWidth + requests) + keyWidth + valueWidth + 2) ^ 5 := by
  let records := 2 ^ keyWidth + requests
  let depth := FiniteParameters.binaryDepth records
  have recordCount : 2 ^ keyWidth + requests + FiniteParameters.paddingCount records =
      networkRecords depth := FiniteParameters.records_add_paddingCount records
  refine ⟨_, circuit table recordCount, circuit_eval table recordCount, ?_⟩
  have recordsPositive : 0 < records := by
    have : 0 < (2 : Nat) ^ keyWidth := by positivity
    dsimp [records]
    omega
  have padded := (FiniteParameters.networkRecords_binaryDepth_lt_two_mul records recordsPositive).le
  calc
    _ ≤ 128 * networkRecords depth * (depth + keyWidth + valueWidth + 2) ^ 5 :=
      circuit_cost_le_polynomial table recordCount
    _ ≤ 128 * (2 * records) * (depth + keyWidth + valueWidth + 2) ^ 5 := by gcongr
    _ = _ := by dsimp [records, depth]; ring

end Algebraic.MassProduction.Nonuniform.BatchLookup
