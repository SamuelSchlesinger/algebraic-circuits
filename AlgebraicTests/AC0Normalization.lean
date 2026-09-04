import Algebraic.Basis.AC0.Normalization

/-!
# AC0 dual-rail normalization regressions

These examples exercise the public operation-level simulation and exact cost
law on concrete gates. The generic theorems themselves cover every fan-in.
-/

namespace AlgebraicTests.AC0Normalization

open Algebraic

example (input : Fin 3 -> Bool) :
    AC0.DualRail.encode (AC0.interpretation (.and 3) input) =
      (AC0.DualRail.translation.operation (.and 3)).eval
        AC0.interpretation
        (Block.flatten (AC0.DualRail.encode ∘ input)) :=
  AC0.DualRail.operation_encode (.and 3) input

example :
    AC0.DualRail.translation.pullCost AC0.andOrCost (.and 7) = 2 := by
  rw [AC0.DualRail.pullCost_andOrCost]
  rfl

example :
    AC0.DualRail.translation.pullCost AC0.andOrCost .not = 0 := by
  rw [AC0.DualRail.pullCost_andOrCost]
  rfl

example (input : Fin 5 -> Nat) :
    AC0.DualRail.duplicateDepth
        (AC0.logicalDepthInterpretation (.or 5) input) =
      (AC0.DualRail.translation.operation (.or 5)).eval
        AC0.logicalDepthInterpretation
        (Block.flatten (AC0.DualRail.duplicateDepth ∘ input)) :=
  AC0.DualRail.operation_duplicateDepth (.or 5) input

/-- A source circuit with a genuinely internal NOT gate. -/
def internalNotCircuit : Circuit AC0.signature 2 2 1 where
  program := ((Program.empty : Program AC0.signature 2 0).gate {
    op := .and 2
    wires := Wire.input
  }).gate {
    op := .not
    wires := fun _ => Wire.gate 0
  }
  outputs := fun _ => Wire.gate 1

example :
    ¬ AC0.Program.NegationsAtInputs internalNotCircuit.program := by
  simp [internalNotCircuit, AC0.Program.NegationsAtInputs,
    AC0.Line.NegationAtInput]
  constructor
  · intro equality
    have values := congrArg Fin.val equality
    simp at values
  · intro equality
    have values := congrArg Fin.val equality
    simp at values

example : AC0.Program.NegationsAtInputs
    (AC0.DualRail.normalize internalNotCircuit).program :=
  AC0.DualRail.normalize_negationsAtInputs internalNotCircuit

example (input : Fin 2 -> Bool) :
    (AC0.DualRail.normalize internalNotCircuit).eval
        AC0.interpretation input =
      internalNotCircuit.eval AC0.interpretation input := by
  simp

example :
    (AC0.DualRail.normalize internalNotCircuit).cost AC0.andOrCost =
      2 * internalNotCircuit.cost AC0.andOrCost := by
  simp

example :
    AC0.Circuit.logicalDepth (AC0.DualRail.normalize internalNotCircuit) =
      AC0.Circuit.logicalDepth internalNotCircuit := by
  simp

example (family : Circuit.Family AC0.signature 1)
    (smallDepth : AC0.Family.IsRawSmallDepth family) :
    AC0.Family.IsSmallDepth (AC0.DualRail.normalizeFamily family) :=
  AC0.DualRail.normalizeFamily_isSmallDepth family smallDepth

example (family : Circuit.Family AC0.signature 1)
    (polynomialCost : family.HasPolynomialCost AC0.andOrCost) :
    (AC0.DualRail.normalizeFamily family).HasPolynomialSize :=
  AC0.DualRail.normalizeFamily_hasPolynomialSize family polynomialCost

example (target : Target.Family Bool 1) :
    AC0.RawComputable target <-> AC0.Computable target :=
  AC0.rawComputable_iff_computable target

end AlgebraicTests.AC0Normalization
