import Algebraic.PartialAssignment

/-!
# Boolean partial-assignment regression tests
-/

namespace AlgebraicTests.PartialAssignment

open Algebraic

example (input : Fin 3 -> Bool) :
    (PartialAssignment.fix (1 : Fin 3) true).apply input 1 = true := by
  simp

example (input : Fin 3 -> Bool) :
    (PartialAssignment.fix (1 : Fin 3) true).apply input 0 = input 0 := by
  apply PartialAssignment.apply_of_live
  simp [PartialAssignment.fix]

example :
    (PartialAssignment.fix (1 : Fin 3) true).liveVariables =
      ({0, 2} : Finset (Fin 3)) := by
  rw [PartialAssignment.liveVariables_fix]
  decide

example
    (rho sigma : PartialAssignment 4)
    (input : Fin 4 -> Bool) :
    (rho.refine sigma).apply input = rho.apply (sigma.apply input) :=
  PartialAssignment.apply_refine rho sigma input

example
    (rho extension : PartialAssignment 4)
    (newFixes : extension.fixedVariables ⊆ rho.liveVariables) :
    (rho.refine extension).clear extension.fixedVariables = rho :=
  PartialAssignment.clear_refine_fixedVariables rho extension newFixes

example
    (rho tail : PartialAssignment 4)
    (selected : Fin 4)
    (pathValue satisfyingValue : Bool)
    (live : rho selected = none) :
    (PartialAssignment.fix selected pathValue).refine
        (rho.refine
          ((PartialAssignment.fix selected satisfyingValue).refine tail)) =
      (rho.refine (PartialAssignment.fix selected pathValue)).refine tail :=
  PartialAssignment.fix_refine_refine_fix rho tail selected
    pathValue satisfyingValue live

def firstBit : ScalarFunction Bool 3 :=
  fun input => input 0

example :
    firstBit.restrict (PartialAssignment.fix 0 true) = fun _ => true := by
  funext input
  simp [firstBit]

def twoOutputs : Target Bool 3 2 :=
  fun input output => if output = 0 then input 0 else input 2

example :
    DependsOnlyOn
      (twoOutputs.restrict (PartialAssignment.fix 0 false))
      (PartialAssignment.fix (0 : Fin 3) false).liveVariables :=
  Target.restrict_dependsOnlyOn_live twoOutputs _

end AlgebraicTests.PartialAssignment
