import Algebraic.Restriction
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Card

/-!
# Boolean partial assignments

A partial assignment records, for each named Boolean variable, either a fixed
value or a live variable. Restricted functions retain the original input
indexing: values supplied at fixed coordinates are ignored. This representation
is convenient for random restrictions and decision trees, while conversion to
`InputSubstitution` connects it to the library's existing semantic interface.

Sequential refinement is left-biased. In `rho.refine sigma`, assignments
already fixed by `rho` remain fixed, and `sigma` is consulted only at variables
left live by `rho`.
-/

namespace Algebraic

/-- A Boolean restriction on `n` named variables. `none` means that a variable
is live; `some value` fixes it to `value`. -/
abbrev PartialAssignment (n : Nat) := Fin n -> Option Bool

namespace PartialAssignment

/-- Two partial assignments are equal when they agree on every variable. -/
theorem ext
    {rho sigma : PartialAssignment n}
    (equal : forall index, rho index = sigma index) :
    rho = sigma :=
  funext equal

/-- The empty partial assignment leaves every variable live. -/
def empty : PartialAssignment n :=
  fun _ => none

/-- A total assignment fixes every variable. -/
def total (input : Fin n -> Bool) : PartialAssignment n :=
  fun index => some (input index)

/-- The partial assignment fixing exactly one variable. -/
def fix (selected : Fin n) (value : Bool) : PartialAssignment n :=
  fun index => if index = selected then some value else none

@[simp] theorem empty_apply (index : Fin n) :
    (empty : PartialAssignment n) index = none := rfl

@[simp] theorem total_apply
    (input : Fin n -> Bool)
    (index : Fin n) :
    total input index = some (input index) := rfl

@[simp] theorem fix_selected
    (selected : Fin n)
    (value : Bool) :
    fix selected value selected = some value := by
  simp [fix]

@[simp] theorem fix_other
    (selected index : Fin n)
    (value : Bool)
    (different : index ≠ selected) :
    fix selected value index = none := by
  simp [fix, different]

/-- Apply a partial assignment to a complete input. Values at fixed variables
are overwritten, while values at live variables are retained. -/
def apply
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) : Fin n -> Bool :=
  fun index => (rho index).getD (input index)

@[simp] theorem apply_of_live
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    {index : Fin n}
    (live : rho index = none) :
    rho.apply input index = input index := by
  simp [apply, live]

@[simp] theorem apply_of_fixed
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    {index : Fin n}
    {value : Bool}
    (fixed : rho index = some value) :
    rho.apply input index = value := by
  simp [apply, fixed]

@[simp] theorem apply_empty (input : Fin n -> Bool) :
    (empty : PartialAssignment n).apply input = input := by
  funext index
  simp [apply]

@[simp] theorem apply_total
    (fixed input : Fin n -> Bool) :
    (total fixed).apply input = fixed := by
  funext index
  simp [apply]

/-- Fixing a variable to the value it already has leaves a complete input
unchanged. -/
theorem apply_fix_eq_self
    (input : Fin n -> Bool)
    (selected : Fin n)
    (value : Bool)
    (selectedValue : input selected = value) :
    (fix selected value).apply input = input := by
  funext index
  by_cases equal : index = selected
  · subst index
    simp [apply, fix, selectedValue]
  · simp [apply, fix, equal]

/-- Refine `rho` with `sigma`, retaining every value already fixed by `rho`. -/
def refine
    (rho sigma : PartialAssignment n) : PartialAssignment n :=
  fun index =>
    match rho index with
    | some value => some value
    | none => sigma index

@[simp] theorem empty_refine (rho : PartialAssignment n) :
    empty.refine rho = rho := by
  apply ext
  intro index
  rfl

@[simp] theorem refine_empty (rho : PartialAssignment n) :
    rho.refine empty = rho := by
  apply ext
  intro index
  cases fixed : rho index <;> simp [refine, fixed]

/-- Applying a sequential refinement is function composition on inputs. -/
theorem apply_refine
    (rho sigma : PartialAssignment n)
    (input : Fin n -> Bool) :
    (rho.refine sigma).apply input = rho.apply (sigma.apply input) := by
  funext index
  cases fixed : rho index with
  | none => simp [refine, apply, fixed]
  | some value => simp [refine, apply, fixed]

/-- Sequential refinement is associative. -/
theorem refine_assoc
    (rho sigma tau : PartialAssignment n) :
    (rho.refine sigma).refine tau = rho.refine (sigma.refine tau) := by
  apply ext
  intro index
  cases first : rho index <;>
    cases second : sigma index <;>
      simp [refine, first, second]

/-- View a partial assignment as a semantic input substitution on the same
named variables. -/
def toInputSubstitution
    (rho : PartialAssignment n) : InputSubstitution Bool n n :=
  fun index input => rho.apply input index

@[simp] theorem toInputSubstitution_apply
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    rho.toInputSubstitution.apply input = rho.apply input := rfl

@[simp] theorem toInputSubstitution_empty :
    (empty : PartialAssignment n).toInputSubstitution =
      (InputSubstitution.id : InputSubstitution Bool n n) := by
  funext index input
  simp [toInputSubstitution, InputSubstitution.id, apply]

/-- Conversion to input substitutions preserves sequential composition. -/
theorem toInputSubstitution_refine
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).toInputSubstitution =
      rho.toInputSubstitution.comp sigma.toInputSubstitution := by
  funext index input
  exact congrFun (apply_refine rho sigma input) index

/-- The finite set of variables left live by a partial assignment. -/
def liveVariables (rho : PartialAssignment n) : Finset (Fin n) :=
  Finset.univ.filter fun index => rho index = none

@[simp] theorem mem_liveVariables
    (rho : PartialAssignment n)
    (index : Fin n) :
    index ∈ rho.liveVariables ↔ rho index = none := by
  simp [liveVariables]

/-- The number of variables left live by a partial assignment. -/
def liveCount (rho : PartialAssignment n) : Nat :=
  rho.liveVariables.card

/-- The finite set of variables fixed by a partial assignment. -/
def fixedVariables (rho : PartialAssignment n) : Finset (Fin n) :=
  Finset.univ.filter fun index => rho index ≠ none

@[simp] theorem mem_fixedVariables
    (rho : PartialAssignment n)
    (index : Fin n) :
    index ∈ rho.fixedVariables ↔ rho index ≠ none := by
  simp [fixedVariables]

/-- The number of variables fixed by a partial assignment. -/
def fixedCount (rho : PartialAssignment n) : Nat :=
  rho.fixedVariables.card

@[simp] theorem liveVariables_empty :
    (empty : PartialAssignment n).liveVariables = Finset.univ := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem liveCount_empty :
    (empty : PartialAssignment n).liveCount = n := by
  simp [liveCount]

@[simp] theorem fixedVariables_empty :
    (empty : PartialAssignment n).fixedVariables = {} := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem fixedCount_empty :
    (empty : PartialAssignment n).fixedCount = 0 := by
  simp [fixedCount]

@[simp] theorem liveVariables_total (input : Fin n -> Bool) :
    (total input).liveVariables = {} := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem liveCount_total (input : Fin n -> Bool) :
    (total input).liveCount = 0 := by
  simp [liveCount]

@[simp] theorem fixedVariables_total (input : Fin n -> Bool) :
    (total input).fixedVariables = Finset.univ := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem fixedCount_total (input : Fin n -> Bool) :
    (total input).fixedCount = n := by
  simp [fixedCount]

/-- Every variable is either live or fixed, but not both. -/
theorem liveVariables_union_fixedVariables
    (rho : PartialAssignment n) :
    rho.liveVariables ∪ rho.fixedVariables = Finset.univ := by
  apply Finset.ext
  intro index
  cases fixed : rho index <;> simp [fixed]

/-- The live and fixed variable sets are disjoint. -/
theorem disjoint_liveVariables_fixedVariables
    (rho : PartialAssignment n) :
    Disjoint rho.liveVariables rho.fixedVariables := by
  rw [Finset.disjoint_left]
  intro index live fixed
  exact (mem_fixedVariables rho index).1 fixed
    ((mem_liveVariables rho index).1 live)

/-- Live and fixed variables partition the input coordinates exactly. -/
theorem liveCount_add_fixedCount
    (rho : PartialAssignment n) :
    rho.liveCount + rho.fixedCount = n := by
  rw [liveCount, fixedCount,
    ← Finset.card_union_of_disjoint
      (disjoint_liveVariables_fixedVariables rho),
    liveVariables_union_fixedVariables, Finset.card_fin]

/-- Fixing one variable removes exactly that variable from the live set. -/
theorem liveVariables_fix
    (selected : Fin n)
    (value : Bool) :
    (fix selected value).liveVariables = Finset.univ.erase selected := by
  apply Finset.ext
  intro index
  simp [liveVariables, fix]

/-- The live variables after sequential refinement are the variables left live
by both constituent partial assignments. -/
theorem liveVariables_refine
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).liveVariables =
      rho.liveVariables ∩ sigma.liveVariables := by
  apply Finset.ext
  intro index
  simp only [mem_liveVariables, Finset.mem_inter]
  cases fixed : rho index with
  | none => simp [refine, fixed]
  | some value => simp [refine, fixed]

/-- The variables fixed by a sequential refinement are exactly those fixed by
either constituent assignment. -/
theorem fixedVariables_refine
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).fixedVariables =
      rho.fixedVariables ∪ sigma.fixedVariables := by
  apply Finset.ext
  intro index
  simp only [mem_fixedVariables, Finset.mem_union]
  cases fixed : rho index with
  | none => simp [refine, fixed]
  | some value => simp [refine, fixed]

/-- Sequential refinement cannot increase the number of live variables. -/
theorem liveCount_refine_le_left
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).liveCount ≤ rho.liveCount := by
  rw [liveCount, liveVariables_refine]
  exact Finset.card_le_card Finset.inter_subset_left

/-- Refining by a one-variable assignment removes exactly that variable from
the live set. If it was already fixed, the set is unchanged. -/
theorem liveVariables_refine_fix
    (rho : PartialAssignment n)
    (selected : Fin n)
    (value : Bool) :
    (rho.refine (fix selected value)).liveVariables =
      rho.liveVariables.erase selected := by
  rw [liveVariables_refine, liveVariables_fix, Finset.inter_erase]
  simp

/-- Fixing a currently live variable strictly decreases the live count. -/
theorem liveCount_refine_fix_lt_of_live
    (rho : PartialAssignment n)
    (selected : Fin n)
    (value : Bool)
    (live : rho selected = none) :
    (rho.refine (fix selected value)).liveCount < rho.liveCount := by
  rw [liveCount, liveVariables_refine_fix]
  exact Finset.card_erase_lt_of_mem
    ((mem_liveVariables rho selected).2 live)

/-- If the second assignment fixes only variables left live by the first,
their fixed-variable counts add under refinement. -/
theorem fixedCount_refine_eq_add
    (rho sigma : PartialAssignment n)
    (newFixes : sigma.fixedVariables ⊆ rho.liveVariables) :
    (rho.refine sigma).fixedCount = rho.fixedCount + sigma.fixedCount := by
  have disjoint : Disjoint rho.fixedVariables sigma.fixedVariables := by
    rw [Finset.disjoint_left]
    intro index fixedByRho fixedBySigma
    have liveByRho := newFixes fixedBySigma
    exact (Finset.disjoint_left.mp
      (disjoint_liveVariables_fixedVariables rho)) liveByRho fixedByRho
  rw [fixedCount, fixedVariables_refine,
    Finset.card_union_of_disjoint disjoint, fixedCount, fixedCount]

/-- Under a refinement that fixes only live variables, the decrease in live
count is exactly the second assignment's fixed count. -/
theorem liveCount_refine_add_fixedCount_eq
    (rho sigma : PartialAssignment n)
    (newFixes : sigma.fixedVariables ⊆ rho.liveVariables) :
    (rho.refine sigma).liveCount + sigma.fixedCount = rho.liveCount := by
  have refinedPartition := liveCount_add_fixedCount (rho.refine sigma)
  have sourcePartition := liveCount_add_fixedCount rho
  rw [fixedCount_refine_eq_add rho sigma newFixes] at refinedPartition
  omega

/-- Inputs that agree on every live variable become equal after applying the
partial assignment. -/
theorem apply_eq_of_agree_live
    (rho : PartialAssignment n)
    {left right : Fin n -> Bool}
    (agree : forall index, index ∈ rho.liveVariables ->
      left index = right index) :
    rho.apply left = rho.apply right := by
  funext index
  cases fixed : rho index with
  | none =>
      rw [apply_of_live rho left fixed, apply_of_live rho right fixed]
      exact agree index ((mem_liveVariables rho index).2 fixed)
  | some value =>
      rw [apply_of_fixed rho left fixed, apply_of_fixed rho right fixed]

end PartialAssignment

namespace ScalarFunction

/-- Restrict a scalar Boolean function by a partial assignment. -/
def restrict
    (function : ScalarFunction Bool n)
    (rho : PartialAssignment n) : ScalarFunction Bool n :=
  fun input => function (rho.apply input)

@[simp] theorem restrict_apply
    (function : ScalarFunction Bool n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    function.restrict rho input = function (rho.apply input) := rfl

@[simp] theorem restrict_empty
    (function : ScalarFunction Bool n) :
    function.restrict PartialAssignment.empty = function := rfl

/-- Restricting twice agrees with restriction by sequential refinement. -/
theorem restrict_refine
    (function : ScalarFunction Bool n)
    (rho sigma : PartialAssignment n) :
    (function.restrict rho).restrict sigma =
      function.restrict (rho.refine sigma) := by
  funext input
  rw [restrict_apply, restrict_apply, restrict_apply,
    PartialAssignment.apply_refine]

/-- A restricted scalar function depends only on variables left live. -/
theorem restrict_dependsOnlyOn_live
    (function : ScalarFunction Bool n)
    (rho : PartialAssignment n) :
    DependsOnlyOn (function.restrict rho) rho.liveVariables := by
  intro left right agree
  exact congrArg function (rho.apply_eq_of_agree_live agree)

end ScalarFunction

namespace Target

/-- Restrict every output of a Boolean target by a partial assignment. -/
def restrict
    (target : Target Bool n m)
    (rho : PartialAssignment n) : Target Bool n m :=
  target.substitute rho.toInputSubstitution

@[simp] theorem restrict_apply
    (target : Target Bool n m)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    target.restrict rho input = target (rho.apply input) := rfl

@[simp] theorem restrict_empty
    (target : Target Bool n m) :
    target.restrict PartialAssignment.empty = target := rfl

/-- Restricting a target twice agrees with sequential refinement. -/
theorem restrict_refine
    (target : Target Bool n m)
    (rho sigma : PartialAssignment n) :
    (target.restrict rho).restrict sigma =
      target.restrict (rho.refine sigma) := by
  funext input
  rw [restrict_apply, restrict_apply, restrict_apply,
    PartialAssignment.apply_refine]

/-- A restricted target depends only on variables left live. -/
theorem restrict_dependsOnlyOn_live
    (target : Target Bool n m)
    (rho : PartialAssignment n) :
    DependsOnlyOn (target.restrict rho) rho.liveVariables := by
  intro left right agree
  change target (rho.apply left) = target (rho.apply right)
  exact congrArg target (rho.apply_eq_of_agree_live agree)

end Target

end Algebraic
