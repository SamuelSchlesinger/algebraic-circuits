import Algebraic.BooleanCube.AlexanderDual
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Pi
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.BigOperators.Pi

/-!
# Augmented simplicial chains over F2

Coefficients are indexed by all subsets of a finite ground set, including the
empty subset. The usual boundary deletes a vertex; its transpose adds one.
Characteristic two removes orientation signs. Grading is by cardinality, so
cardinality zero represents reduced degree `-1`.
-/

namespace Algebraic.BooleanCube.SimplicialF2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ambient augmented chain module, containing all cardinality degrees. -/
abbrev Chains (ι : Type*) := Finset ι → ZMod 2

/-- The simplicial boundary in coefficient coordinates. -/
def boundary : Chains ι →ₗ[ZMod 2] Chains ι where
  toFun chain support := ∑ i, if i ∈ support then 0 else chain (insert i support)
  map_add' left right := by
    ext support
    change (∑ i, if i ∈ support then 0 else left (insert i support) + right (insert i support)) = _
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases member : i ∈ support <;> simp [member]
  map_smul' scalar chain := by
    ext support
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases member : i ∈ support <;> simp [member]

/-- The transpose boundary, before restriction to a complex. -/
def coboundary : Chains ι →ₗ[ZMod 2] Chains ι where
  toFun chain support := ∑ i ∈ support, chain (support.erase i)
  map_add' left right := by ext support; simp [Finset.sum_add_distrib]
  map_smul' scalar chain := by ext support; simp [Finset.mul_sum]

/-- Complementation reverses the Boolean lattice on chain coefficients. -/
def complement : Chains ι ≃ₗ[ZMod 2] Chains ι where
  toFun chain support := chain supportᶜ
  invFun chain support := chain supportᶜ
  left_inv chain := by ext; simp
  right_inv chain := by ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The boundary coefficient sums over one-vertex extensions. -/
theorem boundary_apply (chain : Chains ι) (support : Finset ι) :
    boundary chain support = ∑ i, if i ∈ support then 0 else chain (insert i support) := rfl

omit [Fintype ι] in
/-- The coboundary coefficient sums over one-vertex deletions. -/
theorem coboundary_apply (chain : Chains ι) (support : Finset ι) :
    coboundary chain support = ∑ i ∈ support, chain (support.erase i) := rfl

/-- Complementation reads the coefficient at the complementary support. -/
@[simp] theorem complement_apply (chain : Chains ι) (support : Finset ι) :
    complement chain support = chain supportᶜ := rfl

/-- Complementation is involutive on chains. -/
@[simp] theorem complement_complement (chain : Chains ι) : complement (complement chain) = chain := by
  ext; simp

/-- Every two-vertex deletion occurs twice, so the boundary squares to zero. -/
@[simp] theorem boundary_boundary (chain : Chains ι) : boundary (boundary chain) = 0 := by
  ext support
  let term : ι × ι → ZMod 2 := fun pair =>
    if pair.1 ∈ support ∨ pair.2 ∈ support ∨ pair.1 = pair.2 then 0
    else chain (insert pair.2 (insert pair.1 support))
  have expansion : boundary (boundary chain) support = ∑ pair, term pair := by
    rw [boundary_apply]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    by_cases member : i ∈ support
    · simp [term, member]
    · simp only [member, ↓reduceIte, boundary_apply]
      apply Finset.sum_congr rfl
      intro j _
      simp [term, member, eq_comm, or_comm]
  rw [expansion]
  apply Finset.sum_ninvolution Prod.swap
  · rintro ⟨i, j⟩
    simp only [term, Prod.swap_prod_mk]
    by_cases excluded : i ∈ support ∨ j ∈ support ∨ i = j
    · have reverse : j ∈ support ∨ i ∈ support ∨ j = i := by tauto
      simp [excluded, reverse]
    · have reverse : ¬(j ∈ support ∨ i ∈ support ∨ j = i) := by tauto
      simp [excluded, reverse, Finset.insert_comm, CharTwo.add_self_eq_zero]
  · rintro ⟨i, j⟩ nonzero same
    have equal : i = j := congrArg Prod.snd same
    exact nonzero (by simp [term, equal])
  · intro pair; exact Finset.mem_univ _
  · intro pair; exact Prod.swap_swap pair

/-- Complementing the lattice exchanges relative boundary and transpose coboundary. -/
theorem coboundary_complement (chain : Chains ι) :
    coboundary (complement chain) = complement (boundary chain) := by
  ext support
  simp only [coboundary_apply, complement_apply, boundary_apply, Finset.mem_compl,
    Finset.compl_erase, ite_not]
  calc
    _ = ∑ i ∈ support, if i ∈ support then chain (insert i supportᶜ) else 0 :=
      Finset.sum_congr rfl (by intro i member; simp [member])
    _ = _ := Finset.sum_subset (Finset.subset_univ support) (by intro i _ absent; simp [absent])

/-- The transpose also squares to zero. -/
@[simp] theorem coboundary_coboundary (chain : Chains ι) : coboundary (coboundary chain) = 0 := by
  have identity := coboundary_complement (complement chain)
  rw [complement_complement] at identity
  rw [identity, coboundary_complement, boundary_boundary, map_zero]

/-- Coning at a chosen vertex, including the empty simplex. -/
def cone (vertex : ι) : Chains ι →ₗ[ZMod 2] Chains ι where
  toFun chain support := if vertex ∈ support then chain (support.erase vertex) else 0
  map_add' left right := by ext support; by_cases member : vertex ∈ support <;> simp [member]
  map_smul' scalar chain := by ext support; by_cases member : vertex ∈ support <;> simp [member]

omit [Fintype ι] in
/-- Coning includes a face precisely when it contains the cone vertex. -/
@[simp] theorem cone_apply (vertex : ι) (chain : Chains ι) (support : Finset ι) :
    cone vertex chain support = if vertex ∈ support then chain (support.erase vertex) else 0 := rfl

/-- Adding the cone boundary and the cone of the boundary gives the original chain. -/
theorem boundary_cone_add_cone_boundary (vertex : ι) (chain : Chains ι) :
    boundary (cone vertex chain) + cone vertex (boundary chain) = chain := by
  ext support
  by_cases member : vertex ∈ support
  · simp only [Pi.add_apply, cone_apply, member, ↓reduceIte, boundary_apply]
    rw [← Finset.sum_add_distrib, Finset.sum_eq_single vertex]
    · simp [member]
    · intro i _ different
      by_cases present : i ∈ support
      · simp [present, Finset.mem_erase, different]
      · simp [present, member, Finset.erase_insert_of_ne different, CharTwo.add_self_eq_zero]
    · simp
  · simp only [Pi.add_apply, cone_apply, member, ↓reduceIte, add_zero, boundary_apply]
    rw [Finset.sum_eq_single vertex]
    · simp [member]
    · intro i _ different
      simp [Ne.symm different, member]
    · simp

end Algebraic.BooleanCube.SimplicialF2
