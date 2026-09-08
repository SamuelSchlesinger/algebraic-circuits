import Algebraic.Basis.DeMorgan.StarDuality

/-!
# Downstream reduced simplicial homology checks

A triangle boundary has a nonzero degree-one homology class. These checks also
exercise the transpose differential and the augmented degree convention.
-/

open Algebraic.BooleanCube Algebraic.BooleanCube.SimplicialF2

private def triangleFaces : Set (Finset (Fin 3)) := {support | support.card ≤ 2}

private def triangleCycle : Chains (Fin 3) := fun support => if support.card = 2 then 1 else 0

private theorem triangleCycle_mem : triangleCycle ∈ cycles triangleFaces 2 := by
  change ((∀ support, support ∉ triangleFaces → triangleCycle support = 0) ∧
    (∀ support, (support.card : ℤ) ≠ 2 → triangleCycle support = 0)) ∧ boundary triangleCycle = 0
  unfold triangleFaces triangleCycle
  decide

private theorem triangleCycle_not_boundary : triangleCycle ∉ boundaries triangleFaces 2 := by
  rintro ⟨filling, member, same⟩
  have vanishes : filling = 0 := by
    ext support
    by_cases small : support.card ≤ 2
    · apply member.2
      have bound : (support.card : ℤ) ≤ 2 := by exact_mod_cast small
      omega
    · exact member.1 support small
  rw [vanishes, map_zero] at same
  have coefficient := congrFun same ({0, 1} : Finset (Fin 3))
  norm_num [triangleCycle] at coefficient

example : Nontrivial (ReducedHomology triangleFaces 1) := by
  let cycle : cycles triangleFaces 2 := ⟨triangleCycle, triangleCycle_mem⟩
  let projection := ((boundaries triangleFaces 2).comap (cycles triangleFaces 2).subtype).mkQ
  refine ⟨⟨projection cycle, 0, ?_⟩⟩
  intro equal
  have member := (Submodule.Quotient.mk_eq_zero
    ((boundaries triangleFaces 2).comap (cycles triangleFaces 2).subtype)).mp equal
  exact triangleCycle_not_boundary member

example (left right : Finset (Fin 3)) :
    coboundary (fun support => if support = left then (1 : ZMod 2) else 0) right =
      boundary (fun support => if support = right then (1 : ZMod 2) else 0) left := by
  revert left right
  decide

example : (∅ : Finset (Fin 3)) ∈ ({∅} : Set (Finset (Fin 3))) ∧
    (∅ : Finset (Fin 3)) ∉ (∅ : Set (Finset (Fin 3))) := by simp

noncomputable example : ReducedHomology ({∅} : Set (Finset (Fin 3))) (-1) ≃ₗ[ZMod 2]
    ReducedCohomology (Complex.dual ({∅} : Set (Finset (Fin 3)))) 1 :=
  reducedAlexanderDuality (0 : Fin 3) {∅} (by
    intro left right included member
    have empty : right = ∅ := member
    rw [empty] at included
    simpa using Finset.subset_empty.mp included) (-1)

example : FiniteDimensional (ZMod 2) (ReducedHomology triangleFaces 1) := inferInstance

example : FiniteDimensional (ZMod 2) (ReducedCohomology triangleFaces 1) := inferInstance
