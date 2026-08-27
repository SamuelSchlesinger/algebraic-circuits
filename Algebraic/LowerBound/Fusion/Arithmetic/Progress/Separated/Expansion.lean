import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated
import Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial

/-!
# Exact monomial expansions under polynomial substitution

This file supplies the algebraic half of the separated-monomial enrichment
argument.  Over natural coefficients there is no cancellation: the support of
`bind₁ substitution polynomial` is exactly the union, over source monomials,
of their individual substitution expansions.

The key factor lemma is independent of the particular substitution.  If a
source monomial divides the product of two source monomials, then some monomial
in its expansion divides the product of any chosen monomials in the two other
expansions.  This packages the divisibility step used when pulling separation
certificates backward.
-/

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Expansion

open scoped Pointwise

noncomputable section

variable {SourceVar : Type u}
variable {TargetVar : Type v}
variable {Index : Type w}

/-- The polynomial obtained by substituting into one coefficient-one source
monomial. -/
def monomialExpansion
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (exponent : SourceVar →₀ ℕ) : MvPolynomial TargetVar ℕ :=
  MvPolynomial.bind₁ substitution (MvPolynomial.monomial exponent 1)

/-- Exact support of a finite sum over natural coefficients. -/
theorem support_finset_sum
    [DecidableEq TargetVar]
    (indices : Finset Index)
    (polynomial : Index → MvPolynomial TargetVar ℕ) :
    (∑ index ∈ indices, polynomial index).support =
      indices.biUnion fun index => (polynomial index).support := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent,
        MonotonePolynomial.polynomial_support_add,
        inductionHypothesis]
      simp

/-- Multiplication by a positive natural scalar does not change polynomial
support. -/
theorem support_C_mul_of_pos
    [DecidableEq TargetVar]
    (coefficient : Nat)
    (positive : 0 < coefficient)
    (polynomial : MvPolynomial TargetVar ℕ) :
    (MvPolynomial.C coefficient * polynomial).support =
      polynomial.support := by
  rw [MonotonePolynomial.polynomial_support_mul,
    MvPolynomial.support_C]
  rw [if_neg (Nat.ne_of_gt positive)]
  ext exponent
  constructor
  · intro present
    rw [Finset.mem_add] at present
    obtain ⟨zero, zeroPresent, other, otherPresent, equal⟩ := present
    have zeroEqual : zero = 0 := Finset.mem_singleton.mp zeroPresent
    subst zero
    have otherEqual : other = exponent := by simpa using equal
    simpa [otherEqual] using otherPresent
  · intro present
    rw [Finset.mem_add]
    exact ⟨0, Finset.mem_singleton_self 0,
      exponent, present, zero_add exponent⟩

/-- A supported source coefficient contributes the same support as the
corresponding coefficient-one monomial. -/
theorem support_bind₁_monomial_coeff
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (exponent : SourceVar →₀ ℕ)
    (present : exponent ∈ polynomial.support) :
    (MvPolynomial.bind₁ substitution
      (MvPolynomial.monomial exponent
        (MvPolynomial.coeff exponent polynomial))).support =
      (monomialExpansion substitution exponent).support := by
  have coefficientPositive :
      0 < MvPolynomial.coeff exponent polynomial :=
    Nat.pos_of_ne_zero (MvPolynomial.mem_support_iff.mp present)
  have monomialFactorization :
      MvPolynomial.monomial exponent
          (MvPolynomial.coeff exponent polynomial) =
          MvPolynomial.C (MvPolynomial.coeff exponent polynomial) *
          MvPolynomial.monomial exponent 1 := by
    symm
    simpa using
      (MvPolynomial.C_mul_monomial
        (σ := SourceVar) (R := Nat)
        (a := MvPolynomial.coeff exponent polynomial)
        (s := exponent) (a' := 1))
  rw [monomialFactorization, map_mul]
  simp only [MvPolynomial.bind₁_C_right]
  exact support_C_mul_of_pos _ coefficientPositive _

/-- Exact support decomposition of a monotone polynomial substitution. -/
theorem support_bind₁
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (MvPolynomial.bind₁ substitution polynomial).support =
      polynomial.support.biUnion fun exponent =>
        (monomialExpansion substitution exponent).support := by
  conv_lhs =>
    rw [polynomial.as_sum]
    simp only [map_sum]
  rw [support_finset_sum]
  apply Finset.biUnion_congr rfl
  intro exponent present
  exact support_bind₁_monomial_coeff substitution polynomial exponent present

/-- Membership in one source-monomial expansion. -/
def IsNeighbor
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (source : SourceVar →₀ ℕ)
    (target : TargetVar →₀ ℕ) : Prop :=
  target ∈ (monomialExpansion substitution source).support

/-- Every monomial after substitution has a source neighbor. -/
theorem exists_source_of_mem_support_bind₁
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (target : TargetVar →₀ ℕ)
    (present : target ∈
      (MvPolynomial.bind₁ substitution polynomial).support) :
    ∃ source ∈ polynomial.support,
      IsNeighbor substitution source target := by
  rw [support_bind₁, Finset.mem_biUnion] at present
  exact present

/-- Every neighbor of a supported source monomial survives in the whole
substituted polynomial. -/
theorem mem_support_bind₁_of_neighbor
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (source : SourceVar →₀ ℕ)
    (sourcePresent : source ∈ polynomial.support)
    (target : TargetVar →₀ ℕ)
    (neighbor : IsNeighbor substitution source target) :
    target ∈ (MvPolynomial.bind₁ substitution polynomial).support := by
  rw [support_bind₁, Finset.mem_biUnion]
  exact ⟨source, sourcePresent, neighbor⟩

/-- Expansion turns addition of exponent vectors into multiplication of
their expansion polynomials. -/
theorem monomialExpansion_add
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (left right : SourceVar →₀ ℕ) :
    monomialExpansion substitution (left + right) =
      monomialExpansion substitution left *
        monomialExpansion substitution right := by
  simpa [monomialExpansion] using
    (map_mul (MvPolynomial.bind₁ substitution)
      (MvPolynomial.monomial left 1)
      (MvPolynomial.monomial right 1))

/-- If `middle` divides `left * right`, every chosen pair of expansion
neighbors contains some expansion neighbor of `middle`. -/
theorem exists_neighbor_le_add
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (left right middle : SourceVar →₀ ℕ)
    (middleLe : middle ≤ left + right)
    (leftTarget rightTarget : TargetVar →₀ ℕ)
    (leftNeighbor : IsNeighbor substitution left leftTarget)
    (rightNeighbor : IsNeighbor substitution right rightTarget) :
    ∃ middleTarget,
      IsNeighbor substitution middle middleTarget ∧
        middleTarget ≤ leftTarget + rightTarget := by
  let remainder := left + right - middle
  have middle_add_remainder : middle + remainder = left + right := by
    dsimp [remainder]
    rw [add_comm, tsub_add_cancel_of_le middleLe]
  have productEquality :
      monomialExpansion substitution left *
          monomialExpansion substitution right =
        monomialExpansion substitution middle *
          monomialExpansion substitution remainder := by
    rw [← monomialExpansion_add, ← monomialExpansion_add,
      middle_add_remainder]
  have productPresent : leftTarget + rightTarget ∈
      (monomialExpansion substitution left *
        monomialExpansion substitution right).support := by
    rw [MonotonePolynomial.polynomial_support_mul, Finset.mem_add]
    exact ⟨leftTarget, leftNeighbor, rightTarget, rightNeighbor, rfl⟩
  rw [productEquality,
    MonotonePolynomial.polynomial_support_mul,
    Finset.mem_add] at productPresent
  obtain ⟨middleTarget, middleNeighbor, remainderTarget, _, equal⟩ :=
    productPresent
  refine ⟨middleTarget, middleNeighbor, ?_⟩
  rw [← equal]
  intro coordinate
  exact Nat.le_add_right _ _

/-- Origins chosen for one separated target set.  Rigidity says that a chosen
target monomial has exactly the selected source origin among the ambient
source support.  The score field records the permitted loss after identifying
the chosen origins. -/
structure OriginSelection
    [DecidableEq SourceVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (selected : Finset (TargetVar →₀ ℕ))
    (loss : Nat) where
  /-- Source origin selected for each target monomial. -/
  origin : ↥selected → SourceVar →₀ ℕ
  /-- Every selected origin belongs to the source support. -/
  origin_mem : ∀ target, origin target ∈ polynomial.support
  /-- Each selected target is a neighbor of its selected origin. -/
  neighbor : ∀ target,
    IsNeighbor substitution (origin target) target.1
  /-- No other ambient source monomial produces the selected target. -/
  rigid : ∀ target other,
    other ∈ polynomial.support →
      IsNeighbor substitution other target.1 →
        other = origin target
  /-- Identifying origins loses at most the allowed separation score. -/
  score : selected.card - 1 ≤
    (selected.attach.image origin).card - 1 + loss

/-- Rigid origins pull a separated target set back to a separated source
set. -/
theorem OriginSelection.prior_isSeparated
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    {substitution : SourceVar → MvPolynomial TargetVar ℕ}
    {polynomial : MvPolynomial SourceVar ℕ}
    {selected : Finset (TargetVar →₀ ℕ)}
    {loss : Nat}
    (selection : OriginSelection substitution polynomial selected loss)
    (separated : IsSeparated
      (MvPolynomial.bind₁ substitution polynomial).support selected) :
    IsSeparated polynomial.support
      (selected.attach.image selection.origin) := by
  classical
  constructor
  · intro source sourcePresent
    obtain ⟨target, _, targetEqual⟩ := Finset.mem_image.mp sourcePresent
    rw [← targetEqual]
    exact selection.origin_mem target
  · intro left leftPresent right rightPresent middle middlePresent middleLe
    obtain ⟨leftTarget, _, leftEqual⟩ := Finset.mem_image.mp leftPresent
    obtain ⟨rightTarget, _, rightEqual⟩ := Finset.mem_image.mp rightPresent
    have middleLeOrigins :
        middle ≤ selection.origin leftTarget +
          selection.origin rightTarget := by
      simpa [leftEqual, rightEqual] using middleLe
    obtain ⟨middleTarget, middleNeighbor, middleTargetLe⟩ :=
      exists_neighbor_le_add substitution
        (selection.origin leftTarget) (selection.origin rightTarget)
        middle middleLeOrigins leftTarget.1 rightTarget.1
        (selection.neighbor leftTarget) (selection.neighbor rightTarget)
    have middleTargetPresent : middleTarget ∈
        (MvPolynomial.bind₁ substitution polynomial).support :=
      mem_support_bind₁_of_neighbor substitution polynomial middle
        middlePresent middleTarget middleNeighbor
    rcases separated.2 leftTarget.1 leftTarget.2
        rightTarget.1 rightTarget.2 middleTarget middleTargetPresent
        middleTargetLe with middleIsLeft | middleIsRight
    · left
      have middleIsOrigin : middle = selection.origin leftTarget :=
        selection.rigid leftTarget middle middlePresent (by
          simpa [middleIsLeft] using middleNeighbor)
      exact middleIsOrigin.trans leftEqual
    · right
      have middleIsOrigin : middle = selection.origin rightTarget :=
        selection.rigid rightTarget middle middlePresent (by
          simpa [middleIsRight] using middleNeighbor)
      exact middleIsOrigin.trans rightEqual

/-- If every separated target set admits rigid origins with a fixed loss,
then the substitution supplies the abstract separation pullback certificate. -/
theorem pullback_of_originSelections
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (loss : Nat)
    (selections : ∀ selected,
      IsSeparated
          (MvPolynomial.bind₁ substitution polynomial).support selected →
        OriginSelection substitution polynomial selected loss) :
    Pullback polynomial.support
      (MvPolynomial.bind₁ substitution polynomial).support loss := by
  constructor
  intro selected separated
  let selection := selections selected separated
  exact ⟨selected.attach.image selection.origin,
    selection.prior_isSeparated separated, selection.score⟩

end
end Expansion
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
