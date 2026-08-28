import Algebraic.Basis.AndOr

/-!
# Preimages as homomorphisms of set interpretations

Taking preimages under a map of ambient types commutes with intersection and
union, so it is a homomorphism between the set interpretations of the AND/OR
basis.  The special case of the inclusion of a subset restricts every set to
that subset: this is how a Boolean function is restricted to a subcube, and it
lets a single circuit be observed through any chosen restriction.
-/

namespace Algebraic
namespace AndOr

/-- Preimage under a map is a homomorphism of set interpretations. -/
def preimageHomomorphism (f : Δ → Γ) :
    Homomorphism (setInterpretation Γ) (setInterpretation Δ) where
  map set := f ⁻¹' set
  homomorphic := by
    intro op input
    cases op <;> simp [setInterpretation, Set.preimage_inter, Set.preimage_union]

@[simp] theorem preimageHomomorphism_map
    (f : Δ → Γ) (set : Set Γ) :
    (preimageHomomorphism f).map set = f ⁻¹' set := rfl

/-- Restricting sets to a subset of the ambient type. -/
abbrev restrictHomomorphism (subset : Set Γ) :
    Homomorphism (setInterpretation Γ) (setInterpretation subset) :=
  preimageHomomorphism Subtype.val

end AndOr
end Algebraic
