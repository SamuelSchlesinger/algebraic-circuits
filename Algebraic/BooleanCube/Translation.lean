import Algebraic.BooleanCube.Star

/-!
# Translation of truth tables and incident faces

XOR by a fixed truth table is an involutive Hamming isometry. It carries
incident faces to incident faces with the same set of free coordinates.
-/

namespace Algebraic.BooleanCube

variable {ι : Type*}

/-- Translate a Boolean cube by coordinatewise XOR. -/
def translate (shift vertex : ι → Bool) : ι → Bool := fun i => Bool.xor (vertex i) (shift i)

/-- Every XOR translation is its own inverse. -/
@[simp] theorem translate_translate (shift vertex : ι → Bool) :
    translate shift (translate shift vertex) = vertex := by
  funext i
  simp [translate]

/-- Translating zero gives the translation center. -/
@[simp] theorem translate_zero (shift : ι → Bool) : translate shift (fun _ => false) = shift := by
  funext i
  simp [translate]

/-- XOR translation is an equivalence of Boolean vertices. -/
def translateEquiv (shift : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun := translate shift
  invFun := translate shift
  left_inv := translate_translate shift
  right_inv := translate_translate shift

/-- XOR translation preserves exact Hamming distance. -/
theorem hammingDist_translate [Fintype ι] (shift left right : ι → Bool) :
    hammingDist (translate shift left) (translate shift right) = hammingDist left right := by
  unfold hammingDist
  congr 1
  apply Finset.ext
  intro i
  cases hl : left i <;> cases hr : right i <;> simp [translate, hl, hr]

/-- Translating a face changes its center and preserves its direction set. -/
theorem corner_translate [DecidableEq ι] (shift base : ι → Bool) (directions : Finset ι) :
    corner (translate shift base) directions = translate shift (corner base directions) := by
  funext i
  by_cases member : i ∈ directions <;>
    cases hb : base i <;> cases hs : shift i <;> simp [corner, translate, member, hb, hs]

/-- A cost bound for translated vertices extends to every incident-face birth time. -/
theorem faceBirth_translate_le [DecidableEq ι] (cost : (ι → Bool) → Nat)
    (shift base : ι → Bool) (overhead : Nat)
    (bounded : ∀ vertex, cost (translate shift vertex) ≤ cost vertex + overhead)
    (directions : Finset ι) :
    faceBirth cost (translate shift base) directions ≤ faceBirth cost base directions + overhead := by
  apply Finset.sup_le
  intro subset member
  rw [corner_translate]
  exact (bounded _).trans (Nat.add_le_add_right
    (cost_corner_le_faceBirth cost base (Finset.mem_powerset.mp member)) overhead)

/-- Uniform translation overhead gives an inclusion of link filtrations. -/
theorem link_subset_translate [DecidableEq ι] (cost : (ι → Bool) → Nat)
    (shift base : ι → Bool) (budget overhead : Nat)
    (bounded : ∀ vertex, cost (translate shift vertex) ≤ cost vertex + overhead) :
    link {vertex | cost vertex ≤ budget} base ⊆
      link {vertex | cost vertex ≤ budget + overhead} (translate shift base) := by
  intro directions member
  apply (mem_link_sublevel_iff _ _ _ _).mpr
  exact (faceBirth_translate_le cost shift base overhead bounded directions).trans
    (Nat.add_le_add_right ((mem_link_sublevel_iff _ _ _ _).mp member) overhead)

end Algebraic.BooleanCube
