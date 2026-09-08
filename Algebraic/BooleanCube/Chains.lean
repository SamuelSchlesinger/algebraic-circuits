import Algebraic.BooleanCube.Face
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Oriented finite cubical chains

The ambient chain module has one basis vector for each cube face, in all
degrees. The boundary uses the usual product orientation. Prefix erasure
has an explicit chain homotopy, so its support and dimension can be counted.
-/

namespace Algebraic.BooleanCube

/-- Finite formal linear combinations of cube faces. -/
abbrev Chains (R : Type*) [Zero R] (n : Nat) := Face n →₀ R

namespace Chains

variable (R : Type*) [CommRing R]

/-- Prepend a coordinate to every face of a chain. -/
noncomputable def push (bit : Option Bool) : Chains R n →ₗ[R] Chains R (n + 1) :=
  Finsupp.lmapDomain R R (Face.cons bit)

/-- Pushing a basis chain prepends its face coordinate. -/
theorem push_single (bit : Option Bool) (face : Face n) (a : R) :
    push R bit (Finsupp.single face a) = Finsupp.single (face.cons bit) a := by
  simp [push, Finsupp.lmapDomain_apply]

/-- The oriented cubical boundary, acting on the ambient graded module. -/
noncomputable def boundary : (n : Nat) → Chains R n →ₗ[R] Chains R n
  | 0 => 0
  | n + 1 => Finsupp.linearCombination R (fun face =>
      let tail := Finsupp.single (Fin.tail face) (1 : R)
      match face 0 with
      | some bit => push R (some bit) (boundary n tail)
      | none => push R (some true) tail - push R (some false) tail -
          push R none (boundary n tail))

/-- The projection to the zero vertex, with zero on positive-dimensional faces. -/
noncomputable def augmentation : (n : Nat) → Chains R n →ₗ[R] Chains R n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination R (fun face =>
      match face 0 with
      | some _ => push R (some false) (augmentation n (Finsupp.single (Fin.tail face) 1))
      | none => 0)

/-- The prism operator for the coherent prefix-erasure contraction. -/
noncomputable def prism : (n : Nat) → Chains R n →ₗ[R] Chains R n
  | 0 => 0
  | n + 1 => Finsupp.linearCombination R (fun face =>
      let tail := Finsupp.single (Fin.tail face) (1 : R)
      match face 0 with
      | some false => push R (some false) (prism n tail)
      | some true => push R none tail + push R (some false) (prism n tail)
      | none => 0)

/-- A fixed coordinate commutes with the boundary. -/
@[simp] theorem boundary_push_fixed (bit : Bool) (chain : Chains R n) :
    boundary R (n + 1) (push R (some bit) chain) =
      push R (some bit) (boundary R n chain) := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single face a =>
      have scale : Finsupp.single face a = a • Finsupp.single face (1 : R) := by simp
      rw [scale]
      simp only [map_smul]
      congr 1
      simp [push_single, boundary, Face.cons, Finsupp.linearCombination_single]

/-- The product boundary of an interval has its two endpoints and the signed tail boundary. -/
@[simp] theorem boundary_push_free (chain : Chains R n) :
    boundary R (n + 1) (push R none chain) =
      push R (some true) chain - push R (some false) chain - push R none (boundary R n chain) := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; abel
  | single face a =>
      have scale : Finsupp.single face a = a • Finsupp.single face (1 : R) := by simp
      rw [scale]
      simp only [map_smul]
      simp [push_single, boundary, Face.cons, Finsupp.linearCombination_single, smul_sub]

/-- Augmentation sends either fixed coordinate to the zero endpoint. -/
@[simp] theorem augmentation_push_fixed (bit : Bool) (chain : Chains R n) :
    augmentation R (n + 1) (push R (some bit) chain) =
      push R (some false) (augmentation R n chain) := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single face a =>
      have scale : Finsupp.single face a = a • Finsupp.single face (1 : R) := by simp
      rw [scale]
      simp only [map_smul]
      congr 1
      simp [push_single, augmentation, Face.cons, Finsupp.linearCombination_single]

/-- Augmentation kills faces with a free first coordinate. -/
@[simp] theorem augmentation_push_free (chain : Chains R n) :
    augmentation R (n + 1) (push R none chain) = 0 := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single face a => simp [push_single, augmentation, Face.cons, Finsupp.linearCombination_single]

/-- At the zero endpoint the prism continues in the remaining coordinates. -/
@[simp] theorem prism_push_false (chain : Chains R n) :
    prism R (n + 1) (push R (some false) chain) =
      push R (some false) (prism R n chain) := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single face a =>
      have scale : Finsupp.single face a = a • Finsupp.single face (1 : R) := by simp
      rw [scale]
      simp only [map_smul]
      congr 1
      simp [push_single, prism, Face.cons, Finsupp.linearCombination_single]

/-- At the one endpoint the prism first inserts an interval, then continues at zero. -/
@[simp] theorem prism_push_true (chain : Chains R n) :
    prism R (n + 1) (push R (some true) chain) =
      push R none chain + push R (some false) (prism R n chain) := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; abel
  | single face a =>
      have scale : Finsupp.single face a = a • Finsupp.single face (1 : R) := by simp
      rw [scale]
      simp only [map_smul]
      simp [push_single, prism, Face.cons, Finsupp.linearCombination_single, smul_add]

/-- A face with a free first coordinate has zero prism. -/
@[simp] theorem prism_push_free (chain : Chains R n) :
    prism R (n + 1) (push R none chain) = 0 := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single face a => simp [push_single, prism, Face.cons, Finsupp.linearCombination_single]

/-- Cubical boundary squares to zero. -/
theorem boundary_boundary (n : Nat) (chain : Chains R n) :
    boundary R n (boundary R n chain) = 0 := by
  induction n with
  | zero => simp [boundary]
  | succ n ih =>
      induction chain using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp [ha, hb]
      | single face a =>
          rw [← Face.cons_tail face, ← push_single]
          cases h : face 0 with
          | some bit => simp [ih]
          | none => simp [map_sub, ih]

/-- The prism satisfies the chain-homotopy identity `d h + h d = id - augmentation`. -/
theorem boundary_prism_add_prism_boundary (n : Nat) (chain : Chains R n) :
    boundary R n (prism R n chain) + prism R n (boundary R n chain) =
      chain - augmentation R n chain := by
  induction n with
  | zero => simp [boundary, prism, augmentation]
  | succ n ih =>
      induction chain using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp only [map_add]
          calc
            _ = (boundary R (n + 1) (prism R (n + 1) a) + prism R (n + 1) (boundary R (n + 1) a)) +
                (boundary R (n + 1) (prism R (n + 1) b) + prism R (n + 1) (boundary R (n + 1) b)) := by abel
            _ = _ := by rw [ha, hb]; abel
      | single face a =>
          rw [← Face.cons_tail face, ← push_single]
          cases h : face 0 with
          | none => simp [map_sub]
          | some bit =>
              cases bit
              · simpa only [prism_push_false, boundary_push_fixed, augmentation_push_fixed,
                  ← map_add, ← map_sub] using congrArg (push R (some false)) (ih (Finsupp.single (Fin.tail face) a))
              · have hi := congrArg (push R (some false)) (ih (Finsupp.single (Fin.tail face) a))
                simp only [map_add, map_sub] at hi
                simp only [prism_push_true, boundary_push_fixed, augmentation_push_fixed,
                  boundary_push_free, map_add]
                calc
                  _ = push R (some true) (Finsupp.single (Fin.tail face) a) -
                      push R (some false) (Finsupp.single (Fin.tail face) a) +
                      (push R (some false) (boundary R n (prism R n (Finsupp.single (Fin.tail face) a))) +
                      push R (some false) (prism R n (boundary R n (Finsupp.single (Fin.tail face) a)))) := by abel
                  _ = _ := by rw [hi]; abel

end Chains
end Algebraic.BooleanCube
