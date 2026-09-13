import Algebraic.BooleanCube.Chains

/-!
# Support of cubical boundaries and erasure prisms

Boundary faces are codimension-one subfaces. Every prism face has one more
free coordinate, and every vertex of it is a prefix erasure of an original
vertex. These support statements carry the circuit budget into finite chains.
-/

namespace Algebraic.BooleanCube

namespace Face

/-- Prefix erasure after the first coordinate erases that coordinate completely. -/
theorem erase_cons_succ (bit : Bool) (vertex : Fin n → Bool) (threshold : Nat) :
    erase Fin.val (threshold + 1) (Fin.cons bit vertex) =
      Fin.cons false (erase Fin.val threshold vertex) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [erase, patch]
  · simp [erase, patch]

/-- Containment in a face decomposes at the first coordinate. -/
theorem contains_iff_head_tail (bit : Option Bool) (face : Face n)
    (vertex : Fin (n + 1) → Bool) :
    (face.cons bit).Contains vertex ↔
      (bit = none ∨ bit = some (vertex 0)) ∧ face.Contains (Fin.tail vertex) := by
  simpa only [Fin.cons_self_tail] using contains_cons bit face (vertex 0) (Fin.tail vertex)

end Face

namespace Chains

variable (R : Type*) [CommRing R]

/-- A face in the support of a pushed chain comes from a face in the original support. -/
theorem support_push {bit : Option Bool} {chain : Chains R n} {face : Face (n + 1)}
    (member : face ∈ (push R bit chain).support) :
    ∃ original ∈ chain.support, original.cons bit = face := by
  classical
  exact Finset.mem_image.mp (Finsupp.mapDomain_support member)

private theorem support_sub {a b : Chains R n} {face : Face n}
    (member : face ∈ (a - b).support) : face ∈ a.support ∨ face ∈ b.support :=
  Finset.mem_union.mp (Finsupp.support_sub member)

private theorem support_add {a b : Chains R n} {face : Face n}
    (member : face ∈ (a + b).support) : face ∈ a.support ∨ face ∈ b.support :=
  Finset.mem_union.mp (Finsupp.support_add member)

/-- Every boundary face is a subface of one lower dimension. -/
theorem boundary_support (face : Face n) {result : Face n}
    (member : result ∈ (boundary R n (Finsupp.single face 1)).support) :
    (∀ vertex, result.Contains vertex → face.Contains vertex) ∧
      result.dimension + 1 = face.dimension := by
  induction n with
  | zero => simp [boundary] at member
  | succ n ih =>
      rw [← Face.cons_tail face] at member ⊢
      rw [← push_single] at member
      cases bit : face 0 with
      | some value =>
          rw [bit, boundary_push_fixed] at member
          obtain ⟨original, support, rfl⟩ := support_push R member
          obtain ⟨subface, dim⟩ := ih (Fin.tail face) support
          constructor
          · intro vertex contained
            rw [Face.contains_iff_head_tail] at contained ⊢
            exact ⟨contained.1, subface _ contained.2⟩
          · simp only [Face.dimension_cons, reduceCtorEq, ite_false, Nat.add_zero]
            exact dim
      | none =>
          rw [bit, boundary_push_free] at member
          rcases support_sub R member with first | last
          · rcases support_sub R first with upper | lower
            all_goals
              obtain ⟨original, support, rfl⟩ := support_push R (by assumption)
              have equal : original = Fin.tail face :=
                Finset.mem_singleton.mp (Finsupp.support_single_subset support)
              subst original
              constructor
              · intro vertex contained
                rw [Face.contains_iff_head_tail] at contained ⊢
                exact ⟨Or.inl rfl, contained.2⟩
              · simp
          · obtain ⟨original, support, rfl⟩ := support_push R last
            obtain ⟨subface, dim⟩ := ih (Fin.tail face) support
            constructor
            · intro vertex contained
              rw [Face.contains_iff_head_tail] at contained ⊢
              exact ⟨Or.inl rfl, subface _ contained.2⟩
            · simp only [Face.dimension_cons, ite_true]
              omega

/-- Every prism face is one dimension higher and has only erased original vertices. -/
theorem prism_support (face : Face n) {result : Face n}
    (member : result ∈ (prism R n (Finsupp.single face 1)).support) :
    result.dimension = face.dimension + 1 ∧
      ∀ vertex, result.Contains vertex →
        ∃ original, face.Contains original ∧
          ∃ threshold, erase Fin.val threshold original = vertex := by
  induction n with
  | zero => simp [prism] at member
  | succ n ih =>
      rw [← Face.cons_tail face] at member ⊢
      rw [← push_single] at member
      cases bit : face 0 with
      | none => simp [bit] at member
      | some value =>
          have lift (support : result ∈
              (push R (some false) (prism R n (Finsupp.single (Fin.tail face) 1))).support) :
              result.dimension = (Face.cons (some value) (Fin.tail face)).dimension + 1 ∧
                ∀ vertex, result.Contains vertex →
                  ∃ original, (Face.cons (some value) (Fin.tail face)).Contains original ∧
                    ∃ threshold, erase Fin.val threshold original = vertex := by
            obtain ⟨tail, tailMember, rfl⟩ := support_push R support
            obtain ⟨dim, swept⟩ := ih (Fin.tail face) tailMember
            refine ⟨by simpa using dim, ?_⟩
            intro vertex contained
            rw [Face.contains_iff_head_tail] at contained
            have head : vertex 0 = false := by
              have h : false = vertex 0 := by simpa using contained.1
              exact h.symm
            obtain ⟨original, originalContains, threshold, erased⟩ := swept _ contained.2
            refine ⟨Fin.cons value original, ?_, threshold + 1, ?_⟩
            · exact Face.contains_cons _ _ _ _ |>.mpr ⟨Or.inr rfl, originalContains⟩
            · rw [Face.erase_cons_succ, erased, ← head, Fin.cons_self_tail]
          cases value
          · rw [bit, prism_push_false] at member
            exact lift member
          · rw [bit, prism_push_true] at member
            rcases support_add R member with first | last
            · obtain ⟨tail, tailMember, rfl⟩ := support_push R first
              have equal : tail = Fin.tail face :=
                Finset.mem_singleton.mp (Finsupp.support_single_subset tailMember)
              subst tail
              refine ⟨by simp, ?_⟩
              intro vertex contained
              rw [Face.contains_iff_head_tail] at contained
              refine ⟨Fin.cons true (Fin.tail vertex), ?_, ?_⟩
              · exact Face.contains_cons _ _ _ _ |>.mpr ⟨Or.inr rfl, contained.2⟩
              · cases head : vertex 0
                · refine ⟨1, ?_⟩
                  rw [Face.erase_cons_succ true (Fin.tail vertex) 0]
                  simp only [erase, patch_zero]
                  rw [← head, Fin.cons_self_tail]
                · refine ⟨0, ?_⟩
                  simp only [erase, patch_zero]
                  rw [← head, Fin.cons_self_tail]
            · exact lift last

/-- Augmentation vanishes on every positive-dimensional face. -/
theorem augmentation_single_eq_zero (face : Face n) (positive : 0 < face.dimension) :
    augmentation R n (Finsupp.single face 1) = 0 := by
  induction n with
  | zero => simp [Face.dimension, Face.free] at positive
  | succ n ih =>
      rw [← Face.cons_tail face, ← push_single]
      cases bit : face 0 with
      | none => simp
      | some value =>
          have positiveTail : 0 < Face.dimension (Fin.tail face) := by
            rw [← Face.cons_tail face, bit] at positive
            simpa using positive
          simp [ih _ positiveTail]

/-- A linear map carries supported chains into a submodule once it does so on basis faces. -/
theorem map_supported {M : Type*} [AddCommGroup M] [Module R M]
    (map : Chains R n →ₗ[R] M)
    (source : Set (Face n)) (target : Submodule R M)
    (basis : ∀ face ∈ source, map (Finsupp.single face 1) ∈ target)
    {chain : Chains R n} (member : chain ∈ Finsupp.supported R R source) : map chain ∈ target := by
  rw [Finsupp.supported_eq_span_single] at member
  have included : Submodule.span R ((fun face => Finsupp.single face (1 : R)) '' source) ≤
      target.comap map := by
    apply Submodule.span_le.mpr
    rintro _ ⟨face, allowed, rfl⟩
    exact basis face allowed
  exact included member

end Chains
end Algebraic.BooleanCube
