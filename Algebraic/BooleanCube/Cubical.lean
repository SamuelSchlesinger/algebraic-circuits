import Algebraic.BooleanCube.Sweep
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Cubical sublevels and coherent erasure

A point belongs to the cubical realization of a set of Boolean vertices
when it lies in the unit cube and every vertex of its smallest containing
face belongs to the set. In particular, squares and higher faces are filled
exactly when all their vertices are present.

A uniform bound on the cost of prefix erasure gives an actual continuous
null-homotopy of the sublevel inclusion. This is stronger than a separate
choice of a path for each vertex.
-/

namespace Algebraic.BooleanCube

variable {ι : Type*}

/-- The vertices of the smallest cube face containing a point. -/
def Compatible (point : ι → Real) (vertex : ι → Bool) : Prop :=
  ∀ i, (point i = 0 → vertex i = false) ∧ (point i = 1 → vertex i = true)

/-- The union of all cube faces whose vertices belong to `vertices`. -/
def cubical (vertices : Set (ι → Bool)) : Set (ι → Real) :=
  {point | (∀ i, 0 ≤ point i ∧ point i ≤ 1) ∧
    ∀ vertex, Compatible point vertex → vertex ∈ vertices}

/-- Embed a Boolean vertex in the real unit cube. -/
def realVertex (vertex : ι → Bool) : ι → Real := fun i => if vertex i then 1 else 0

/-- The cubical realization has exactly the specified Boolean vertices. -/
theorem realVertex_mem_cubical_iff (vertices : Set (ι → Bool)) (vertex : ι → Bool) :
    realVertex vertex ∈ cubical vertices ↔ vertex ∈ vertices := by
  constructor
  · intro member
    apply member.2 vertex
    intro i
    cases h : vertex i <;> simp [realVertex, h]
  · intro member
    constructor
    · intro i
      cases h : vertex i <;> simp [realVertex, h]
    · intro other compatible
      have equal : other = vertex := by
        funext i
        have h := compatible i
        cases bit : vertex i <;> simp [realVertex, bit] at h ⊢ <;> tauto
      simpa [equal] using member

/-- Cubical realization preserves inclusions of vertex sets. -/
theorem cubical_mono {left right : Set (ι → Bool)} (included : left ⊆ right) :
    cubical left ⊆ cubical right := by
  intro point member
  exact ⟨member.1, fun vertex compatible => included (member.2 vertex compatible)⟩

/-- Prefix erasure extended to real cube points. -/
def erasePoint (rank : ι → Nat) (threshold : Nat) (point : ι → Real) : ι → Real :=
  fun i => if rank i < threshold then 0 else point i

/-- One continuous step of the coordinate erasure. -/
def sweepPoint (rank : ι → Nat) (threshold : Nat) (time : unitInterval)
    (point : ι → Real) : ι → Real :=
  fun i => if rank i < threshold then 0
    else if rank i = threshold then (1 - (time : Real)) * point i else point i

private noncomputable def liftVertex (rank : ι → Nat) (threshold : Nat)
    (point : ι → Real) (vertex : ι → Bool) : ι → Bool := by
  classical
  exact fun i => if rank i < threshold then decide (point i = 1) else vertex i

private theorem liftVertex_compatible (rank : ι → Nat) (threshold : Nat)
    (point : ι → Real) (vertex : ι → Bool)
    (compatible : Compatible (erasePoint rank threshold point) vertex) :
    Compatible point (liftVertex rank threshold point vertex) := by
  classical
  intro i
  by_cases before : rank i < threshold
  · simp [liftVertex, before]
    intro zero
    simp [zero]
  · simpa [liftVertex, erasePoint, before] using compatible i

private theorem erase_liftVertex (rank : ι → Nat) (threshold : Nat)
    (point : ι → Real) (vertex : ι → Bool)
    (compatible : Compatible (erasePoint rank threshold point) vertex) :
    erase rank threshold (liftVertex rank threshold point vertex) = vertex := by
  classical
  funext i
  by_cases before : rank i < threshold
  · have value : vertex i = false := (compatible i).1 (by simp [erasePoint, before])
    simp [erase, patch, before, value]
  · simp [erase, patch, liftVertex, before]

/-- Bounds on erased vertices also bound the erased geometric faces. -/
theorem erasePoint_mem_cubical (rank : ι → Nat) (threshold : Nat)
    {source target : Set (ι → Bool)}
    (bounded : ∀ vertex ∈ source, erase rank threshold vertex ∈ target)
    {point : ι → Real} (member : point ∈ cubical source) :
    erasePoint rank threshold point ∈ cubical target := by
  constructor
  · intro i
    by_cases before : rank i < threshold <;> simp [erasePoint, before, member.1 i]
  · intro vertex compatible
    have original := member.2 _ (liftVertex_compatible rank threshold point vertex compatible)
    have result := bounded _ original
    rwa [erase_liftVertex rank threshold point vertex compatible] at result

private theorem sweep_lift (rank : ι → Nat) (injective : Function.Injective rank)
    (threshold : Nat) (time : unitInterval) (point : ι → Real) (vertex : ι → Bool)
    (compatible : Compatible (sweepPoint rank threshold time point) vertex) :
    ∃ original, Compatible point original ∧
      (erase rank threshold original = vertex ∨ erase rank (threshold + 1) original = vertex) := by
  classical
  by_cases allFalse : ∀ i, rank i = threshold → vertex i = false
  · let original := liftVertex rank (threshold + 1) point vertex
    refine ⟨original, ?_, Or.inr ?_⟩
    · intro i
      by_cases before : rank i < threshold + 1
      · simp [original, liftVertex, before]
        intro zero
        simp [zero]
      · have earlier : ¬rank i < threshold := by omega
        have current : rank i ≠ threshold := by omega
        simpa [original, liftVertex, before, sweepPoint, earlier, current] using compatible i
    · funext i
      by_cases before : rank i < threshold + 1
      · have value : vertex i = false := by
          by_cases earlier : rank i < threshold
          · exact (compatible i).1 (by simp [sweepPoint, earlier])
          · exact allFalse i (by omega)
        simp [erase, patch, before, value]
      · simp [erase, patch, original, liftVertex, before]
  · push Not at allFalse
    obtain ⟨index, atRank, notFalse⟩ := allFalse
    have allTrue : ∀ i, rank i = threshold → vertex i = true := by
      intro i hi
      have equal : i = index := injective (hi.trans atRank.symm)
      subst i
      cases h : vertex index <;> simp_all
    let original := liftVertex rank threshold point vertex
    refine ⟨original, ?_, Or.inl ?_⟩
    · intro i
      by_cases before : rank i < threshold
      · simp [original, liftVertex, before]
        intro zero
        simp [zero]
      · simp only [original, liftVertex, before, ite_false]
        constructor
        · intro zero
          exact (compatible i).1 (by simp [sweepPoint, before, zero])
        · intro one
          by_cases current : rank i = threshold
          · exact allTrue i current
          · exact (compatible i).2 (by simp [sweepPoint, before, current, one])
    · funext i
      by_cases before : rank i < threshold
      · have value : vertex i = false := (compatible i).1 (by simp [sweepPoint, before])
        simp [erase, patch, before, value]
      · simp [erase, patch, original, liftVertex, before]

/-- An entire continuous erasure step stays within faces controlled by its two endpoints. -/
theorem sweepPoint_mem_cubical (rank : ι → Nat) (injective : Function.Injective rank)
    (threshold : Nat) (time : unitInterval) {source target : Set (ι → Bool)}
    (before : ∀ vertex ∈ source, erase rank threshold vertex ∈ target)
    (after : ∀ vertex ∈ source, erase rank (threshold + 1) vertex ∈ target)
    {point : ι → Real} (member : point ∈ cubical source) :
    sweepPoint rank threshold time point ∈ cubical target := by
  constructor
  · intro i
    have bounds := member.1 i
    have timeLower : 0 ≤ (time : Real) := time.property.1
    have timeUpper : (time : Real) ≤ 1 := time.property.2
    dsimp [sweepPoint]
    split_ifs
    · constructor <;> norm_num
    · constructor
      · exact mul_nonneg (sub_nonneg.mpr timeUpper) bounds.1
      · nlinarith [mul_nonneg timeLower bounds.1]
    · exact bounds
  · intro vertex compatible
    obtain ⟨original, originalCompatible, equal | equal⟩ :=
      sweep_lift rank injective threshold time point vertex compatible
    · exact equal ▸ before original (member.2 original originalCompatible)
    · exact equal ▸ after original (member.2 original originalCompatible)

/-- The geometric realization of a cost sublevel, with its subspace topology. -/
abbrev Sublevel (cost : (ι → Bool) → Nat) (budget : Nat) :=
  {point : ι → Real // point ∈ cubical {vertex | cost vertex ≤ budget}}

/-- Increasing the budget induces the usual continuous sublevel inclusion. -/
def inclusion (cost : (ι → Bool) → Nat) (budget overhead : Nat) :
    C(Sublevel cost budget, Sublevel cost (budget + overhead)) where
  toFun point := ⟨point.val, cubical_mono (fun _ h => h.trans (Nat.le_add_right _ _)) point.property⟩
  continuous_toFun := by fun_prop

private def erasureMap (rank : ι → Nat) (cost : (ι → Bool) → Nat) (budget overhead : Nat)
    (bounded : ∀ threshold vertex, cost (erase rank threshold vertex) ≤ cost vertex + overhead)
    (threshold : Nat) : C(Sublevel cost budget, Sublevel cost (budget + overhead)) where
  toFun point := ⟨erasePoint rank threshold point.val,
    erasePoint_mem_cubical rank threshold
      (fun vertex h => (bounded threshold vertex).trans (Nat.add_le_add_right h overhead))
      point.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    dsimp [erasePoint]
    split_ifs
    · exact continuous_const
    · exact (continuous_apply i).comp continuous_subtype_val

private def erasureHomotopy (rank : ι → Nat) (injective : Function.Injective rank)
    (cost : (ι → Bool) → Nat) (budget overhead : Nat)
    (bounded : ∀ threshold vertex, cost (erase rank threshold vertex) ≤ cost vertex + overhead)
    (threshold : Nat) :
    (erasureMap rank cost budget overhead bounded threshold).Homotopy
      (erasureMap rank cost budget overhead bounded (threshold + 1)) where
  toFun pair := ⟨sweepPoint rank threshold pair.1 pair.2.val,
    sweepPoint_mem_cubical rank injective threshold pair.1
      (fun vertex h => (bounded threshold vertex).trans (Nat.add_le_add_right h overhead))
      (fun vertex h => (bounded (threshold + 1) vertex).trans (Nat.add_le_add_right h overhead))
      pair.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    dsimp [sweepPoint]
    split_ifs
    · exact continuous_const
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))
    · exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  map_zero_left point := by
    apply Subtype.ext
    funext i
    simp [sweepPoint, erasureMap, erasePoint]
  map_one_left point := by
    apply Subtype.ext
    funext i
    by_cases before : rank i < threshold
    · have next : rank i < threshold + 1 := by omega
      simp [sweepPoint, erasureMap, erasePoint, before, next]
    · by_cases current : rank i = threshold
      · simp [sweepPoint, erasureMap, erasePoint, current]
      · have next : ¬rank i < threshold + 1 := by omega
        simp [sweepPoint, erasureMap, erasePoint, before, current, next]

/-- Bounded prefix erasure contracts the whole sublevel inclusion, in every dimension.
The zero-vertex premise ensures the target is nonempty even when the source is empty. -/
theorem inclusion_nullhomotopic (rank : ι → Nat) (injective : Function.Injective rank)
    (length : Nat) (ranksBounded : ∀ i, rank i < length)
    (cost : (ι → Bool) → Nat) (budget overhead : Nat)
    (bounded : ∀ threshold vertex, cost (erase rank threshold vertex) ≤ cost vertex + overhead)
    (zeroBound : cost (fun _ => false) ≤ budget + overhead) :
    (inclusion cost budget overhead).Nullhomotopic := by
  let zero : Sublevel cost (budget + overhead) :=
    ⟨realVertex (fun _ => false), (realVertex_mem_cubical_iff _ _).mpr zeroBound⟩
  have chain : ∀ threshold,
      (erasureMap rank cost budget overhead bounded 0).Homotopic
        (erasureMap rank cost budget overhead bounded threshold) := by
    intro threshold
    induction threshold with
    | zero => exact ⟨ContinuousMap.Homotopy.refl _⟩
    | succ threshold ih =>
        exact ih.trans ⟨erasureHomotopy rank injective cost budget overhead bounded threshold⟩
  have start : erasureMap rank cost budget overhead bounded 0 = inclusion cost budget overhead := by
    ext point i
    simp [erasureMap, inclusion, erasePoint]
  have finish : erasureMap rank cost budget overhead bounded length =
      ContinuousMap.const (Sublevel cost budget) zero := by
    ext point i
    simp [erasureMap, erasePoint, ranksBounded i, zero, realVertex]
  refine ⟨zero, ?_⟩
  rw [← start, ← finish]
  exact chain length

end Algebraic.BooleanCube
