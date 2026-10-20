import OperatorKO7.Meta.BoundaryObserver.LinearObservability
import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false

/-!
# Merged pairs, record-preserving translations and a projection side record of a linear system

A linear system has an action `A : V →ₗ[K] V` and a linear record `C : V →ₗ[K] W` over a field
`K`; its observer is the behavioral record `x ↦ (C (A ^ k x))ₖ`. Two states have one behavioral
record exactly when their difference lies in the unobservable subspace, and in finite dimension
this subspace is the kernel of the stacked map of `C, C A, …, C A ^ (n - 1)`. The merged pairs of
the observer are therefore the distinct pairs with an unobservable difference; translation by a
vector keeps every record exactly when the vector is unobservable; the observer has no merged
pair exactly when the stacked map has full rank; and every linear projection onto the
unobservable subspace is a side record that resolves every merged pair. Such a projection
exists on every vector space.

Relation: none; the statements concern linear maps over a field.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.KalmanSideRecord

open OperatorKO7.Meta.BoundaryObserver.KalmanObservability
open OperatorKO7.Meta.BoundaryObserver.LinearObservability
open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-! ## Record equality and merged pairs -/

/-- Two states have one behavioral record exactly when their difference lies in the
unobservable subspace, in every dimension. -/
theorem behavioralRecord_eq_iff_sub_mem_unobservable (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V) :
    behavioralRecord K A C x = behavioralRecord K A C y ↔ x - y ∈ unobservable K A C := by
  rw [← ker_behavioralRecord K A C, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- In finite dimension, two states have one behavioral record exactly when their difference
lies in the kernel of the stacked map of `C, C A, …, C A ^ (n - 1)`. -/
theorem behavioralRecord_eq_iff_sub_mem_ker_stacked (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V) :
    behavioralRecord K A C x = behavioralRecord K A C y ↔
      x - y ∈ LinearMap.ker (stackedObservability K A C) := by
  rw [ker_stackedObservability K A C]
  exact behavioralRecord_eq_iff_sub_mem_unobservable K A C x y

/-- The merged pairs of the behavioral observer are the distinct pairs with an unobservable
difference. -/
theorem isMergedPair_iff (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V) :
    MergedPair.IsMergedPair (behavioralRecord K A C) x y ↔
      x ≠ y ∧ x - y ∈ unobservable K A C :=
  and_congr Iff.rfl (behavioralRecord_eq_iff_sub_mem_unobservable K A C x y)

/-- In finite dimension, the merged pairs of the behavioral observer are the distinct pairs with
difference in the kernel of the stacked map. -/
theorem isMergedPair_iff_ker_stacked (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V) :
    MergedPair.IsMergedPair (behavioralRecord K A C) x y ↔
      x ≠ y ∧ x - y ∈ LinearMap.ker (stackedObservability K A C) := by
  rw [ker_stackedObservability K A C]
  exact isMergedPair_iff K A C x y

/-! ## Translations -/

/-- Translation by `v` is a permutation keeping every behavioral record exactly when `v` is
unobservable. -/
theorem addRight_mem_licenseStabilizer_iff (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (v : V) :
    Equiv.addRight v ∈ licenseStabilizer (behavioralRecord K A C) ↔
      v ∈ unobservable K A C := by
  rw [mem_licenseStabilizer_iff, ← ker_behavioralRecord K A C, LinearMap.mem_ker]
  constructor
  · intro h
    simpa using h 0
  · intro hv x
    simp [hv]

/-- In finite dimension, translation by `v` keeps every behavioral record exactly when `v` lies
in the kernel of the stacked map. -/
theorem addRight_mem_licenseStabilizer_iff_ker_stacked (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (v : V) :
    Equiv.addRight v ∈ licenseStabilizer (behavioralRecord K A C) ↔
      v ∈ LinearMap.ker (stackedObservability K A C) := by
  rw [ker_stackedObservability K A C]
  exact addRight_mem_licenseStabilizer_iff K A C v

/-- The translation by the difference of a merged pair keeps every record and maps the first
state of the pair to the second. -/
theorem mergedPair_translation (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V)
    (h : MergedPair.IsMergedPair (behavioralRecord K A C) x y) :
    Equiv.addRight (y - x) ∈ licenseStabilizer (behavioralRecord K A C) ∧
      Equiv.addRight (y - x) x = y := by
  refine ⟨?_, ?_⟩
  · rw [addRight_mem_licenseStabilizer_iff]
    exact (behavioralRecord_eq_iff_sub_mem_unobservable K A C y x).mp h.2.symm
  · simp

/-! ## The full-rank criterion -/

/-- In finite dimension, the behavioral observer has no merged pair exactly when the stacked map
has rank equal to the dimension of the state space. -/
theorem boundary_eq_empty_iff_finrank_range (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    MergedPair.boundary (behavioralRecord K A C) = ∅ ↔
      Module.finrank K (LinearMap.range (stackedObservability K A C)) =
        Module.finrank K V := by
  rw [MergedPair.boundary_eq_empty_iff_injective]
  exact observable_iff_rank_eq K A C

/-! ## The projection side record -/

/-- Two states with one behavioral record and one value under a linear map `π` differ by an
unobservable vector with image zero under `π`. -/
theorem same_record_same_value (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (π : V →ₗ[K] V) (x y : V)
    (h₁ : behavioralRecord K A C x = behavioralRecord K A C y) (h₂ : π x = π y) :
    x - y ∈ unobservable K A C ∧ π (x - y) = 0 :=
  ⟨(behavioralRecord_eq_iff_sub_mem_unobservable K A C x y).mp h₁, by
    rw [map_sub, h₂, sub_self]⟩

/-- A projection onto the unobservable subspace, read beside the behavioral record, determines
the state: the joint record is injective. -/
theorem projection_record_injective (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (π : V →ₗ[K] V)
    (hπ : LinearMap.IsProj (unobservable K A C) π) :
    Function.Injective (fun x => (behavioralRecord K A C x, π x)) := by
  intro x y hxy
  obtain ⟨hd, hz⟩ := same_record_same_value K A C π x y (congrArg Prod.fst hxy)
    (congrArg Prod.snd hxy)
  rw [hπ.map_id (x - y) hd] at hz
  exact sub_eq_zero.mp hz

/-- A projection onto the unobservable subspace separates the two states of every merged pair of
the behavioral observer. -/
theorem projection_separates_mergedPair (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (π : V →ₗ[K] V)
    (hπ : LinearMap.IsProj (unobservable K A C) π) (x y : V)
    (h : MergedPair.IsMergedPair (behavioralRecord K A C) x y) :
    π x ≠ π y := by
  intro hxy
  exact h.1 (projection_record_injective K A C π hπ (Prod.ext h.2 hxy))

/-- A projection onto the unobservable subspace is a resolving side channel of the behavioral
observer for the identity target: confusable states receive distinct side values. -/
theorem projection_resolvingSideChannel (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (π : V →ₗ[K] V)
    (hπ : LinearMap.IsProj (unobservable K A C) π) :
    OperationalInexpressibility.Confusability.ResolvingSideChannel
      (behavioralRecord K A C) (id : V → V) π := by
  intro x y hxy hπxy
  obtain ⟨h₁, h₂⟩ := hxy
  exact h₂ (projection_record_injective K A C π hπ (Prod.ext h₁ hπxy))

/-- The behavioral record augmented by a projection onto the unobservable subspace determines
the identity target. -/
theorem projection_determines_state (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (π : V →ₗ[K] V)
    (hπ : LinearMap.IsProj (unobservable K A C) π) :
    MergedPair.Determines (fun x => (behavioralRecord K A C x, π x)) (id : V → V) :=
  (MergedPair.determines_id_iff_injective _).mpr (projection_record_injective K A C π hπ)

/-- Every vector space has a linear projection onto the unobservable subspace. -/
theorem exists_isProj_unobservable (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    ∃ π : V →ₗ[K] V, LinearMap.IsProj (unobservable K A C) π := by
  obtain ⟨S, hS⟩ := Submodule.exists_isCompl (unobservable K A C)
  refine ⟨(unobservable K A C).subtype ∘ₗ
    Submodule.linearProjOfIsCompl (unobservable K A C) S hS, ?_, ?_⟩
  · intro x
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    exact Submodule.coe_mem _
  · intro x hx
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hS ⟨x, hx⟩)

/-- In finite dimension, every projection onto the kernel of the stacked map resolves the
behavioral observer, and such a projection exists. -/
theorem projection_ker_stacked (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (∀ π : V →ₗ[K] V, LinearMap.IsProj (LinearMap.ker (stackedObservability K A C)) π →
      Function.Injective (fun x => (behavioralRecord K A C x, π x))) ∧
    ∃ π : V →ₗ[K] V, LinearMap.IsProj (LinearMap.ker (stackedObservability K A C)) π := by
  rw [ker_stackedObservability K A C]
  exact ⟨fun π hπ => projection_record_injective K A C π hπ,
    exists_isProj_unobservable K A C⟩

/-! ## A system with a merged pair -/

/-- Under the identity action with the first coordinate as record, the states `(0, 0)` and
`(0, 1)` of `K × K` form a merged pair. -/
theorem identity_firstCoordinate_mergedPair (K : Type*) [Field K] :
    MergedPair.IsMergedPair
      (behavioralRecord K (LinearMap.id : (K × K) →ₗ[K] (K × K)) (firstCoordinate K))
      ((0 : K), (0 : K)) ((0 : K), (1 : K)) := by
  rw [isMergedPair_iff, identity_unobservable_eq_second_axis, LinearMap.mem_ker]
  refine ⟨?_, ?_⟩
  · intro h
    exact zero_ne_one (congrArg Prod.snd h)
  · simp [firstCoordinate]

/-! ## The example as one statement -/

/-- The finite-dimensional linear system: one behavioral record exactly when the difference is
unobservable; the unobservable subspace is cut out by the first `n` records and equals the
kernel `ker 𝒪` of the stacked map; the merged pairs are the distinct pairs with difference in
`ker 𝒪`; translation by `v` keeps every record exactly when `v ∈ ker 𝒪`; no merged pair exists
exactly when `𝒪` has rank `n`; every projection onto `ker 𝒪` separates every merged pair, and
such a projection exists. -/
theorem kalman_example (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (∀ x y : V, behavioralRecord K A C x = behavioralRecord K A C y ↔
      x - y ∈ unobservable K A C) ∧
    (unobservable K A C =
      ⨅ i : Fin (Module.finrank K V), LinearMap.ker (C.comp (A ^ (i : ℕ)))) ∧
    (LinearMap.ker (stackedObservability K A C) = unobservable K A C) ∧
    (∀ x y : V, MergedPair.IsMergedPair (behavioralRecord K A C) x y ↔
      x ≠ y ∧ x - y ∈ LinearMap.ker (stackedObservability K A C)) ∧
    (∀ v : V, Equiv.addRight v ∈ licenseStabilizer (behavioralRecord K A C) ↔
      v ∈ LinearMap.ker (stackedObservability K A C)) ∧
    (MergedPair.boundary (behavioralRecord K A C) = ∅ ↔
      Module.finrank K (LinearMap.range (stackedObservability K A C)) =
        Module.finrank K V) ∧
    (∀ π : V →ₗ[K] V, LinearMap.IsProj (LinearMap.ker (stackedObservability K A C)) π →
      ∀ x y : V, MergedPair.IsMergedPair (behavioralRecord K A C) x y → π x ≠ π y) ∧
    (∃ π : V →ₗ[K] V, LinearMap.IsProj (LinearMap.ker (stackedObservability K A C)) π) := by
  refine ⟨behavioralRecord_eq_iff_sub_mem_unobservable K A C, unobservable_eq_finite K A C,
    ker_stackedObservability K A C, isMergedPair_iff_ker_stacked K A C,
    addRight_mem_licenseStabilizer_iff_ker_stacked K A C,
    boundary_eq_empty_iff_finrank_range K A C, ?_, (projection_ker_stacked K A C).2⟩
  intro π hπ x y h
  rw [ker_stackedObservability K A C] at hπ
  exact projection_separates_mergedPair K A C π hπ x y h

end OperatorKO7.Meta.BoundaryObserver.KalmanSideRecord
