import OperatorKO7.Meta.BoundaryObserver.KalmanObservability

set_option autoImplicit false

/-!
# Linear observability under one permitted action

The kernel of the stacked record determines behavioral equivalence, the largest
action-invariant hidden subspace, and the full-rank observability criterion.
-/

namespace OperatorKO7.Meta.BoundaryObserver.LinearObservability

open OperatorKO7.Meta.BoundaryObserver.KalmanObservability

/-- Two states have the same permitted linear trajectory record precisely when their
difference belongs to the kernel of the finite stacked observability map. -/
theorem behavioral_equiv_iff_mem_ker_obs (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V) :
    AdmissibleObservation.FutureEq (C : V → W)
      (fun _ : Unit => (A : V → V)) x y ↔
      x - y ∈ LinearMap.ker (stackedObservability K A C) := by
  rw [ker_stackedObservability K A C]
  exact futureEq_iff_sub_mem_unobservable K A C x y

/-- The kernel of the stacked observability map is invariant under the action,
lies inside the immediate record kernel, and contains every such invariant subspace. -/
theorem unobservable_largest_invariant_subspace (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (∀ x ∈ LinearMap.ker (stackedObservability K A C),
      A x ∈ LinearMap.ker (stackedObservability K A C)) ∧
    LinearMap.ker (stackedObservability K A C) ≤ LinearMap.ker C ∧
    ∀ S : Submodule K V, (∀ x ∈ S, A x ∈ S) →
      S ≤ LinearMap.ker C → S ≤ LinearMap.ker (stackedObservability K A C) := by
  simpa only [ker_stackedObservability K A C] using
    (unobservable_largest_invariant K A C)

/-- The full behavioral record is injective exactly when the finite stacked map
has rank equal to the dimension of the state space. -/
theorem observable_iff_rank_eq (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    Function.Injective (behavioralRecord K A C) ↔
      Module.finrank K (LinearMap.range (stackedObservability K A C)) =
        Module.finrank K V := by
  have hbehavior :
      Function.Injective (behavioralRecord K A C) ↔
        Function.Injective (stackedObservability K A C) :=
    (behavior_injective_iff K A C).1.trans (behavior_injective_iff K A C).2
  rw [hbehavior]
  constructor
  · intro hinj
    have hker : LinearMap.ker (stackedObservability K A C) = ⊥ :=
      (LinearMap.ker_eq_bot (f := stackedObservability K A C)).2 hinj
    have hdim := LinearMap.finrank_range_add_finrank_ker
      (stackedObservability K A C)
    have hzero :
        Module.finrank K (LinearMap.ker (stackedObservability K A C)) = 0 :=
      (Submodule.finrank_eq_zero).mpr hker
    simpa only [hzero, Nat.add_zero] using hdim
  · intro hrank
    apply (LinearMap.ker_eq_bot (f := stackedObservability K A C)).1
    have hdim := LinearMap.finrank_range_add_finrank_ker
      (stackedObservability K A C)
    rw [hrank] at hdim
    have hzero :
        Module.finrank K (LinearMap.ker (stackedObservability K A C)) = 0 := by
      omega
    exact (Submodule.finrank_eq_zero).mp hzero

end OperatorKO7.Meta.BoundaryObserver.LinearObservability
