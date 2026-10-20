import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation

set_option autoImplicit false

/-!
# Kalman's unobservable subspace

The kernel of all linear trajectory records is the largest action-invariant subspace
inside the current observation kernel. Its finite-dimensional quotient carries the
minimal stable behavioral observer.
-/

namespace OperatorKO7.Meta.BoundaryObserver.KalmanObservability

/-- The vectors producing a zero record at every nonnegative power of the action. -/
def unobservable (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) : Submodule K V :=
  ⨅ k : ℕ, LinearMap.ker (C.comp (A ^ k))

/-- Membership means that every recorded iterate of the vector is zero. -/
theorem mem_unobservable_iff (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x : V) :
    x ∈ unobservable K A C ↔ ∀ k : ℕ, C ((A ^ k) x) = 0 := by
  simp [unobservable, LinearMap.mem_ker, LinearMap.comp_apply]

/-- A vector hidden at every time is hidden after one more action. -/
theorem unobservable_stable (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x : V)
    (hx : x ∈ unobservable K A C) : A x ∈ unobservable K A C := by
  rw [mem_unobservable_iff]
  intro k
  have h := (mem_unobservable_iff K A C x).mp hx (k + 1)
  simpa only [pow_succ, Module.End.mul_apply] using h

/-- The unobservable subspace lies in the kernel of the current record. -/
theorem unobservable_le_ker (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    unobservable K A C ≤ LinearMap.ker C := by
  intro x hx
  rw [LinearMap.mem_ker]
  have h := (mem_unobservable_iff K A C x).mp hx 0
  simpa using h

/-- Every action-invariant subspace in the record kernel lies in the unobservable subspace. -/
theorem invariant_le_unobservable (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (S : Submodule K V)
    (hA : ∀ x ∈ S, A x ∈ S) (hC : S ≤ LinearMap.ker C) :
    S ≤ unobservable K A C := by
  intro x hx
  rw [mem_unobservable_iff]
  intro k
  have hk : ∀ m : ℕ, (A ^ m) x ∈ S := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ j ih =>
        simpa only [pow_succ', Module.End.mul_apply] using hA _ ih
  exact LinearMap.mem_ker.mp (hC (hk k))

/-- The unobservable subspace is invariant, is inside the record kernel, and is
the largest subspace with those two properties. -/
theorem unobservable_largest_invariant (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (∀ x ∈ unobservable K A C, A x ∈ unobservable K A C) ∧
    unobservable K A C ≤ LinearMap.ker C ∧
    ∀ S : Submodule K V, (∀ x ∈ S, A x ∈ S) →
      S ≤ LinearMap.ker C → S ≤ unobservable K A C :=
  ⟨unobservable_stable K A C, unobservable_le_ker K A C,
    invariant_le_unobservable K A C⟩

/-- The first finrank-many trajectory records detect every later zero record by
the Cayley-Hamilton polynomial identity, including the zero-dimensional case. -/
theorem unobservable_eq_finite (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    unobservable K A C =
      ⨅ i : Fin (Module.finrank K V), LinearMap.ker (C.comp (A ^ (i : ℕ))) := by
  ext x
  simp only [mem_unobservable_iff, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.comp_apply]
  constructor
  · intro hx i
    exact hx i
  · intro hfin k
    by_cases hn : Module.finrank K V = 0
    · have hz : x = 0 := (finrank_zero_iff_forall_zero).mp hn x
      simp [hz]
    · let p : Polynomial K := Polynomial.X ^ k %ₘ A.charpoly
      have hne : A.charpoly ≠ 1 := by
        intro he
        have hdegree := A.charpoly_natDegree
        rw [he, Polynomial.natDegree_one] at hdegree
        exact hn hdegree.symm
      have hdeg : p.natDegree < Module.finrank K V := by
        dsimp [p]
        rw [← A.charpoly_natDegree]
        exact Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hne
      have hz : C ((Polynomial.aeval A p) x) = 0 := by
        rw [Polynomial.aeval_eq_sum_range' hdeg A]
        rw [LinearMap.sum_apply, map_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hii : i < Module.finrank K V := Finset.mem_range.mp hi
        have hh := hfin ⟨i, hii⟩
        simp [LinearMap.smul_apply, map_smul, hh]
      calc
        C ((A ^ k) x) = C ((Polynomial.aeval A p) x) := by
          rw [A.pow_eq_aeval_mod_charpoly k]
        _ = 0 := hz

/-- Every word of the single linear action acts by the power given by its length. -/
theorem run_linear_unit (K : Type*) [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (A : V →ₗ[K] V)
    (w : List Unit) (x : V) :
    AdmissibleObservation.run (fun _ : Unit => (A : V → V)) w x =
      (A ^ w.length) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
      change AdmissibleObservation.run (fun _ : Unit => (A : V → V)) w (A x) =
        (A ^ (w.length + 1)) x
      rw [ih, pow_succ, Module.End.mul_apply]

/-- Two states have equal permitted trajectory records exactly when their
difference lies in the unobservable subspace. -/
theorem futureEq_iff_sub_mem_unobservable (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V) :
    AdmissibleObservation.FutureEq (C : V → W)
      (fun _ : Unit => (A : V → V)) x y ↔
      x - y ∈ unobservable K A C := by
  constructor
  · intro h
    apply (mem_unobservable_iff K A C (x - y)).2
    intro k
    have hh := congrFun h (List.replicate k ())
    change C (AdmissibleObservation.run (fun _ : Unit => (A : V → V))
        (List.replicate k ()) x) =
      C (AdmissibleObservation.run (fun _ : Unit => (A : V → V))
        (List.replicate k ()) y) at hh
    rw [run_linear_unit K A, run_linear_unit K A, List.length_replicate] at hh
    simpa only [map_sub, sub_eq_zero] using hh
  · intro h
    have hh := (mem_unobservable_iff K A C (x - y)).mp h
    funext w
    change C (AdmissibleObservation.run (fun _ : Unit => (A : V → V)) w x) =
      C (AdmissibleObservation.run (fun _ : Unit => (A : V → V)) w y)
    rw [run_linear_unit K A, run_linear_unit K A]
    have hz := hh w.length
    simpa only [map_sub, sub_eq_zero] using hz

/-- The linear behavioral map records the output of every nonnegative iterate. -/
def behavioralRecord (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) : V →ₗ[K] (ℕ → W) :=
  LinearMap.pi (fun k : ℕ => C.comp (A ^ k))

/-- The kernel of the entire behavioral map is exactly the unobservable subspace. -/
theorem ker_behavioralRecord (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    LinearMap.ker (behavioralRecord K A C) = unobservable K A C := by
  ext x
  rw [LinearMap.mem_ker, mem_unobservable_iff]
  constructor
  · intro h k
    have hk := congrFun h k
    simpa [behavioralRecord] using hk
  · intro h
    funext k
    simpa [behavioralRecord] using h k

/-- The stacked observability map records exactly the first finrank-many outputs. -/
def stackedObservability (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    V →ₗ[K] (Fin (Module.finrank K V) → W) :=
  LinearMap.pi (fun k : Fin (Module.finrank K V) => C.comp (A ^ (k : ℕ)))

/-- The finite stacked map has the unobservable subspace as its kernel. -/
theorem ker_stackedObservability (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    LinearMap.ker (stackedObservability K A C) = unobservable K A C := by
  rw [unobservable_eq_finite]
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_iInf]
  constructor
  · intro h k
    rw [LinearMap.mem_ker]
    have hk := congrFun h k
    simpa [stackedObservability] using hk
  · intro h
    funext k
    have hk := LinearMap.mem_ker.mp (h k)
    simpa [stackedObservability] using hk

/-- The entire behavior is injective exactly when the hidden subspace vanishes,
exactly when the finite stacked observability map is injective. -/
theorem behavior_injective_iff (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (Function.Injective (behavioralRecord K A C) ↔ unobservable K A C = ⊥) ∧
    (unobservable K A C = ⊥ ↔ Function.Injective (stackedObservability K A C)) := by
  constructor
  · rw [← ker_behavioralRecord K A C]
    exact (LinearMap.ker_eq_bot (f := behavioralRecord K A C)).symm
  · rw [← ker_stackedObservability K A C]
    exact LinearMap.ker_eq_bot (f := stackedObservability K A C)

/-- The hidden-state quotient carries the action induced by the original dynamics. -/
def quotientAction (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (V ⧸ unobservable K A C) →ₗ[K] (V ⧸ unobservable K A C) :=
  (unobservable K A C).mapQ (unobservable K A C) A
    (by
      intro x hx
      exact unobservable_stable K A C x hx)

/-- The original linear record descends to the hidden-state quotient. -/
def quotientRecord (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (V ⧸ unobservable K A C) →ₗ[K] W :=
  (unobservable K A C).liftQ C (unobservable_le_ker K A C)

/-- The hidden-state quotient identifies precisely states with the same future records. -/
theorem quotient_eq_iff_futureEq (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V) :
    (unobservable K A C).mkQ x = (unobservable K A C).mkQ y ↔
      AdmissibleObservation.FutureEq (C : V → W)
        (fun _ : Unit => (A : V → V)) x y := by
  simpa only [Submodule.mkQ_apply, Submodule.Quotient.eq] using
    (futureEq_iff_sub_mem_unobservable K A C x y).symm

/-- The quotient action and record descend from the original system, and
every sufficient, updateable record factors uniquely onto the minimal observer. -/
theorem unobservable_quotient_universal (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    (∀ x : V, quotientRecord K A C ((unobservable K A C).mkQ x) = C x) ∧
    (∀ x : V, quotientAction K A C ((unobservable K A C).mkQ x) =
      (unobservable K A C).mkQ (A x)) ∧
    ∃! f : (V ⧸ unobservable K A C) →
      AdmissibleObservation.MinimalState (C : V → W)
        (fun _ : Unit => (A : V → V)),
      ∀ x : V, f ((unobservable K A C).mkQ x) =
        AdmissibleObservation.minimalRecord (C : V → W)
          (fun _ : Unit => (A : V → V)) x := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [quotientRecord]
  · intro x
    simp [quotientAction]
  · apply AdmissibleObservation.minimal_observer_universal
      (C : V → W) (fun _ : Unit => (A : V → V))
      (unobservable K A C).mkQ (Submodule.mkQ_surjective (unobservable K A C))
    · intro x y h
      have hh := congrArg (quotientRecord K A C) h
      simpa [quotientRecord] using hh
    · intro a x y h
      have hh := congrArg (quotientAction K A C) h
      simpa [quotientAction] using hh

/-- The coordinate-swap action interchanges two components of a state. -/
def coordinateSwap (K : Type*) [Field K] : (K × K) →ₗ[K] (K × K) where
  toFun := fun x => (x.2, x.1)
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/-- The record of a pair retains exactly its first coordinate. -/
def firstCoordinate (K : Type*) [Field K] : (K × K) →ₗ[K] K where
  toFun := fun x => x.1
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/-- The coordinate-swap system with first-coordinate observation has no
nonzero unobservable vector. -/
theorem coordinate_swap_unobservable_eq_bot (K : Type*) [Field K] :
    unobservable K (coordinateSwap K) (firstCoordinate K) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  have h := (mem_unobservable_iff K (coordinateSwap K) (firstCoordinate K) x).mp hx
  have h0 := h 0
  have h1 := h 1
  have hx0 : x.1 = 0 := by simpa [firstCoordinate] using h0
  have hx1 : x.2 = 0 := by simpa [coordinateSwap, firstCoordinate] using h1
  exact Prod.ext hx0 hx1

/-- For the identity action, first-coordinate observation has precisely the
second coordinate axis as its hidden subspace. -/
theorem identity_unobservable_eq_second_axis (K : Type*) [Field K] :
    unobservable K (LinearMap.id : (K × K) →ₗ[K] (K × K))
      (firstCoordinate K) = LinearMap.ker (firstCoordinate K) := by
  ext x
  rw [mem_unobservable_iff, LinearMap.mem_ker]
  constructor
  · intro h
    simpa using h 0
  · intro h k
    simpa using h

end OperatorKO7.Meta.BoundaryObserver.KalmanObservability
