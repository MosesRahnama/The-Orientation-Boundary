/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
import OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory
import OperatorKO7.Meta.LicensedBoundaryCalculus.MetricDynamicLicense
import Mathlib.Logic.Relation

/-!
# Completion of dynamics as a licensed computation rule

Intent: prove that passing a one-step dynamics to its reflexive-transitive
closure does not change the persistent `Box` license, forward invariance, the
persistent diagonal grade `D1p`, or the represented grade `D2At`.  The same
rule is instantiated on the natural-number shift dynamics, where the metric
persistent license is exactly a `Box` predicate over the completed tail of the
index process.

Relation: a generic relation `R`, and the concrete shift relation
`shiftStep n m := m = n + 1`.
Closure: `Relation.ReflTransGen`.
Strategy: unrestricted reflexive-transitive closure.
External trust: Mathlib baseline only.
Non-vacuity witnesses: `toComplete` is a concrete morphism, and the shift
characterization is inhabited at every `N` by reflexivity.

`D0` and `D1s` do not mention a dynamics.  No completion theorem is stated for
them, because such a theorem would be a vacuous restatement rather than a
computation rule.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingCompletionRule

open Set
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory
open OperatorKO7.Meta.LicensedBoundaryCalculus.MetricDynamicLicense
open OperatorKO7.Analysis.UniformSeparation

universe u v w

/-- Proves: completing the dynamics does not change the greatest persistent
sublicense.

Relation: `R` and `Relation.ReflTransGen R`.
Closure: reflexive-transitive.
Strategy: unrestricted.
Trust: kernel plus Mathlib relation library.
-/
theorem box_reflTransGen_iff {α : Type} (R : α → α → Prop)
    (P : α → Prop) (x : α) :
    Box (Relation.ReflTransGen R) P x ↔ Box R P x := by
  constructor
  · intro h
    refine ⟨h.holds, ?_⟩
    intro y hy
    exact h.persists y (Relation.ReflTransGen.single hy)
  · intro h
    refine ⟨h.holds, ?_⟩
    intro y hy
    have hy' : Relation.ReflTransGen R x y := by
      simpa only [Relation.reflTransGen_idem] using hy
    exact h.persists y hy'

/-- Proves: star-closed forward invariance is invariant under completion of the
one-step dynamics.

Relation: `R` and `Relation.ReflTransGen R`.
Closure: reflexive-transitive.
Strategy: unrestricted.
Trust: kernel plus Mathlib relation library.
-/
theorem forwardInvariant_reflTransGen_iff {α : Type}
    (R : α → α → Prop) (Q : α → Prop) :
    ForwardInvariant (Relation.ReflTransGen R) Q ↔ ForwardInvariant R Q := by
  constructor
  · intro h x y hx hy
    exact h hx (Relation.ReflTransGen.single hy)
  · intro h x y hx hy
    have hy' : Relation.ReflTransGen R x y := by
      simpa only [Relation.reflTransGen_idem] using hy
    exact h hx hy'

/-- Proves: the persistent diagonal grade is unchanged by replacing the
one-step dynamics with its reflexive-transitive closure.

Relation: `R` and `Relation.ReflTransGen R`.
Closure: reflexive-transitive in each coordinate.
Strategy: unrestricted.
Trust: kernel plus Mathlib relation library.
-/
theorem d1p_reflTransGen_iff {α β : Type}
    (R : α → α → Prop) (q : α → β) (x y : α) :
    D1p (Relation.ReflTransGen R) q x y ↔ D1p R q x y := by
  constructor
  · intro h x' y' hx hy
    exact h x' y'
      (Relation.ReflTransGen.single hx)
      (Relation.ReflTransGen.single hy)
  · intro h x' y' hx hy
    have hx' : Relation.ReflTransGen R x x' := by
      simpa only [Relation.reflTransGen_idem] using hx
    have hy' : Relation.ReflTransGen R y y' := by
      simpa only [Relation.reflTransGen_idem] using hy
    exact h x' y' hx' hy'

/-- Proves: the represented persistent grade `D2At` is unchanged by completion
of its dynamics.  The comparator representation component is transported
identically; only the `D1p` component uses the completion law.

Relation: `R` and `Relation.ReflTransGen R`.
Closure: reflexive-transitive in each coordinate.
Strategy: unrestricted.
Trust: kernel plus Mathlib relation library.
-/
theorem d2At_reflTransGen_iff {α β : Type}
    (Represented : (α → α → Prop) → Prop) (R : α → α → Prop)
    (q : α → β) (x y : α) :
    D2At Represented (Relation.ReflTransGen R) q x y ↔
      D2At Represented R q x y := by
  constructor
  · rintro ⟨hD1, hCmp⟩
    exact ⟨(d1p_reflTransGen_iff R q x y).1 hD1, hCmp⟩
  · rintro ⟨hD1, hCmp⟩
    exact ⟨(d1p_reflTransGen_iff R q x y).2 hD1, hCmp⟩

/-- Complete a licensing datum by replacing its one-step dynamics with its
reflexive-transitive closure.  Every other field is definitionally preserved. -/
def completeDatum (D : LicensingDatum.{u,v,w}) : LicensingDatum.{u,v,w} :=
  { D with dynamics := Relation.ReflTransGen D.dynamics }

/-- Proves: completion is idempotent on the dynamics field.

Relation: `D.dynamics`.
Closure: reflexive-transitive, applied twice.
Strategy: unrestricted.
Trust: kernel plus Mathlib relation library.
-/
theorem completeDatum_idem (D : LicensingDatum.{u,v,w}) :
    (completeDatum (completeDatum D)).dynamics =
      (completeDatum D).dynamics := by
  exact Relation.reflTransGen_idem

/-- The identity maps form a concrete licensing morphism from a datum into its
completion.  The only non-reflexive field is dynamics preservation, witnessed
by the one-step injection into `Relation.ReflTransGen`.

Relation: `D.dynamics` to `Relation.ReflTransGen D.dynamics`.
Closure: target one-step relation is the source closure.
Strategy: unrestricted.
Trust: kernel plus Mathlib relation library.
-/
def toComplete (D : LicensingDatum.{u,v,w}) : Hom D (completeDatum D) where
  stateMap := id
  policyMap := id
  outputMap := id
  tag := LicenseTransportTag.identity
  dynamics_preserve := fun h => Relation.ReflTransGen.single h
  policy_preserve := fun h => h
  consume_preserve := fun _ => rfl
  license_preserve := fun _ _ h => h
  license_reflect := fun _ _ h => h

/-- Proves: a licensing datum and its completed dynamics carry exactly the same
persistent license at every state. -/
theorem box_license_completion_invariant (D : LicensingDatum.{0,v,w})
    (x : D.Carrier) :
    Box (completeDatum D).dynamics D.license x ↔
      Box D.dynamics D.license x :=
  box_reflTransGen_iff D.dynamics D.license x

/-- The one-step natural-number shift dynamics. -/
def shiftStep (n m : ℕ) : Prop :=
  m = n + 1

/-- Proves: the reflexive-transitive closure of one-step shift is precisely the
natural-number order.

Relation: `shiftStep`.
Closure: reflexive-transitive.
Strategy: unrestricted.
Trust: kernel plus Mathlib natural-number arithmetic.
-/
theorem reflTransGen_shiftStep_iff_le (N n : ℕ) :
    Relation.ReflTransGen shiftStep N n ↔ N ≤ n := by
  constructor
  · intro h
    induction h with
    | refl => exact Nat.le_refl N
    | tail _ hstep ih =>
        change _ = _ + 1 at hstep
        rw [hstep]
        exact Nat.le_succ_of_le ih
  · intro h
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    clear h
    induction k with
    | zero =>
        simpa using (Relation.ReflTransGen.refl :
          Relation.ReflTransGen shiftStep N N)
    | succ k ih =>
        rw [Nat.add_succ]
        exact Relation.ReflTransGen.tail ih (by rfl)

/-- Proves: compact-uniform separation is a persistent pointwise separation
predicate over the completed index dynamics.

Relation: `Relation.ReflTransGen shiftStep`.
Closure: `Box` applies reflexive-transitive closure once more, which is
idempotent.
Strategy: unrestricted.
Trust: kernel plus Mathlib analysis and relation libraries.
-/
theorem compactUniformSeparation_iff_box_shift
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) :
    CompactUniformSeparation F U ↔
      ∀ K ⊆ U, IsCompact K →
        ∃ ε, 0 < ε ∧ ∃ N,
          Box (Relation.ReflTransGen shiftStep)
            (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N := by
  constructor
  · intro h K hKU hK
    rcases h K hKU hK with ⟨ε, hε, N, hN⟩
    refine ⟨ε, hε, N, ?_⟩
    apply (box_reflTransGen_iff shiftStep
      (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N).2
    refine ⟨hN N (Nat.le_refl N), ?_⟩
    intro n hn
    exact hN n ((reflTransGen_shiftStep_iff_le N n).1 hn)
  · intro h K hKU hK
    rcases h K hKU hK with ⟨ε, hε, N, hBox⟩
    refine ⟨ε, hε, N, ?_⟩
    have hBase : Box shiftStep (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N :=
      (box_reflTransGen_iff shiftStep
        (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N).1 hBox
    intro n hn
    exact hBase.persists n ((reflTransGen_shiftStep_iff_le N n).2 hn)

/-- Proves: the metric persistent license is the same `Box` computation rule
on the uncompleted shift relation.  Completion invariance converts freely
between this statement and `compactUniformSeparation_iff_box_shift`. -/
theorem metricPersistentLicense_iff_box_shift
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) :
    MetricPersistentLicense F U ↔
      ∀ K ⊆ U, IsCompact K →
        ∃ ε, 0 < ε ∧ ∃ N,
          Box shiftStep (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N := by
  constructor
  · intro h K hKU hK
    have hSep : CompactUniformSeparation F U :=
      (metricPersistentLicense_iff_compactUniformSeparation F U).1 h
    rcases (compactUniformSeparation_iff_box_shift F U).1 hSep K hKU hK with
      ⟨ε, hε, N, hBox⟩
    exact ⟨ε, hε, N,
      (box_reflTransGen_iff shiftStep
        (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N).1 hBox⟩
  · intro h
    apply (metricPersistentLicense_iff_compactUniformSeparation F U).2
    apply (compactUniformSeparation_iff_box_shift F U).2
    intro K hKU hK
    rcases h K hKU hK with ⟨ε, hε, N, hBox⟩
    exact ⟨ε, hε, N,
      (box_reflTransGen_iff shiftStep
        (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N).2 hBox⟩

/-- The fourth Licensed Boundary computation rule bundled at one generic and
one analytic instance: `Box`, `D1p`, datum licensing, and the metric license all
survive completion exactly. -/
theorem completion_rules_complete {α β : Type}
    (R : α → α → Prop) (P : α → Prop) (q : α → β) (x y : α)
    (D : LicensingDatum.{0,v,w}) (d : D.Carrier)
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) :
    (Box (Relation.ReflTransGen R) P x ↔ Box R P x) ∧
    (D1p (Relation.ReflTransGen R) q x y ↔ D1p R q x y) ∧
    (Box (completeDatum D).dynamics D.license d ↔
      Box D.dynamics D.license d) ∧
    (MetricPersistentLicense F U ↔
      ∀ K ⊆ U, IsCompact K →
        ∃ ε, 0 < ε ∧ ∃ N,
          Box shiftStep (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N) :=
  ⟨box_reflTransGen_iff R P x,
    d1p_reflTransGen_iff R q x y,
    box_license_completion_invariant D d,
    metricPersistentLicense_iff_box_shift F U⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingCompletionRule
