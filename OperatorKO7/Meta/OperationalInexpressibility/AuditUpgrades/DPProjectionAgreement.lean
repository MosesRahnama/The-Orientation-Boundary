import OperatorKO7.Meta.Recursor.InformationEquivalence

/-!
# Direct-mass agreement and counter-projection separation of the two orbit families

Proves: the relation `InformationEquivalentModDP` holds for every pair of orbits, so it records
the stipulated invariance of the functional and nothing about the orbits; the counter projection
of the dependency-pair method reads the counter depth `n` on the recursor orbit and `0` on every
later stage of the circular-reference orbit; agreement of counter projections is an equivalence
relation, and it separates the recursor orbit from the circular-reference orbit, while every
linear-growth-invariant functional of direct mass agrees on them.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the orbits `RecursorOrbit b s` and `CircularReferenceOrbit A B` of `CircularIdentity.lean`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.DPProjectionAgreement

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.InformationEquivalence

/-- The stipulated relation holds for every pair of orbits. -/
theorem informationEquivalentModDP_total (orbit1 orbit2 : Nat → Trace) :
    InformationEquivalentModDP orbit1 orbit2 := by
  intro E D _ _ _ h1 h2
  exact E.respects_linear_growth _ _ h1 h2

/-- Number of leading successor constructors of a term. -/
def deltaDepth : Trace → Nat
  | delta t => deltaDepth t + 1
  | _ => 0

/-- The counter projection of the dependency-pair method: the successor depth of the third
argument at a recursor head, and zero at every other head. -/
def counterProjection : Trace → Nat
  | recΔ _ _ n => deltaDepth n
  | _ => 0

theorem deltaDepth_counterTrace (n : Nat) : deltaDepth (counterTrace n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [counterTrace, deltaDepth, ih]

/-- On the recursor orbit the counter projection reads the counter depth. -/
theorem counterProjection_recursorOrbit (b s : Trace) (n : Nat) :
    counterProjection (RecursorOrbit b s n) = n := by
  simp [RecursorOrbit, counterProjection, deltaDepth_counterTrace]

/-- On every later stage of the circular-reference orbit the counter projection reads zero. -/
theorem counterProjection_circularOrbit_succ (A B : Trace) (n : Nat) :
    counterProjection (CircularReferenceOrbit A B (n + 1)) = 0 := by
  simp [CircularReferenceOrbit, counterProjection]

/-- Agreement of the counter projections of two orbits at every index. -/
def CounterProjectionAgreement (orbit1 orbit2 : Nat → Trace) : Prop :=
  ∀ n : Nat, counterProjection (orbit1 n) = counterProjection (orbit2 n)

theorem CounterProjectionAgreement.refl (orbit : Nat → Trace) : CounterProjectionAgreement orbit orbit :=
  fun _ => rfl

theorem CounterProjectionAgreement.symm {orbit1 orbit2 : Nat → Trace}
    (h : CounterProjectionAgreement orbit1 orbit2) : CounterProjectionAgreement orbit2 orbit1 :=
  fun n => (h n).symm

theorem CounterProjectionAgreement.trans {orbit1 orbit2 orbit3 : Nat → Trace}
    (h12 : CounterProjectionAgreement orbit1 orbit2) (h23 : CounterProjectionAgreement orbit2 orbit3) :
    CounterProjectionAgreement orbit1 orbit3 :=
  fun n => (h12 n).trans (h23 n)

/-- The counter projection separates the recursor orbit from the circular-reference orbit. -/
theorem dpProjection_separates_recursor_and_circular (b s A B : Trace) :
    ¬ CounterProjectionAgreement (RecursorOrbit b s) (CircularReferenceOrbit A B) := by
  intro h
  have h1 := h 1
  rw [counterProjection_recursorOrbit, counterProjection_circularOrbit_succ] at h1
  exact Nat.one_ne_zero h1

/-- Every linear-growth-invariant functional of direct mass agrees on the two families, while
the counter projection separates them. -/
theorem direct_mass_agrees_counter_projection_separates (b s A B : Trace) :
    InformationEquivalentModDP (RecursorOrbit b s) (CircularReferenceOrbit A B) ∧
      ¬ CounterProjectionAgreement (RecursorOrbit b s) (CircularReferenceOrbit A B) :=
  ⟨informationEquivalentModDP_total _ _, dpProjection_separates_recursor_and_circular b s A B⟩

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.DPProjectionAgreement
