import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Recorded outcomes and post-measurement states

Proof graph: Audit/ledgers/operational-inexpressibility/OBSERVATION-EXTENSIONS-PROOF-GRAPH.md,
nodes I1 and I2. Deterministic instruments and finite stochastic kernels are separate objects.
Recovery retains both the outcome record and the state. No heat law is assumed or inferred.
-/

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryObserver.InstrumentLoss

structure Instrument (X Y Z : Type*) where
  read : X → Y
  post : X → Z

def joint {X Y Z : Type*} (I : Instrument X Y Z) (x : X) : Y × Z :=
  (I.read x, I.post x)

def Recoverable {X Y Z : Type*} (I : Instrument X Y Z) : Prop :=
  ∃ restore : Y × Z → X, ∀ x, restore (joint I x) = x

/-- On a nonempty input type, joint injectivity is necessary and sufficient for restoration. -/
theorem recoverable_iff_joint_injective {X Y Z : Type*} [Nonempty X]
    (I : Instrument X Y Z) : Recoverable I ↔ Function.Injective (joint I) := by
  classical
  constructor
  · rintro ⟨r, hr⟩ x x' he
    exact (hr x).symm.trans ((congrArg r he).trans (hr x'))
  · intro hi
    let restore : Y × Z → X := fun yz =>
      if h : ∃ x, joint I x = yz then Classical.choose h
      else Classical.choice ‹Nonempty X›
    refine ⟨restore, ?_⟩
    intro x
    have h : ∃ x', joint I x' = joint I x := ⟨x, rfl⟩
    change (if h : ∃ x', joint I x' = joint I x then Classical.choose h
      else Classical.choice ‹Nonempty X›) = x
    rw [dif_pos h]
    exact hi (Classical.choose_spec h)

/-- Composition stores the first outcome beside the outcome of the second operation. -/
def compose {X Y Z W T : Type*} (I : Instrument X Y Z) (J : Instrument Z W T) :
    Instrument X (Y × W) T where
  read x := (I.read x, J.read (I.post x))
  post x := J.post (I.post x)

theorem joint_compose_eq_iff {X Y Z W T : Type*}
    (I : Instrument X Y Z) (J : Instrument Z W T) (x x' : X) :
    joint (compose I J) x = joint (compose I J) x' ↔
      I.read x = I.read x' ∧ joint J (I.post x) = joint J (I.post x') := by
  simp only [joint, compose, Prod.mk.injEq]
  tauto

/-- Once both the outcome and post-state coincide, later processing cannot separate the inputs. -/
theorem joint_collision_persists {X Y Z W T : Type*}
    (I : Instrument X Y Z) (J : Instrument Z W T) {x x' : X}
    (h : joint I x = joint I x') : joint (compose I J) x = joint (compose I J) x' := by
  apply (joint_compose_eq_iff I J x x').mpr
  exact ⟨congrArg Prod.fst h, congrArg (joint J) (congrArg Prod.snd h)⟩

theorem compose_injective {X Y Z W T : Type*}
    (I : Instrument X Y Z) (J : Instrument Z W T)
    (hI : Function.Injective (joint I)) (hJ : Function.Injective (joint J)) :
    Function.Injective (joint (compose I J)) := by
  intro x x' h
  obtain ⟨hy, hz⟩ := (joint_compose_eq_iff I J x x').mp h
  exact hI (Prod.ext hy (hJ hz))

/-- Invertibility of the composite forces invertibility of the first joint output. -/
theorem first_injective_of_composite {X Y Z W T : Type*}
    (I : Instrument X Y Z) (J : Instrument Z W T)
    (h : Function.Injective (joint (compose I J))) : Function.Injective (joint I) := by
  intro x x' he
  exact h (joint_collision_persists I J he)

theorem compose_recoverable {X Y Z W T : Type*}
    (I : Instrument X Y Z) (J : Instrument Z W T)
    (hI : Recoverable I) (hJ : Recoverable J) : Recoverable (compose I J) := by
  obtain ⟨rI, hrI⟩ := hI
  obtain ⟨rJ, hrJ⟩ := hJ
  refine ⟨fun out => rI (out.1.1, rJ (out.1.2, out.2)), ?_⟩
  intro x
  change rI (I.read x, rJ (joint J (I.post x))) = x
  rw [hrJ]
  exact hrI x

def silentKeep : Instrument Bool Unit Bool := ⟨fun _ => (), id⟩
def silentErase : Instrument Bool Unit Bool := ⟨fun _ => (), fun _ => false⟩
def readAndErase : Instrument Bool Bool Bool := ⟨id, fun _ => false⟩

theorem equal_records_different_recovery :
    silentKeep.read = silentErase.read ∧ Recoverable silentKeep ∧ ¬ Recoverable silentErase := by
  refine ⟨rfl, ⟨Prod.snd, fun _ => rfl⟩, ?_⟩
  rintro ⟨r, hr⟩
  have h : false = true := (hr false).symm.trans (hr true)
  cases h

/-- State reset can be reversed from a retained outcome, but not from the reset state alone. -/
theorem retained_record_recovers_reset :
    Recoverable readAndErase ∧ ¬ Function.Injective readAndErase.post := by
  refine ⟨⟨Prod.fst, fun _ => rfl⟩, ?_⟩
  intro h
  have he : false = true := h rfl
  cases he

/-- A finite stochastic instrument assigns a joint probability to outcome and post-state. -/
structure StochasticInstrument (X Y Z : Type*) [Fintype Y] [Fintype Z] where
  weight : X → Y → Z → ℝ
  nonneg : ∀ x y z, 0 ≤ weight x y z
  total : ∀ x, ∑ y, ∑ z, weight x y z = 1

noncomputable def outcomeLaw {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) (x : X) (y : Y) : ℝ := ∑ z, I.weight x y z

noncomputable def stateLaw {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) (x : X) (z : Z) : ℝ := ∑ y, I.weight x y z

theorem outcomeLaw_normalized {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) (x : X) : ∑ y, outcomeLaw I x y = 1 := I.total x

theorem stateLaw_normalized {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) (x : X) : ∑ z, stateLaw I x z = 1 := by
  unfold stateLaw
  rw [Finset.sum_comm]
  exact I.total x

/-- A fair independent outcome is emitted while the hidden bit is retained or reset. -/
noncomputable def randomRead (erase : Bool) : StochasticInstrument Bool Bool Bool where
  weight x _ z := if z = (if erase then false else x) then 1 / 2 else 0
  nonneg := by intro x y z; split_ifs <;> norm_num
  total := by
    intro x
    cases erase <;> cases x <;> norm_num [Fintype.sum_bool]

theorem randomRead_outcome (erase x y : Bool) : outcomeLaw (randomRead erase) x y = 1 / 2 := by
  cases erase <;> cases x <;> cases y <;> norm_num [outcomeLaw, randomRead, Fintype.sum_bool]

theorem randomRead_state (erase x z : Bool) :
    stateLaw (randomRead erase) x z = if z = (if erase then false else x) then 1 else 0 := by
  cases erase <;> cases x <;> cases z <;> norm_num [stateLaw, randomRead, Fintype.sum_bool]

/-- Equal outcome distributions do not determine state change, even for normalized kernels. -/
theorem same_outcome_different_state :
    (∀ x y, outcomeLaw (randomRead false) x y = outcomeLaw (randomRead true) x y) ∧
      stateLaw (randomRead false) true true ≠ stateLaw (randomRead true) true true := by
  constructor
  · intro x y
    rw [randomRead_outcome, randomRead_outcome]
  · rw [randomRead_state, randomRead_state]
    norm_num

/-- Recovery on every positive-probability joint outcome. -/
def StochasticRecoverable {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) : Prop :=
  ∃ r : Y × Z → X, ∀ x y z, 0 < I.weight x y z → r (y, z) = x

theorem randomRead_keep_recovers : StochasticRecoverable (randomRead false) := by
  refine ⟨Prod.snd, ?_⟩
  intro x y z h
  change z = x
  by_contra he
  simp [randomRead, he] at h

theorem randomRead_erase_not_recovers : ¬ StochasticRecoverable (randomRead true) := by
  rintro ⟨r, hr⟩
  have h0 := hr false false false (by norm_num [randomRead])
  have h1 := hr true false false (by norm_num [randomRead])
  have h : false = true := h0.symm.trans h1
  cases h

end OperatorKO7.Meta.BoundaryObserver.InstrumentLoss
