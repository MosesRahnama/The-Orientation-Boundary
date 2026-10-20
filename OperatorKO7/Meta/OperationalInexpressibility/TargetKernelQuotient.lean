import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore

/-!
# Canonical target-kernel quotient

For a target `P : X → V`, the smallest lawful representation is the quotient of `X`
by equality of target values. Any observer licensed for `P` refines this quotient, and the
quotient itself is licensed for `P`. Thus it is the coarsest observer, up to equality of
observer kernels, that preserves exactly the distinctions needed by the target.

Relation: equality of target outputs and observer refinement by fiber inclusion.
Closure: equivalence closure supplied by equality.
Strategy: not applicable.
Trust: kernel checked; quotient equality uses the baseline axiom `Quot.sound`.
Scope: arbitrary types and arbitrary targets. No finiteness, decidable equality, surjectivity,
or inhabitance assumptions are used.
Non-vacuity: `parityTarget_fixture` below has both equal-output and distinct-output fibers.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.TargetKernel

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe u v w z

/-- The equivalence relation that forgets exactly the distinctions irrelevant to `P`. -/
def targetKernelSetoid {X : Type u} {V : Type v} (P : X → V) : Setoid X :=
  observerSetoid P

/-- The quotient of source states by equality of target values. -/
abbrev TargetKernelQuotient {X : Type u} {V : Type v} (P : X → V) : Type u :=
  Quotient (targetKernelSetoid P)

/-- Canonical projection to the target-kernel quotient. -/
def targetKernelQuotientMap {X : Type u} {V : Type v} (P : X → V) (x : X) :
    TargetKernelQuotient P :=
  Quotient.mk (targetKernelSetoid P) x

/-- The target descends canonically to its own kernel quotient. -/
def targetKernelDecoder {X : Type u} {V : Type v} (P : X → V) :
    TargetKernelQuotient P → V :=
  Quotient.lift P (fun _ _ h => h)

@[simp] theorem targetKernelDecoder_map {X : Type u} {V : Type v}
    (P : X → V) (x : X) :
    targetKernelDecoder P (targetKernelQuotientMap P x) = P x := rfl

/-- The target quotient identifies exactly, not merely at least, the target-equal states. -/
theorem targetKernelQuotientMap_eq_iff {X : Type u} {V : Type v}
    (P : X → V) (x y : X) :
    targetKernelQuotientMap P x = targetKernelQuotientMap P y ↔ P x = P y := by
  constructor
  · intro h
    exact congrArg (targetKernelDecoder P) h
  · intro h
    exact Quotient.sound h

/-- The canonical target quotient is licensed for the target it was built to preserve. -/
theorem targetKernelQuotient_licenses_target {X : Type u} {V : Type v}
    (P : X → V) :
    Licensed (targetKernelQuotientMap P) P := by
  intro x y hxy
  exact (targetKernelQuotientMap_eq_iff P x y).1 hxy

/-- A target is licensed by an observer exactly when that observer refines the target-kernel
quotient. This is the universal representation theorem for one target. -/
theorem licensed_iff_refines_targetKernelQuotient
    {X : Type u} {Q : Type w} {V : Type v}
    (q : X → Q) (P : X → V) :
    Licensed q P ↔ ObserverRefines q (targetKernelQuotientMap P) := by
  constructor
  · intro hlic x y hxy
    exact (targetKernelQuotientMap_eq_iff P x y).2 (hlic x y hxy)
  · intro href x y hxy
    exact (targetKernelQuotientMap_eq_iff P x y).1 (href hxy)

/-- Every observer licensed for `P` refines the target-kernel quotient. Hence the target
quotient is the coarsest sufficient observer for `P` in the observer-refinement order. -/
theorem every_licensed_observer_refines_targetKernelQuotient
    {X : Type u} {Q : Type w} {V : Type v}
    (q : X → Q) (P : X → V) (hlic : Licensed q P) :
    ObserverRefines q (targetKernelQuotientMap P) :=
  (licensed_iff_refines_targetKernelQuotient q P).1 hlic

/-- The coarsest-sufficient characterization packages both directions: the target quotient is
licensed, and every licensed observer lies above it in the refinement order. -/
theorem targetKernelQuotient_coarsest_sufficient
    {X : Type u} {V : Type v} (P : X → V) :
    Licensed (targetKernelQuotientMap P) P ∧
      ∀ {Q : Type w} (q : X → Q), Licensed q P →
        ObserverRefines q (targetKernelQuotientMap P) := by
  constructor
  · exact targetKernelQuotient_licenses_target P
  · intro Q q hlic
    exact every_licensed_observer_refines_targetKernelQuotient q P hlic

/-- Any sufficient observer that is also no finer than the canonical target quotient has
exactly the same observer kernel as the target quotient. This is uniqueness up to observer
kernel equivalence, with no choice of quotient representatives. -/
theorem targetKernelQuotient_unique_up_to_kernel
    {X : Type u} {Q : Type w} {V : Type v}
    (q : X → Q) (P : X → V)
    (hlic : Licensed q P)
    (hminimal : ObserverRefines (targetKernelQuotientMap P) q) :
    ∀ x y,
      q x = q y ↔
        targetKernelQuotientMap P x = targetKernelQuotientMap P y := by
  have hforward : ObserverRefines q (targetKernelQuotientMap P) :=
    every_licensed_observer_refines_targetKernelQuotient q P hlic
  exact (mutual_refinement_iff_same_kernel q (targetKernelQuotientMap P)).1
    ⟨hforward, hminimal⟩

/-- Equivalent formulation of uniqueness: a sufficient observer is canonical exactly when
its kernel is the target kernel. -/
theorem licensed_and_targetKernel_refines_iff_same_kernel
    {X : Type u} {Q : Type w} {V : Type v}
    (q : X → Q) (P : X → V) :
    (Licensed q P ∧ ObserverRefines (targetKernelQuotientMap P) q) ↔
      ∀ x y, q x = q y ↔ P x = P y := by
  constructor
  · rintro ⟨hlic, hminimal⟩ x y
    have hkernel := targetKernelQuotient_unique_up_to_kernel q P hlic hminimal x y
    exact hkernel.trans (targetKernelQuotientMap_eq_iff P x y)
  · intro h
    constructor
    · intro x y hxy
      exact (h x y).1 hxy
    · intro x y hxy
      exact (h x y).2 ((targetKernelQuotientMap_eq_iff P x y).1 hxy)

/-! ## Joint observers and target families -/

/-- One observation containing every coordinate in an arbitrary indexed family. -/
def jointObserver {X : Type u} {I : Type z} {Q : I → Type v}
    (q : (i : I) → X → Q i) (x : X) : (i : I) → Q i := fun i => q i x

/-- The joint observation identifies exactly the pairs identified by every coordinate. -/
theorem jointObserver_eq_iff {X : Type u} {I : Type z} {Q : I → Type v}
    (q : (i : I) → X → Q i) (x y : X) :
    jointObserver q x = jointObserver q y ↔ ∀ i, q i x = q i y :=
  ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- Refining the joint observer is equivalent to refining every coordinate. -/
theorem refines_jointObserver_iff
    {X : Type u} {I : Type z} {Q : I → Type v} {A : Type w}
    (r : X → A) (q : (i : I) → X → Q i) :
    ObserverRefines r (jointObserver q) ↔ ∀ i, ObserverRefines r (q i) := by
  constructor
  · intro h i x y hxy
    exact congrFun (h hxy) i
  · intro h x y hxy
    exact funext (fun i => h i hxy)

/-- A joint target is determined exactly when each of its coordinates is determined. -/
theorem licensed_joint_target_iff
    {X : Type u} {I : Type z} {V : I → Type v} {A : Type w}
    (q : X → A) (P : (i : I) → X → V i) :
    Licensed q (jointObserver P) ↔ ∀ i, Licensed q (P i) := by
  constructor
  · intro h i x y hxy
    exact congrFun (h x y hxy) i
  · intro h x y hxy
    exact funext (fun i => h i x y hxy)

/-- The joint observation is the least common refinement of its coordinates. -/
theorem jointObserver_least_common_refinement
    {X : Type u} {I : Type z} {Q : I → Type v}
    (q : (i : I) → X → Q i) :
    (∀ i, ObserverRefines (jointObserver q) (q i)) ∧
      ∀ {A : Type w} (r : X → A),
        (∀ i, ObserverRefines r (q i)) → ObserverRefines r (jointObserver q) := by
  refine ⟨?_, fun r h => (refines_jointObserver_iff r q).2 h⟩
  intro i x y hxy
  exact congrFun hxy i

/-- The quotient by joint target equality is the coarsest observer determining
the whole target family, without finiteness or inhabitance assumptions. -/
theorem licensed_family_iff_refines_jointTargetKernel
    {X : Type u} {I : Type z} {V : I → Type v} {A : Type w}
    (q : X → A) (P : (i : I) → X → V i) :
    (∀ i, Licensed q (P i)) ↔
      ObserverRefines q (targetKernelQuotientMap (jointObserver P)) := by
  rw [← licensed_joint_target_iff, licensed_iff_refines_targetKernelQuotient]

/-- Joint target equality has the same quotient as the actual range of targets. -/
noncomputable def targetKernelRangeEquiv {X : Type u} {V : Type v}
    (P : X → V) : TargetKernelQuotient P ≃ Set.range P where
  toFun := Quotient.lift (fun x => ⟨P x, ⟨x, rfl⟩⟩)
    (fun _ _ h => Subtype.ext h)
  invFun := fun value => targetKernelQuotientMap P (Classical.choose value.property)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    apply (targetKernelQuotientMap_eq_iff P _ x).2
    exact Classical.choose_spec (show P x ∈ Set.range P from ⟨x, rfl⟩)
  right_inv := by
    intro value
    apply Subtype.ext
    exact Classical.choose_spec value.property

/-- The range equivalence retains the original target value on each source state. -/
theorem targetKernelRangeEquiv_map {X : Type u} {V : Type v}
    (P : X → V) (x : X) :
    (targetKernelRangeEquiv P (targetKernelQuotientMap P x)).val = P x := rfl

/-- Two independent Boolean observation coordinates. -/
def coordinateObserver (i : Bool) (x : Bool × Bool) : Bool :=
  if i then x.2 else x.1

/-- Together the two coordinates recover the actual source pair. -/
theorem joint_coordinateObserver_injective :
    Function.Injective (jointObserver coordinateObserver) := by
  intro x y h
  apply Prod.ext
  · simpa [jointObserver, coordinateObserver] using congrFun h false
  · simpa [jointObserver, coordinateObserver] using congrFun h true

/-- Neither coordinate alone determines the other. -/
theorem coordinateObserver_neither_licenses_other :
    ¬ Licensed (coordinateObserver false) (coordinateObserver true) ∧
      ¬ Licensed (coordinateObserver true) (coordinateObserver false) := by
  constructor
  · intro h
    have hbad : (false : Bool) = true := h (false, false) (false, true) rfl
    cases hbad
  · intro h
    have hbad : (false : Bool) = true := h (false, false) (true, false) rfl
    cases hbad

/-! ## Non-vacuous finite fixture -/

/-- A target with two nonempty fibers. -/
def parityTarget_fixture (i : Fin 4) : Bool := decide (i.val % 2 = 0)

/-- Two distinct source states are identified by the canonical target quotient. -/
theorem parityTarget_fixture_identifies_even :
    targetKernelQuotientMap parityTarget_fixture (0 : Fin 4) =
      targetKernelQuotientMap parityTarget_fixture (2 : Fin 4) := by
  apply (targetKernelQuotientMap_eq_iff parityTarget_fixture _ _).2
  decide

/-- The same quotient separates states with distinct target values. -/
theorem parityTarget_fixture_separates_odd :
    ¬ targetKernelQuotientMap parityTarget_fixture (0 : Fin 4) =
      targetKernelQuotientMap parityTarget_fixture (1 : Fin 4) := by
  intro h
  have hp := (targetKernelQuotientMap_eq_iff parityTarget_fixture _ _).1 h
  norm_num [parityTarget_fixture] at hp



end OperatorKO7.Meta.OperationalInexpressibility.TargetKernel
