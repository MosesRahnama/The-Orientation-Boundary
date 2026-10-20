import OperatorKO7.Meta.OperationalInexpressibility.TargetKernelQuotient
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore

/-!
# Joint-target recovery and finite side-channel capacity

Multiple operational tasks are represented by a product target. Joint licensing is exactly the
conjunction of the component licenses. Independent side labels compose by product, but the exact
minimum alphabet is determined by the realized joint target values inside observer fibers, not by
a product of the separate minima. A duplicated-target control shows why naive additive or
multiplicative accounting can overcount.

No concrete rewrite system, recursor, or KO7 rule is imported.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.JointTargetCapacity

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

universe u v w z u' v'

/-- Product target for two operational obligations on the same source state. -/
def pairedTarget {X : Type u} {V : Type v} {W : Type w}
    (P : X → V) (R : X → W) : X → V × W := fun x => (P x, R x)

/-- An observer determines the paired target exactly when it determines each component. -/
theorem licensed_pairedTarget_iff
    {X : Type u} {Q : Type z} {V : Type v} {W : Type w}
    (q : X → Q) (P : X → V) (R : X → W) :
    Licensed q (pairedTarget P R) ↔ Licensed q P ∧ Licensed q R := by
  constructor
  · intro h
    constructor
    · intro x y hxy
      exact congrArg Prod.fst (h x y hxy)
    · intro x y hxy
      exact congrArg Prod.snd (h x y hxy)
  · rintro ⟨hP, hR⟩ x y hxy
    exact Prod.ext (hP x y hxy) (hR x y hxy)

/-- Side labels that separately recover two targets compose into a product side label recovering
both targets simultaneously. This is an upper construction, not an assertion that product
cardinality is minimal. -/
theorem product_side_channels_license_pairedTarget
    {X : Type u} {Q : Type z} {V : Type v} {W : Type w}
    {C : Type u'} {D : Type v'}
    (q : X → Q) (P : X → V) (R : X → W)
    (s : X → C) (t : X → D)
    (hP : FactorsThrough (fun x => (q x, s x)) P)
    (hR : FactorsThrough (fun x => (q x, t x)) R) :
    FactorsThrough (fun x => (q x, (s x, t x))) (pairedTarget P R) := by
  intro x y hxy
  have hq : q x = q y := congrArg Prod.fst hxy
  have hst : (s x, t x) = (s y, t y) := congrArg Prod.snd hxy
  have hs : s x = s y := congrArg Prod.fst hst
  have ht : t x = t y := congrArg Prod.snd hst
  exact Prod.ext (hP (Prod.ext hq hs)) (hR (Prod.ext hq ht))

/-- Duplicating a target does not create a new licensing requirement. -/
theorem licensed_duplicatedTarget_iff
    {X : Type u} {Q : Type z} {V : Type v}
    (q : X → Q) (P : X → V) :
    Licensed q (pairedTarget P P) ↔ Licensed q P := by
  rw [licensed_pairedTarget_iff]
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    exact ⟨h, h⟩

section Finite

variable {X : Type u} {Q : Type z} {V : Type v} {W : Type w}
variable [Fintype X] [DecidableEq Q] [DecidableEq V] [DecidableEq W]

/-- The exact finite side-alphabet theorem applies to the realized joint target itself. The
minimum is therefore the joint fiber multiplicity, which may be strictly smaller than a product
of separately sufficient alphabet sizes. -/
theorem pairedTarget_exact_side_capacity
    (q : X → Q) (P : X → V) (R : X → W) :
    (∃ s : X → Fin (fiberMultiplicity q (pairedTarget P R)),
        FactorsThrough (fun x => (q x, s x)) (pairedTarget P R)) ∧
      ∀ {C : Type u'} [Fintype C] (s : X → C),
        FactorsThrough (fun x => (q x, s x)) (pairedTarget P R) →
          fiberMultiplicity q (pairedTarget P R) ≤ Fintype.card C :=
  fiberMultiplicity_is_minimum_side_channel_cardinality q (pairedTarget P R)

/-- Constant observer on a two-state source. -/
def constantBoolObserver (_ : Bool) : Unit := ()

/-- Identity Boolean target. -/
def boolTarget (b : Bool) : Bool := b

/-- One Boolean target has two realized values in the unique observation fiber. -/
theorem boolTarget_fiberMultiplicity_two :
    fiberMultiplicity constantBoolObserver boolTarget = 2 := by decide

/-- Two identical copies of that target still have only two realized joint values, not four. -/
theorem duplicatedBoolTarget_fiberMultiplicity_two :
    fiberMultiplicity constantBoolObserver (pairedTarget boolTarget boolTarget) = 2 := by decide

/-- The product of the separate minima can strictly overcount the true joint minimum. -/
theorem duplicated_target_product_bound_not_tight :
    fiberMultiplicity constantBoolObserver (pairedTarget boolTarget boolTarget) <
      fiberMultiplicity constantBoolObserver boolTarget *
        fiberMultiplicity constantBoolObserver boolTarget := by decide

end Finite

end OperatorKO7.Meta.OperationalInexpressibility.JointTargetCapacity
