import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
import OperatorKO7.Meta.DistinctionBoundary.GodelQuoteEvalPeak
import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

set_option autoImplicit false

/-!
# License expiry category

An expiry object is a concrete issue state, one live dynamics step, a license
holding at issue time, and failure of that same license at the consume state.
Morphisms preserve the dynamics and license and map the distinguished issue and
consume states.  Three instances are taken from the live KO7 development: the
coalescing equality guard, the quote/eval peak, and role erasure.
-/

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory

open OperatorKO7 Trace
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

universe u v w

structure ExpiryObject where
  Carrier : Type u
  dynamics : Carrier → Carrier → Prop
  license : Carrier → Prop
  issue : Carrier
  consume : Carrier
  crossing : dynamics issue consume
  issue_licensed : license issue
  consume_unlicensed : ¬ license consume

structure Hom (A : ExpiryObject.{u}) (B : ExpiryObject.{v}) where
  toFun : A.Carrier → B.Carrier
  issue_map : toFun A.issue = B.issue
  consume_map : toFun A.consume = B.consume
  dynamics_preserve : ∀ {x y}, A.dynamics x y → B.dynamics (toFun x) (toFun y)
  license_preserve : ∀ {x}, A.license x → B.license (toFun x)

namespace Hom

def id (A : ExpiryObject) : Hom A A where
  toFun := _root_.id
  issue_map := rfl
  consume_map := rfl
  dynamics_preserve := fun h => h
  license_preserve := fun h => h

def comp {A : ExpiryObject.{u}} {B : ExpiryObject.{v}} {C : ExpiryObject.{w}}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := g.toFun ∘ f.toFun
  issue_map := by rw [Function.comp_apply, f.issue_map, g.issue_map]
  consume_map := by rw [Function.comp_apply, f.consume_map, g.consume_map]
  dynamics_preserve := fun h => g.dynamics_preserve (f.dynamics_preserve h)
  license_preserve := fun h => g.license_preserve (f.license_preserve h)

theorem id_comp {A B : ExpiryObject} (f : Hom A B) : comp (id A) f = f := by
  cases f
  rfl

theorem comp_id {A B : ExpiryObject} (f : Hom A B) : comp f (id B) = f := by
  cases f
  rfl

theorem comp_assoc {A B C D : ExpiryObject}
    (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f; cases g; cases h
  rfl

end Hom

/-- Live equality-guard expiry: disequality holds at issue time and is erased
by the coalescing `merge void void → void` step. -/
def eqWExpiry : ExpiryObject where
  Carrier := Trace × Trace
  dynamics := PairStep
  license := Distinct
  issue := (merge void void, void)
  consume := (void, void)
  crossing := PairStep.left merge_void_void_steps_void
  issue_licensed := coalescing_is_distinct
  consume_unlicensed := fun h => h rfl

/-- Quote/eval license: “has a next quote/eval step”. The live peak source has
such a step and the value result has none. -/
def QuoteReducible (c : QuoteEvalCfg) : Prop :=
  ∃ d, QuoteEvalStep true c d

def quoteExpiry : ExpiryObject where
  Carrier := QuoteEvalCfg
  dynamics := QuoteEvalStep true
  license := QuoteReducible
  issue := freezePeakSource
  consume := .value void
  crossing := freeze_peak_eval_converge
  issue_licensed := ⟨.value void, freeze_peak_eval_converge⟩
  consume_unlicensed := by
    rintro ⟨d, h⟩
    exact no_step_from_value h

/-- Role-erasure dynamics as a one-step graph of `roleCollapse`. -/
def RoleCollapseStep {Y : Type*} (x y : Occ Y) : Prop := y = roleCollapse x

/-- Live role expiry: activity holds on the active occurrence and fails after
role erasure sends it to the frame occurrence. -/
def roleExpiry : ExpiryObject where
  Carrier := Occ Unit
  dynamics := RoleCollapseStep
  license := isActive
  issue := ((), Role.active)
  consume := ((), Role.frame)
  crossing := rfl
  issue_licensed := rfl
  consume_unlicensed := by intro h; exact Role.noConfusion h

/-- Category laws for expiry objects and expiry morphisms: left identity, right
identity, and associativity of composition.  This is the anchor behind the
sentence that expiry data form a category; the three live objects below supply
its non-vacuity. -/
theorem licenseExpiry_category_laws :
    (∀ {A B : ExpiryObject.{u}} (f : Hom A B), Hom.comp (Hom.id A) f = f) ∧
    (∀ {A B : ExpiryObject.{u}} (f : Hom A B), Hom.comp f (Hom.id B) = f) ∧
    (∀ {A B C D : ExpiryObject.{u}} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h)) :=
  ⟨Hom.id_comp, Hom.comp_id, Hom.comp_assoc⟩

/-- All three live expiry objects are non-vacuous. -/
theorem three_live_expiry_witnesses :
    eqWExpiry.license eqWExpiry.issue ∧ ¬ eqWExpiry.license eqWExpiry.consume ∧
    quoteExpiry.license quoteExpiry.issue ∧ ¬ quoteExpiry.license quoteExpiry.consume ∧
    roleExpiry.license roleExpiry.issue ∧ ¬ roleExpiry.license roleExpiry.consume :=
  ⟨eqWExpiry.issue_licensed, eqWExpiry.consume_unlicensed,
   quoteExpiry.issue_licensed, quoteExpiry.consume_unlicensed,
   roleExpiry.issue_licensed, roleExpiry.consume_unlicensed⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory
