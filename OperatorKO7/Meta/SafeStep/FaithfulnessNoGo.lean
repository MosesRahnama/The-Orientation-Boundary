import OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor

set_option autoImplicit false

/-!
# The faithfulness no-go for dynamical boundary functors

`DynamicalBoundaryFunctor` exhibits collapse-preserving dynamical functors from the
full kernel `Step` and the guarded `SafeStep` into the distinction and orientation
boundaries, and proves one such functor non-faithful. This module turns that single
non-faithfulness fact into a general impossibility theorem and closes the last open
question of the duality program.

The bridge is the boundary-operator `payloadDiscarding` law. A dynamical functor is
*payload-faithful* when the boundary verdict recovers the discarded payload over the
functor's object image. The no-go theorem shows that a functor whose object map
covers the boundary domain can never be payload-faithful, because a recovery over the
image extends to a recovery over the whole domain, which is exactly what
`payloadDiscarding` forbids. Since `payloadDiscarding` is a defining field of every
`BoundaryOperator`, no payload-discarding boundary admits a faithful dynamical functor
with covering object map. The distinction and orientation collapse functors are
concrete instances.

It contains no `sorry`, no new `axiom`, no `native_decide`, and no `@[csimp]`; the
public theorems are spot-checked with `#print axioms` (baseline whitelist
`{propext, Classical.choice, Quot.sound}`).
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.Meta.SafeStep.BoundaryDuality
open OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor

namespace OperatorKO7.Meta.SafeStep.FaithfulnessNoGo

/-- A dynamical boundary functor is *payload-faithful* when the boundary verdict
recovers the discarded payload over the functor's object image. -/
def PayloadFaithful {R : Trace → Trace → Prop}
    {B : BoundaryOperator (Option Trace) Trace}
    (F : RewriteBoundaryFunctor R B) : Prop :=
  ∃ recover : Trace → B.Payload,
    ∀ t : Trace,
      recover (B.apply (F.mapObj t) (F.mapObj_domain t)) = B.payload_extract (F.mapObj t)

/-- THE FAITHFULNESS NO-GO (general). A dynamical boundary functor whose object map
covers the boundary domain is never payload-faithful: a verdict-to-payload recovery
over the image would extend to a recovery over the whole domain, contradicting the
boundary-operator `payloadDiscarding` law. Since `payloadDiscarding` holds for every
`BoundaryOperator`, no payload-discarding boundary admits a covering payload-faithful
dynamical functor. -/
theorem not_payloadFaithful_of_covers
    {R : Trace → Trace → Prop}
    {B : BoundaryOperator (Option Trace) Trace}
    (F : RewriteBoundaryFunctor R B)
    (hcov : ∀ xh : {x : Option Trace // B.domain x}, ∃ t : Trace, F.mapObj t = xh.1) :
    ¬ PayloadFaithful F := by
  rintro ⟨recover, hrec⟩
  apply B.payloadDiscarding
  refine ⟨recover, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨t, ht⟩ := hcov ⟨x, hx⟩
  subst ht
  exact hrec t

/-- The full-kernel distinction dynamical functor is not payload-faithful: the eqW
collapse to `void` cannot be inverted to its source payload. -/
theorem distinction_no_faithful_dynamical_functor :
    ¬ PayloadFaithful step_distinction_dynamical_boundary_functor := by
  apply not_payloadFaithful_of_covers
  rintro ⟨x, hx⟩
  cases x with
  | none => exact absurd rfl hx
  | some t => exact ⟨t, rfl⟩

/-- The full-kernel orientation dynamical functor is not payload-faithful: the
carrier collapse cannot be inverted to its source payload. -/
theorem orientation_no_faithful_dynamical_functor :
    ¬ PayloadFaithful step_orientation_dynamical_boundary_functor := by
  apply not_payloadFaithful_of_covers
  rintro ⟨x, hx⟩
  cases x with
  | none => exact absurd rfl hx
  | some t => exact ⟨t, rfl⟩

/-- The guarded distinction dynamical functor is not payload-faithful either, so the
obstruction is not an artifact of the unguarded relation. -/
theorem safeStep_distinction_no_faithful_dynamical_functor :
    ¬ PayloadFaithful safeStep_distinction_dynamical_boundary_functor := by
  apply not_payloadFaithful_of_covers
  rintro ⟨x, hx⟩
  cases x with
  | none => exact absurd rfl hx
  | some t => exact ⟨t, rfl⟩

/-- A boundary functor is verdict-constant when all source objects have the same
boundary verdict. This is the exact finite functor-strengthening supported by
the compiled collapse functors. -/
def BoundaryVerdictConstant {R : Trace → Trace → Prop}
    {B : BoundaryOperator (Option Trace) Trace}
    (F : RewriteBoundaryFunctor R B) : Prop :=
  ∀ a b : Trace,
    B.apply (F.mapObj a) (F.mapObj_domain a)
      = B.apply (F.mapObj b) (F.mapObj_domain b)

/-- The full-kernel distinction collapse functor is the constant functor on the
boundary verdict. -/
theorem step_distinction_boundary_functor_constant :
    BoundaryVerdictConstant step_distinction_dynamical_boundary_functor := by
  intro a b
  rfl

/-- The guarded distinction collapse functor is also verdict-constant. -/
theorem safeStep_distinction_boundary_functor_constant :
    BoundaryVerdictConstant safeStep_distinction_dynamical_boundary_functor := by
  intro a b
  rfl

/-- Constant-verdict collapse plus the no-faithfulness theorem, packaged for the
distinction boundary. -/
theorem payloadDiscarding_constant_functor_surface :
    BoundaryVerdictConstant step_distinction_dynamical_boundary_functor
      ∧ ¬ PayloadFaithful step_distinction_dynamical_boundary_functor :=
  ⟨step_distinction_boundary_functor_constant,
    distinction_no_faithful_dynamical_functor⟩

#print axioms not_payloadFaithful_of_covers
#print axioms distinction_no_faithful_dynamical_functor
#print axioms orientation_no_faithful_dynamical_functor
#print axioms safeStep_distinction_no_faithful_dynamical_functor
#print axioms step_distinction_boundary_functor_constant
#print axioms safeStep_distinction_boundary_functor_constant
#print axioms payloadDiscarding_constant_functor_surface

end OperatorKO7.Meta.SafeStep.FaithfulnessNoGo
