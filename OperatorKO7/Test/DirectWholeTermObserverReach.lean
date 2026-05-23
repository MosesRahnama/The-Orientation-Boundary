import OperatorKO7.Meta.DirectWholeTermObserver

/-!
# Reach test: DirectWholeTermObserver (Phase B)

Confirms that every public name added in
`Meta/DirectWholeTermObserver.lean` is reachable and type-checks. The reach
test imports nothing beyond the module under test and supplies one inline
concrete family witness so the `payloadCountObserver` and the additive
corollary specialize on a concrete carrier without depending on later
phase modules.
-/

namespace OperatorKO7.StepDuplicating

#check @DirectWholeTermObserver
#check @DirectWholeTermObserver.mk
#check @DirectWholeTermObserver.Carrier
#check @DirectWholeTermObserver.eval
#check @DirectWholeTermObserver.lt
#check @DirectWholeTermObserver.visiblePayloadCoordinate
#check @DirectWholeTermObserver.carrierSensitive
#check @DirectWholeTermObserver.constructorLocal
#check @DirectWholeTermObserver.pumpMonotone
#check @DirectWholeTermObserver.orient_forces_payload_drop

#check @DuplicatingRecursiveFamily.GloballyOrients

#check @no_direct_orientation_of_payload_exposure
#check @payloadCountObserver
#check @no_additive_orients_dup_step_via_DWO

/-! ## Concrete reach example

A trivial single-payload single-position family witnesses every public name.
The witness reuses the canonical RDRS payload-count discipline; `Step` is
deliberately taken to be `fun a b => a = false ∧ b = true` so the rule's
left-hand side steps to the right-hand side and no other steps fire.
-/

private def reachSchema : RightDuplicatingRecursorSchema where
  Term := Bool
  PayloadCoord := Unit
  Position := Unit
  lhs := false
  rhs := true
  payloadOccursAt := fun _ _ _ => True
  payloadCount := fun _ t => if t then 2 else 1
  distinguishedPayload := ()
  lhs_has_payload := rfl
  rhs_duplicates_payload := by decide
  firesOnClosedTerms := True

private def reachFamily : DuplicatingRecursiveFamily where
  schema := reachSchema
  Step := fun a b => a = false ∧ b = true
  duplicating_step := And.intro rfl rfl
  HasUnboundedPayloadPump := fun _ => True
  ExposesPayloadStrictly := fun _ => True
  distinguished_exposed := True.intro
  exposure_strict_count := by
    intro _ _
    -- `reachSchema.payloadCount _ false = 1` and `reachSchema.payloadCount _ true = 2`
    -- by definition of `if t then 2 else 1`; `lhs = false`, `rhs = true`.
    show (1 : Nat) < 2
    decide

example : ¬ reachFamily.GloballyOrients (payloadCountObserver reachFamily) :=
  no_additive_orients_dup_step_via_DWO reachFamily True.intro

/-- Alternative spelling exercising the main theorem directly on the same
reach family with explicit named hypotheses (no theorem-local bridge). -/
example : ¬ reachFamily.GloballyOrients (payloadCountObserver reachFamily) :=
  no_direct_orientation_of_payload_exposure
    (payloadCountObserver reachFamily)
    (i := reachFamily.distinguishedPayload)
    True.intro
    reachFamily.distinguished_exposed
    rfl
    rfl

end OperatorKO7.StepDuplicating
