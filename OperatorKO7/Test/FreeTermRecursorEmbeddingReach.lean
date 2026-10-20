import OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding

/-! # FreeTermRecursorEmbedding reach and axiom check -/

set_option autoImplicit false

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm_injective
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm_injective
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.deltaPrefix_toRecursorTerm
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.deltaPrefix_toRecursorTerm
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.counterObservation_toRecursorTerm
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.counterObservation_toRecursorTerm
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.payloadObservation_toRecursorTerm
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.payloadObservation_toRecursorTerm
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.profileMeasure_toRecursorTerm
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.profileMeasure_toRecursorTerm
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm_successor_instance
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm_successor_instance
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm_rootStep
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.toRecursorTerm_rootStep
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRecursorStep_from_image
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRecursorStep_from_image
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.rootStep_iff_freeRecursorStep
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.rootStep_iff_freeRecursorStep
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.successor_orientation_iff_across_term_types
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.successor_orientation_iff_across_term_types
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_recurZero
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_recurZero
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_recurSucc
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_recurSucc
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_step
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_step
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_decreases
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_decreases
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_eq_zero_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_eq_zero_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_pointwise_least
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_pointwise_least
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_not_profile_factored
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_not_profile_factored
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.derivationHeight_toRecursorTerm
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.derivationHeight_toRecursorTerm
#check @OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_le_importedRanking
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding.freeRootHeight_le_importedRanking

/-! ## Non-vacuity controls -/

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding

/-- A successor instance maps to a successor instance on a concrete closed term. -/
example : FreeRecursorStep
    (toRecursorTerm (.recur .zero (.succ .zero) (.succ (.succ .zero))))
    (toRecursorTerm (.wrap (.succ .zero) (.recur .zero (.succ .zero) (.succ .zero)))) :=
  toRecursorTerm_rootStep (RootStep.recurSucc _ _ _)

/-- Two distinct closed terms have distinct images. -/
example : toRecursorTerm (.succ .zero) ≠ toRecursorTerm (.wrap .zero .zero) := by
  intro h
  exact absurd (toRecursorTerm_injective h) (by simp)

/-- The root height at a term with a variable, at the carrier `Nat`: the zero rule
fires twice and the successor rule once. -/
example : freeRootHeight (ν := Nat)
    (.recur (.recur (.recur (.var 0) (.var 1) (.succ (.var 2))) (.var 3) .zero) (.var 4) .zero)
      = 3 := rfl

/-- The root height is itself a ranking, so the leastness hypothesis is inhabited at
every carrier, here `Nat`. -/
example : ∀ t : FreeTerm Nat, freeRootHeight t ≤ freeRootHeight t :=
  freeRootHeight_pointwise_least freeRootHeight freeRootHeight_decreases

/-- The root height and `derivationHeight` agree on a concrete closed term. -/
example : OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder.derivationHeight
    (toRecursorTerm (.recur (.recur .zero .zero (.succ .zero)) .zero .zero)) = 2 :=
  (derivationHeight_toRecursorTerm _).trans rfl
