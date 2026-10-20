import OperatorKO7.Meta.Methods.OrientationClosure.AttainedPairs

/-!
# AttainedPairs reach and axiom check

Paired declaration reach and axiom checks for `AttainedPairs.lean`, with
non-vacuity controls at a carrier other than `Empty`.
-/

set_option autoImplicit false

#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterTerm
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterTerm
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadTerm
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadTerm
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix_counterTerm
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix_counterTerm
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation_payloadTerm
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation_payloadTerm
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation_payloadTerm
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation_payloadTerm
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.successor_profile
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.successor_profile
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.closedEmbed
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.closedEmbed
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.closedEmbed_injective
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.closedEmbed_injective
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix_closedEmbed
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix_closedEmbed
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation_closedEmbed
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation_closedEmbed
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation_closedEmbed
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation_closedEmbed
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure_closedEmbed
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure_closedEmbed
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.rootStep_closedEmbed
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.rootStep_closedEmbed
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.every_successor_profile_attained
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.every_successor_profile_attained
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.successor_orientation_restricts_to_closed
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.successor_orientation_restricts_to_closed
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.profile_orients_successors_iff
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.profile_orients_successors_iff
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.successor_orientation_carrier_independent
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.successor_orientation_carrier_independent
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.counter_profile_orients_successors
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.counter_profile_orients_successors
#check @OperatorKO7.Methods.OrientationClosure.AttainedPairs.free_successor_orientation_implies_payloadBlind
#print axioms OperatorKO7.Methods.OrientationClosure.AttainedPairs.free_successor_orientation_implies_payloadBlind

/-! ## Non-vacuity controls at the carrier `Bool` -/

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.AttainedPairs

/-- The attainment theorem at the carrier `Bool` for the profile `(c, p, L) = (2, 3, 4)`. -/
example : ∃ a b : FreeTerm Bool, RootStep a b ∧ counterObservation a = 3 ∧
    payloadObservation a = 3 ∧ counterObservation b = 2 ∧ payloadObservation b = 7 :=
  every_successor_profile_attained (ν := Bool) 2 3 4 (by decide)

/-- The orientation equivalence at the carrier `Bool`, applied to the counter projection. -/
example : ∀ b s n : FreeTerm Bool,
    profileMeasure (fun c _ => c) (.wrap s (.recur b s n)) <
      profileMeasure (fun c _ => c) (.recur b s (.succ n)) :=
  (profile_orients_successors_iff (ν := Bool) (fun c _ => c)).2
    (fun c _ _ _ => Nat.lt_succ_self c)

/-- The inclusion keeps the observations of a term carrying a variable-free payload. -/
example : counterObservation (closedEmbed (ν := Bool) (.recur (counterTerm 1) (payloadTerm 2)
    (.succ (counterTerm 3)))) = 4 :=
  (counterObservation_closedEmbed _).trans rfl
