import OperatorKO7.Meta.Recursor.InformationEquivalence

/-!
# Reachability and axiom check for `Meta/Recursor/InformationEquivalence.lean`

Every public declaration of the module, with the constructor and the two projections of
`EntropyMeasure`, carries a `#check @` and a `#print axioms` below. The constructor-cost direct
measure that inhabits the three equations, and the instance of the agreement theorem at it, live in
`TRSEquivalence.lean` and its companion check file.
-/

set_option autoImplicit false

open OperatorKO7
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.InformationEquivalence

namespace RecursorInformationEquivalenceReach

#check @OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure.mk
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure.discardedInfo
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure.respects_linear_growth
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.DiscardedInformationOf
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.InformationEquivalentModDP
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.linear_growth_implies_discarded_info_equality
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.mass_indistinguishable_implies_discarded_info_equality
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.step_duplicator_information_equivalent_to_circular_reference_under_DP_projection
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.step_duplicator_information_agreement_under_linearGrowthInvariant
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.mass_indistinguishable_implies_information_equivalent
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.cost_floor_witnessed_information_equivalence
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.canonical_confession_H_equivalence_invariant_under_orbit_choice
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.canonical_discarded_bits_are_orbit_invariant
#check @OperatorKO7.Meta.Recursor.InformationEquivalence.canonical_confession_converges_to_itself

#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure.mk
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure.discardedInfo
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.EntropyMeasure.respects_linear_growth
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.DiscardedInformationOf
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.InformationEquivalentModDP
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.linear_growth_implies_discarded_info_equality
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.mass_indistinguishable_implies_discarded_info_equality
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.step_duplicator_information_equivalent_to_circular_reference_under_DP_projection
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.step_duplicator_information_agreement_under_linearGrowthInvariant
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.mass_indistinguishable_implies_information_equivalent
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.cost_floor_witnessed_information_equivalence
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.canonical_confession_H_equivalence_invariant_under_orbit_choice
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.canonical_discarded_bits_are_orbit_invariant
#print axioms OperatorKO7.Meta.Recursor.InformationEquivalence.canonical_confession_converges_to_itself

/-- A canonical zero entropy measure: every mass profile receives discarded-information value `0`.
It satisfies the cost-floor consistency condition by reflexivity. -/
def zeroEntropy : EntropyMeasure where
  discardedInfo := fun _ => 0
  respects_linear_growth := by
    intro _ _ _ _
    rfl

/-- The constant direct measure with value `1` on every trace. It does not satisfy the successor
equation `mu (delta t) = mu t + 1`; it serves only the reflexivity example below. The measure that
satisfies all three equations is `TRSEquivalence.constructorCostDirectMeasure`. -/
def constantOneDirectMeasure : DirectMeasureProofSystem where
  mu := fun _ => 1

/-- Under `zeroEntropy` both orbits receive value `0` by computation, for any direct measure. -/
example (b s A B : Trace) :
    DiscardedInformationOf zeroEntropy constantOneDirectMeasure (RecursorOrbit b s)
      = DiscardedInformationOf zeroEntropy constantOneDirectMeasure
          (CircularReferenceOrbit A B) := by
  rfl

example (b s A B : Trace) :
    InformationEquivalentModDP
      (RecursorOrbit b s)
      (CircularReferenceOrbit A B) :=
  step_duplicator_information_equivalent_to_circular_reference_under_DP_projection
    b s A B

end RecursorInformationEquivalenceReach
