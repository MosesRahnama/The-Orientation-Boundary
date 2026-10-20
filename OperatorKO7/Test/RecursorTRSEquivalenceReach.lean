import OperatorKO7.Meta.Recursor.TRSEquivalence

/-!
# Reachability and axiom check for `Meta/Recursor/TRSEquivalence.lean`

Every public declaration of the module carries a `#check @` and a `#print axioms` below, and the
examples instantiate the agreement theorem with and without the named constructor-cost measure.
-/

set_option autoImplicit false

namespace RecursorTRSEquivalenceReach

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.Meta.Recursor.TRSEquivalence

#check @OperatorKO7.Meta.Recursor.TRSEquivalence.trsEquivalentLicensedQuotient
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.trsEquivalenceObservableLabel
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.trsEquivalenceLQ
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.TRSEquivalentUnderLicensedQuotient
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.LicensedQuotientLinearGrowthAgreement
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_simulates_circular_reference_under_licensed_quotient
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.circular_reference_simulates_recursor_under_licensed_quotient
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_linearGrowthAgreement_under_licensed_quotient
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_TRS_equivalence_via_LQF_universal_substrate
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.trs_equivalence_implies_mass_indistinguishable
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.trs_equivalence_consistent_with_dp_projection_license
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_trs_equivalence_anchor
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_linearGrowth_agreement_anchor
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.traceSize
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.counterTrace_injective
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.recursorOrbit_injective
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.circularReferenceOrbit_traceSize_succ
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.circularReferenceOrbit_traceSize_lt_add
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.circularReferenceOrbit_injective
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.OrbitStepRel
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.orbitTransport
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.orbitTransport_eval
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.orbitTransport_step
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_circular_orbit_system_isomorphism
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_orbit_isomorphism_anchor
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostMass
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_mu_delta
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_mu_rec
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_mu_merge
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_equations
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostMass_recursorOrbit
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCost_linearGrowthAgreement_under_licensed_quotient
#check @OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCost_information_agreement_under_DP_projection

#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.trsEquivalentLicensedQuotient
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.trsEquivalenceObservableLabel
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.trsEquivalenceLQ
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.TRSEquivalentUnderLicensedQuotient
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.LicensedQuotientLinearGrowthAgreement
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_simulates_circular_reference_under_licensed_quotient
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.circular_reference_simulates_recursor_under_licensed_quotient
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_linearGrowthAgreement_under_licensed_quotient
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_TRS_equivalence_via_LQF_universal_substrate
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.trs_equivalence_implies_mass_indistinguishable
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.trs_equivalence_consistent_with_dp_projection_license
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_trs_equivalence_anchor
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_linearGrowth_agreement_anchor
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.traceSize
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.counterTrace_injective
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.recursorOrbit_injective
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.circularReferenceOrbit_traceSize_succ
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.circularReferenceOrbit_traceSize_lt_add
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.circularReferenceOrbit_injective
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.OrbitStepRel
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.orbitTransport
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.orbitTransport_eval
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.orbitTransport_step
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_circular_orbit_system_isomorphism
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_orbit_isomorphism_anchor
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostMass
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_mu_delta
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_mu_rec
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_mu_merge
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostDirectMeasure_equations
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCostMass_recursorOrbit
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCost_linearGrowthAgreement_under_licensed_quotient
#print axioms OperatorKO7.Meta.Recursor.TRSEquivalence.constructorCost_information_agreement_under_DP_projection

example : LicensedQuotient (Nat → Trace) := trsEquivalenceLQ

example : trsEquivalenceLQ.proj (fun _ => Trace.void) = PUnit.unit := rfl

example
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    TRSEquivalentUnderLicensedQuotient trsEquivalenceLQ D
      (RecursorOrbit b s) (CircularReferenceOrbit A B) :=
  step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
    b s A B D mu_delta mu_rec mu_merge

example
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    MassIndistinguishable
      (fun n => D.mu (RecursorOrbit b s n))
      (fun n => D.mu (CircularReferenceOrbit A B n)) :=
  trs_equivalence_implies_mass_indistinguishable
    b s A B D mu_delta mu_rec mu_merge

example : recursor_trs_equivalence_anchor =
    "OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient" :=
  rfl

/-- The constructor-cost measure inhabits the three equations, so the hypotheses of the agreement
theorem have a witness: the mass profile of the recursor orbit is `n + 1`. -/
example : constructorCostDirectMeasure.mu (RecursorOrbit void void 3) = 4 :=
  constructorCostMass_recursorOrbit void void 3

/-- The constructor-cost measure separates `delta void` from `void`: it is not a constant measure. -/
example : constructorCostDirectMeasure.mu (delta void) ≠ constructorCostDirectMeasure.mu void := by
  decide

example (b s A B : Trace) :
    TRSEquivalentUnderLicensedQuotient trsEquivalenceLQ constructorCostDirectMeasure
      (RecursorOrbit b s) (CircularReferenceOrbit A B) :=
  constructorCost_linearGrowthAgreement_under_licensed_quotient b s A B

end RecursorTRSEquivalenceReach
