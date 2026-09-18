import OperatorKO7.Meta.Recursor.TRSEquivalence

/-!
# Reach test for `Meta/Recursor/TRSEquivalence.lean`

Asserts the headline theorem and its companion lemmas resolve under
`lake env lean`. Per `.agent-control/COMPLETION_PROTOCOL.md` the reach
test serves as the live-demo gate for theorem-side lanes.
-/

namespace RecursorTRSEquivalenceReach

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.Meta.Recursor.TRSEquivalence

#check @trsEquivalentLicensedQuotient
#check trsEquivalenceObservableLabel
#check trsEquivalenceLQ
#check @TRSEquivalentUnderLicensedQuotient
#check @recursor_simulates_circular_reference_under_licensed_quotient
#check @circular_reference_simulates_recursor_under_licensed_quotient
#check @step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
#check @step_duplicator_TRS_equivalence_via_LQF_universal_substrate
#check @trs_equivalence_implies_mass_indistinguishable
#check @trs_equivalence_consistent_with_dp_projection_license
#check recursor_trs_equivalence_anchor

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

end RecursorTRSEquivalenceReach
