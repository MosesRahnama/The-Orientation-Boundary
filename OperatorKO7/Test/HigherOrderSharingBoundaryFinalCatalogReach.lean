import OperatorKO7.Meta.HigherOrderSharingBoundary_FinalCatalog

namespace HigherOrderSharingBoundaryFinalCatalogReach

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderSharingBoundary
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog

#check HigherOrderSharingBoundaryCatalog
#check FullHigherOrderRewritingOutsideCatalog
#check HigherOrderSharingBoundaryCatalog.fullHigherOrderNotClaimed
#check higher_order_sharing_boundary_final_catalog
#check final_catalog_projects_shared_counterexample
#check final_catalog_projects_unqualified_lift_blocker
#check final_catalog_projects_no_sharing_requirement
#check final_catalog_records_full_higher_order_not_claimed

example : HOPolicyOrientsStep .shared := by
  exact final_catalog_projects_shared_counterexample.1

example (b s n : SharedTerm) :
    HOPolicyCounter .shared
      (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
    HOPolicyCounter .shared
      (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n))) := by
  exact final_catalog_projects_shared_counterexample.2 b s n

example : ¬ UnqualifiedHigherOrderLiftClaim := by
  exact final_catalog_projects_unqualified_lift_blocker

example : NoSharingBoundaryStatus := by
  exact final_catalog_projects_no_sharing_requirement

example : ¬ NoSharingPolicy .shared := by
  exact final_catalog_projects_no_sharing_requirement.sharedPolicyRejected

example : NoSharingLiftHypothesis := by
  exact final_catalog_projects_no_sharing_requirement.noSharingRequiredForLift

example (t : SharedTerm) :
    RestrictedHigherOrderFragment (embedSharedTerm t) := by
  exact
    (final_catalog_projects_no_sharing_requirement).restrictedFragmentCarriesFirstOrderShape t

example : FullHigherOrderRewritingOutsideCatalog := by
  exact final_catalog_records_full_higher_order_not_claimed

/-! ## The outside-catalog marker carries the typed negation, not `True` (WP-4) -/

#check @FullHigherOrderRewritingOutsideCatalog
#check @final_catalog_outside_catalog_marker_is_lift_blocker

#print axioms HigherOrderSharingBoundaryCatalog
#print axioms FullHigherOrderRewritingOutsideCatalog
#print axioms HigherOrderSharingBoundaryCatalog.fullHigherOrderNotClaimed
#print axioms higher_order_sharing_boundary_final_catalog
#print axioms final_catalog_projects_shared_counterexample
#print axioms final_catalog_projects_unqualified_lift_blocker
#print axioms final_catalog_projects_no_sharing_requirement
#print axioms final_catalog_records_full_higher_order_not_claimed
#print axioms final_catalog_outside_catalog_marker_is_lift_blocker

/-- Gate: the marker is definitionally the unqualified-lift blocker. -/
example : FullHigherOrderRewritingOutsideCatalog = (¬ UnqualifiedHigherOrderLiftClaim) :=
  final_catalog_outside_catalog_marker_is_lift_blocker

/-- Gate: inhabiting the marker gives back the blocker, so it cannot be discharged by `trivial`. -/
example : ¬ UnqualifiedHigherOrderLiftClaim :=
  final_catalog_records_full_higher_order_not_claimed

end HigherOrderSharingBoundaryFinalCatalogReach
