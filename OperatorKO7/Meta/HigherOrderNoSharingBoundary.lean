import OperatorKO7.Meta.HigherOrderSharingBoundary

/-!
# Two-policy sharing classification

`NoSharingPolicy` contains only `.tree`. Because `SharingPolicy` has the two constructors `.tree` and
`.shared`, every policy outside `NoSharingPolicy` is `.shared`; the imported
`shared_policy_counter_orients_step` then proves `NoSharingLiftHypothesis`. This is a finite policy
classification, not a necessity or minimality theorem for unrestricted higher-order rewriting.
-/

namespace OperatorKO7.HigherOrderNoSharingBoundary

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderSharingBoundary

/-- The singleton policy class containing `.tree`. -/
inductive NoSharingPolicy : SharingPolicy → Prop
  | tree : NoSharingPolicy .tree

/-- Restricted higher-order fragment still carrying the embedded first-order
recursor shape. -/
abbrev RestrictedHigherOrderFragment : HOTerm → Prop :=
  HOClosedFragment

/-- Every policy outside the singleton tree class orients the imported step relation. -/
abbrev NoSharingLiftHypothesis : Prop :=
  ∀ {policy : SharingPolicy}, ¬ NoSharingPolicy policy → HOPolicyOrientsStep policy

/-- Package of the three displayed two-policy facts. -/
structure NoSharingBoundaryStatus : Prop where
  sharedPolicyRejected : ¬ NoSharingPolicy .shared
  noSharingRequiredForLift : NoSharingLiftHypothesis
  restrictedFragmentCarriesFirstOrderShape :
    ∀ t : SharedTerm, RestrictedHigherOrderFragment (embedSharedTerm t)

/-- The shared-policy branch is not a no-sharing policy. -/
theorem shared_policy_not_no_sharing :
    ¬ NoSharingPolicy .shared := by
  intro h
  cases h

/-- The two-constructor policy enumeration satisfies `NoSharingLiftHypothesis`. -/
theorem no_sharing_hypothesis_is_required_for_tree_lift :
    NoSharingLiftHypothesis := by
  intro policy hNoSharing
  cases policy with
  | tree =>
      exact False.elim (hNoSharing NoSharingPolicy.tree)
  | shared =>
      exact shared_policy_counter_orients_step

/-- Imported negation of `UnqualifiedHigherOrderLiftClaim` for the shared-policy branch. -/
theorem shared_policy_refutes_unqualified_no_go :
    ¬ UnqualifiedHigherOrderLiftClaim :=
  sharing_policy_blocks_unqualified_tree_barrier_lift

/-- Every embedded `SharedTerm` satisfies the imported closed-fragment predicate. -/
theorem restricted_fragment_embeds_first_order_shape :
    ∀ t : SharedTerm, RestrictedHigherOrderFragment (embedSharedTerm t) :=
  embedSharedTerm_closedFragment

/-- Assemble the three proved fields of `NoSharingBoundaryStatus`. -/
def noSharingBoundaryStatus : NoSharingBoundaryStatus where
  sharedPolicyRejected := shared_policy_not_no_sharing
  noSharingRequiredForLift := no_sharing_hypothesis_is_required_for_tree_lift
  restrictedFragmentCarriesFirstOrderShape :=
    restricted_fragment_embeds_first_order_shape

end OperatorKO7.HigherOrderNoSharingBoundary
