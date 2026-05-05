import OperatorKO7.Meta.HigherOrderSharingBoundary

/-!
# Higher-Order No-Sharing Boundary

This file makes the tree/no-sharing restriction theorem-visible.
It does not claim a full higher-order no-go theorem. It isolates the exact
policy boundary needed before the existing tree-based story can be lifted.
-/

namespace OperatorKO7.HigherOrderNoSharingBoundary

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderSharingBoundary

/-- Policies that preserve the tree/no-sharing side of the current carrier. -/
inductive NoSharingPolicy : SharingPolicy → Prop
  | tree : NoSharingPolicy .tree

/-- Restricted higher-order fragment still carrying the embedded first-order
recursor shape. -/
abbrev RestrictedHigherOrderFragment : HOTerm → Prop :=
  HOClosedFragment

/-- Exact hypothesis required before a tree-based lift can ignore the shared
counterexample: every policy outside the no-sharing class must be treated as a
separate orientable branch rather than silently absorbed into the tree theorem. -/
abbrev NoSharingLiftHypothesis : Prop :=
  ∀ {policy : SharingPolicy}, ¬ NoSharingPolicy policy → HOPolicyOrientsStep policy

/-- Paper-facing status package for the current no-sharing boundary. -/
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

/-- The no-sharing hypothesis is load-bearing for any tree-style lift on the
current higher-order carrier. Every policy outside the no-sharing class falls
onto the shared-policy orienting branch. -/
theorem no_sharing_hypothesis_is_required_for_tree_lift :
    NoSharingLiftHypothesis := by
  intro policy hNoSharing
  cases policy with
  | tree =>
      exact False.elim (hNoSharing NoSharingPolicy.tree)
  | shared =>
      exact shared_policy_counter_orients_step

/-- The shared-policy branch already refutes any unqualified higher-order no-go
claim that ignores the sharing policy. -/
theorem shared_policy_refutes_unqualified_no_go :
    ¬ UnqualifiedHigherOrderLiftClaim :=
  sharing_policy_blocks_unqualified_tree_barrier_lift

/-- The restricted fragment still contains every embedded first-order shape
used by the current sharing-aware surrogate. -/
theorem restricted_fragment_embeds_first_order_shape :
    ∀ t : SharedTerm, RestrictedHigherOrderFragment (embedSharedTerm t) :=
  embedSharedTerm_closedFragment

/-- The current theorem-visible status of the no-sharing boundary. -/
def noSharingBoundaryStatus : NoSharingBoundaryStatus where
  sharedPolicyRejected := shared_policy_not_no_sharing
  noSharingRequiredForLift := no_sharing_hypothesis_is_required_for_tree_lift
  restrictedFragmentCarriesFirstOrderShape :=
    restricted_fragment_embeds_first_order_shape

end OperatorKO7.HigherOrderNoSharingBoundary
