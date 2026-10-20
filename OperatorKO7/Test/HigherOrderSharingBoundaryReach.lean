import OperatorKO7.Meta.HigherOrderSharingBoundary

namespace HigherOrderSharingBoundaryReach

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderSharingBoundary

#check SharingPolicy.tree
#check SharingPolicy.shared
#check HOTerm
#check HOClosedFragment
#check HODupStep
#check HOPolicyCounter
#check HOPolicyOrientsStep
#check UnqualifiedHigherOrderLiftClaim
#check embedSharedTerm
#check embedSharedTerm_closedFragment
#check shared_recursor_shape_closed_fragment
#check shared_step_embeds
#check shared_policy_counter_orients_embedded_step
#check shared_policy_counter_orients_step
#check higher_order_fragment_recovers_sharing_breaks_tree_barrier
#check unqualified_higher_order_lift_contradiction
#check sharing_policy_blocks_unqualified_tree_barrier_lift

example {a b : SharedTerm} (h : SharedStep a b) :
    HOPolicyCounter .shared (embedSharedTerm b) <
      HOPolicyCounter .shared (embedSharedTerm a) := by
  exact shared_policy_counter_orients_embedded_step h

example (b s n : SharedTerm) :
    HOClosedFragment (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n))) := by
  exact shared_recursor_shape_closed_fragment b s n

example (h : UnqualifiedHigherOrderLiftClaim) : False := by
  exact unqualified_higher_order_lift_contradiction h

example (b s n : SharedTerm) :
    HOPolicyCounter .shared
      (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
    HOPolicyCounter .shared
      (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n))) := by
  exact higher_order_fragment_recovers_sharing_breaks_tree_barrier b s n

end HigherOrderSharingBoundaryReach
