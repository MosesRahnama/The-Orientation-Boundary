import OperatorKO7.Meta.HigherOrderNoSharingBoundary

/-!
# Higher-Order Sharing Boundary: Final M2 Catalog

This file packages the current M2 result without overclaiming.
It records the shared-policy counterexample, the explicit blocker against an
unqualified tree-barrier lift, the no-sharing boundary status, and the fact
that full higher-order rewriting remains outside the present catalog.
-/

namespace OperatorKO7.HigherOrderSharingBoundaryFinalCatalog

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderSharingBoundary
open OperatorKO7.HigherOrderNoSharingBoundary

/-- Explicit scope marker for the final M2 catalog. -/
abbrev FullHigherOrderRewritingOutsideCatalog : Prop :=
  True

/-- Final paper-facing M2 catalog for the higher-order sharing boundary. -/
structure HigherOrderSharingBoundaryCatalog : Prop where
  sharedCounterOrientsStep : HOPolicyOrientsStep .shared
  sharedCounterexample :
    ∀ b s n : SharedTerm,
      HOPolicyCounter .shared
        (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
      HOPolicyCounter .shared
        (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n)))
  unqualifiedLiftBlocked : ¬ UnqualifiedHigherOrderLiftClaim
  noSharingBoundary : NoSharingBoundaryStatus
  fullHigherOrderNotClaimed : FullHigherOrderRewritingOutsideCatalog

/-- The final M2 catalog packages the current higher-order sharing boundary
without claiming a full higher-order rewriting impossibility theorem. -/
theorem higher_order_sharing_boundary_final_catalog :
    HigherOrderSharingBoundaryCatalog := by
  refine ⟨shared_policy_counter_orients_step, ?_,
    sharing_policy_blocks_unqualified_tree_barrier_lift,
    noSharingBoundaryStatus, trivial⟩
  intro b s n
  exact higher_order_fragment_recovers_sharing_breaks_tree_barrier b s n

/-- The final catalog projects the shared-policy orienting counterexample. -/
theorem final_catalog_projects_shared_counterexample :
    HOPolicyOrientsStep .shared
    ∧ (∀ b s n : SharedTerm,
      HOPolicyCounter .shared
        (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
      HOPolicyCounter .shared
        (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n)))) := by
  exact ⟨higher_order_sharing_boundary_final_catalog.sharedCounterOrientsStep,
    higher_order_sharing_boundary_final_catalog.sharedCounterexample⟩

/-- The final catalog projects the blocker against an unqualified tree-barrier
lift. -/
theorem final_catalog_projects_unqualified_lift_blocker :
    ¬ UnqualifiedHigherOrderLiftClaim :=
  higher_order_sharing_boundary_final_catalog.unqualifiedLiftBlocked

/-- The final catalog projects the theorem-visible no-sharing boundary status. -/
theorem final_catalog_projects_no_sharing_requirement :
    NoSharingBoundaryStatus :=
  higher_order_sharing_boundary_final_catalog.noSharingBoundary

/-- The final catalog records explicitly that full higher-order rewriting is
outside the current M2 scope. -/
theorem final_catalog_records_full_higher_order_not_claimed :
    FullHigherOrderRewritingOutsideCatalog :=
  higher_order_sharing_boundary_final_catalog.fullHigherOrderNotClaimed

end OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
