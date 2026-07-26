import OperatorKO7.Meta.HigherOrderNoSharingBoundary

/-!
This module packages two imported sharing barriers with an inhabited scope marker defined as
True. The exported theorem proves the record fields displayed in its type.




-/

namespace OperatorKO7.HigherOrderSharingBoundaryFinalCatalog

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderSharingBoundary
open OperatorKO7.HigherOrderNoSharingBoundary

/-- Abbreviation for the displayed type. -/
abbrev FullHigherOrderRewritingOutsideCatalog : Prop :=
  True

/-- Data record whose requirements are the fields displayed below. -/
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

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem higher_order_sharing_boundary_final_catalog :
    HigherOrderSharingBoundaryCatalog := by
  refine ⟨shared_policy_counter_orients_step, ?_,
    sharing_policy_blocks_unqualified_tree_barrier_lift,
    noSharingBoundaryStatus, trivial⟩
  intro b s n
  exact higher_order_fragment_recovers_sharing_breaks_tree_barrier b s n

/-- The displayed proposition follows from the stated hypotheses. -/
theorem final_catalog_projects_shared_counterexample :
    HOPolicyOrientsStep .shared
    ∧ (∀ b s n : SharedTerm,
      HOPolicyCounter .shared
        (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
      HOPolicyCounter .shared
        (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n)))) := by
  exact ⟨higher_order_sharing_boundary_final_catalog.sharedCounterOrientsStep,
    higher_order_sharing_boundary_final_catalog.sharedCounterexample⟩

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem final_catalog_projects_unqualified_lift_blocker :
    ¬ UnqualifiedHigherOrderLiftClaim :=
  higher_order_sharing_boundary_final_catalog.unqualifiedLiftBlocked

/-- The displayed proposition follows from the stated hypotheses. -/
theorem final_catalog_projects_no_sharing_requirement :
    NoSharingBoundaryStatus :=
  higher_order_sharing_boundary_final_catalog.noSharingBoundary

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem final_catalog_records_full_higher_order_not_claimed :
    FullHigherOrderRewritingOutsideCatalog :=
  higher_order_sharing_boundary_final_catalog.fullHigherOrderNotClaimed

end OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
