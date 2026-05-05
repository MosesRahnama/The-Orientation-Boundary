import OperatorKO7.Meta.HigherOrderRewriting_PolicyAudit
import OperatorKO7.Meta.HigherOrderRewriting_Closeout

/-!
# Higher-Order Rewriting Final Catalog

This file packages the explicit M2 higher-order rewriting layer without overclaiming.
It records the transported no-sharing boundary, the shared-surrogate and explicit-sharing
counterexamples, the exact policy-subfamily split, and the blocker against an unqualified
full lift.
-/

namespace OperatorKO7.HigherOrderRewritingFinalCatalog

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifications
open OperatorKO7.HigherOrderRewritingCaptureDecidable
open OperatorKO7.HigherOrderRewritingPolicyAudit

/-- Final paper-facing M2 catalog for the explicit higher-order rewriting layer. -/
structure HigherOrderRewritingCatalog : Prop where
  restrictedFragmentTransport :
    ∀ t : SharedTerm,
      ClosedFragment
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm t))
  noSharingBoundaryTransport : NoSharingBoundaryStatus
  sharedPolicyOrientsStep : PolicyOrientsStep sharedPolicy
  explicitSharingPolicyOrientsStep : PolicyOrientsStep explicitSharingPolicy
  sharedCounterexample :
    ∀ b s n : SharedTerm,
      PolicyCounter sharedPolicy
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.shareApp s (SharedTerm.recur b s n)))) <
      PolicyCounter sharedPolicy
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.recur b s (SharedTerm.succ n))))
  explicitSharingCounterexample :
    ∀ b s n : SharedTerm,
      PolicyCounter explicitSharingPolicy
        (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
      PolicyCounter explicitSharingPolicy
        (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n)))
  treeBinderFreeSubstitutionClosed :
    ∀ {name : Nat} {replacement t : HOTerm},
      ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t)
  sharedBinderFreeSubstitutionClosed :
    ∀ {name : Nat} {replacement t : HOTerm},
      ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t)
  explicitSharingBinderFreeSubstitutionClosed :
    ∀ {name : Nat} {replacement t : HOTerm},
      ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t)
  treeBinderFreeContextClosed :
    ∀ {c : Context}, BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.connector c t)
  sharedBinderFreeContextClosed :
    ∀ {c : Context}, BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.connector c t)
  explicitSharingBinderFreeContextClosed :
    ∀ {c : Context}, BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.connector c t)
  betaStepTransport :
    ∀ {a b : HOTerm}, BetaStep a b → RewriteStep betaCompatiblePolicy a b
  betaContextualClosure :
    ∀ {a b : HOTerm}, BetaStep a b → ∀ context : Context,
      ContextualBetaStep (Context.connector context a) (Context.connector context b)
  binderAwareFreshnessObligation :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      BinderAwareSubstitutionObligation name binderName arg body →
        FreshFor binderName arg
  betaCompatibleCounterexample :
    ∃ a b : HOTerm,
      BetaStep a b ∧
        ¬ PolicyCounter betaCompatiblePolicy b < PolicyCounter betaCompatiblePolicy a
  betaCompatibleNotOriented :
    ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy
  policyBranchSplit : PolicyBranchSplitStatus
  policySubfamilies : PolicySubfamilyStatus
  captureSubfamilyCatalog : HigherOrderCaptureSubfamilyCatalog
  decidableClassificationCatalog : HigherOrderDecidableClassificationCatalog
  captureDecidableCatalog : HigherOrderCaptureDecidableCatalog
  policyAuditCatalog : HigherOrderPolicyAuditCatalog
  unqualifiedLiftBlocked : ¬ UnqualifiedHigherOrderRewritingLiftClaim

/-- Canonical final M2 catalog for the explicit higher-order rewriting layer. -/
theorem higher_order_rewriting_final_catalog :
    HigherOrderRewritingCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact catalog_transports_restricted_fragment higher_order_sharing_boundary_final_catalog
  · exact catalog_transports_no_sharing_boundary higher_order_sharing_boundary_final_catalog
  · exact shared_policy_counter_orients_step
  · exact explicit_sharing_counter_orients_step
  · intro b s n
    exact catalog_transports_shared_counterexample higher_order_sharing_boundary_final_catalog b s n
  · intro b s n
    exact explicit_sharing_fragment_recovers_counterexample b s n
  · intro name replacement t ht
    exact tree_policy_binder_free_substitution_closed name replacement ht
  · intro name replacement t ht
    exact shared_policy_binder_free_substitution_closed name replacement ht
  · intro name replacement t ht
    exact explicit_sharing_policy_binder_free_substitution_closed name replacement ht
  · intro c hc t ht
    exact tree_policy_binder_free_context_closed hc ht
  · intro c hc t ht
    exact shared_policy_binder_free_context_closed hc ht
  · intro c hc t ht
    exact explicit_sharing_policy_binder_free_context_closed hc ht
  · intro a b h
    exact beta_step_rewriteStep h
  · intro a b h context
    exact beta_step_contextual_closure h context
  · intro name binderName arg body h
    exact binderAwareSubstitutionObligation_requires_freshness h
  · exact beta_compatible_policy_counterexample
  · exact beta_compatible_policy_does_not_orient_beta_steps
  · exact policy_branch_split_status
  · exact policySubfamilyStatus
  · exact capture_subfamily_catalog
  · exact higher_order_decidable_classification_catalog
  · exact higher_order_capture_decidable_catalog
  · exact higher_order_policy_audit_catalog
  · exact shared_policy_blocks_unqualified_higher_order_rewriting_lift

/-- The final catalog projects the transported restricted-fragment theorem. -/
theorem final_catalog_projects_restricted_fragment_transport :
    ∀ t : SharedTerm,
      ClosedFragment
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm t)) :=
  higher_order_rewriting_final_catalog.restrictedFragmentTransport

/-- The final catalog projects the transported theorem-visible no-sharing boundary. -/
theorem final_catalog_projects_no_sharing_boundary_transport :
    NoSharingBoundaryStatus :=
  higher_order_rewriting_final_catalog.noSharingBoundaryTransport

/-- The final catalog projects the shared-surrogate orienting counter. -/
theorem final_catalog_projects_shared_policy_orients_step :
    PolicyOrientsStep sharedPolicy :=
  higher_order_rewriting_final_catalog.sharedPolicyOrientsStep

/-- The final catalog projects the explicit-sharing orienting counter. -/
theorem final_catalog_projects_explicit_sharing_policy_orients_step :
    PolicyOrientsStep explicitSharingPolicy :=
  higher_order_rewriting_final_catalog.explicitSharingPolicyOrientsStep

/-- The final catalog projects the transported shared-surrogate counterexample. -/
theorem final_catalog_projects_shared_counterexample :
    ∀ b s n : SharedTerm,
      PolicyCounter sharedPolicy
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.shareApp s (SharedTerm.recur b s n)))) <
      PolicyCounter sharedPolicy
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.recur b s (SharedTerm.succ n)))) :=
  higher_order_rewriting_final_catalog.sharedCounterexample

/-- The final catalog projects the explicit-sharing counterexample. -/
theorem final_catalog_projects_explicit_sharing_counterexample :
    ∀ b s n : SharedTerm,
      PolicyCounter explicitSharingPolicy
        (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
      PolicyCounter explicitSharingPolicy
        (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n))) :=
  higher_order_rewriting_final_catalog.explicitSharingCounterexample

/-- The final catalog projects tree-policy binder-free substitution closure. -/
theorem final_catalog_projects_tree_binder_free_substitution_closed
    {name : Nat} {replacement t : HOTerm} :
    ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t) :=
  higher_order_rewriting_final_catalog.treeBinderFreeSubstitutionClosed

/-- The final catalog projects shared-policy binder-free substitution closure. -/
theorem final_catalog_projects_shared_binder_free_substitution_closed
    {name : Nat} {replacement t : HOTerm} :
    ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t) :=
  higher_order_rewriting_final_catalog.sharedBinderFreeSubstitutionClosed

/-- The final catalog projects explicit-sharing binder-free substitution closure. -/
theorem final_catalog_projects_explicit_sharing_binder_free_substitution_closed
    {name : Nat} {replacement t : HOTerm} :
    ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t) :=
  higher_order_rewriting_final_catalog.explicitSharingBinderFreeSubstitutionClosed

/-- The final catalog projects tree-policy binder-free context closure. -/
theorem final_catalog_projects_tree_binder_free_context_closed
    {c : Context} : BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.connector c t) :=
  higher_order_rewriting_final_catalog.treeBinderFreeContextClosed

/-- The final catalog projects shared-policy binder-free context closure. -/
theorem final_catalog_projects_shared_binder_free_context_closed
    {c : Context} : BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.connector c t) :=
  higher_order_rewriting_final_catalog.sharedBinderFreeContextClosed

/-- The final catalog projects explicit-sharing binder-free context closure. -/
theorem final_catalog_projects_explicit_sharing_binder_free_context_closed
    {c : Context} : BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.connector c t) :=
  higher_order_rewriting_final_catalog.explicitSharingBinderFreeContextClosed

/-- The final catalog projects beta-step transport into the beta-compatible rewrite branch. -/
theorem final_catalog_projects_beta_step_transport
    {a b : HOTerm} :
    BetaStep a b → RewriteStep betaCompatiblePolicy a b :=
  higher_order_rewriting_final_catalog.betaStepTransport

/-- The final catalog projects contextual beta-step closure. -/
theorem final_catalog_projects_beta_contextual_closure
    {a b : HOTerm} :
    BetaStep a b → ∀ context : Context,
      ContextualBetaStep (Context.connector context a) (Context.connector context b) :=
  higher_order_rewriting_final_catalog.betaContextualClosure

/-- The final catalog projects the named binder-aware freshness obligation. -/
theorem final_catalog_projects_binder_aware_freshness_obligation
    {name binderName : Nat} {arg body : HOTerm} :
    BinderAwareSubstitutionObligation name binderName arg body →
      FreshFor binderName arg :=
  higher_order_rewriting_final_catalog.binderAwareFreshnessObligation

/-- The final catalog projects the concrete beta counterexample. -/
theorem final_catalog_projects_beta_compatible_counterexample :
    ∃ a b : HOTerm,
      BetaStep a b ∧
        ¬ PolicyCounter betaCompatiblePolicy b < PolicyCounter betaCompatiblePolicy a :=
  higher_order_rewriting_final_catalog.betaCompatibleCounterexample

/-- The final catalog projects the blocker showing that the current policy counter does not
orient every beta step for the beta-compatible policy. -/
theorem final_catalog_projects_beta_compatible_not_oriented :
    ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy :=
  higher_order_rewriting_final_catalog.betaCompatibleNotOriented

/-- The final catalog projects the clean branch split for the current policy classes. -/
theorem final_catalog_projects_policy_branch_split :
    PolicyBranchSplitStatus :=
  higher_order_rewriting_final_catalog.policyBranchSplit

/-- The final catalog projects the exact policy-subfamily status split. -/
theorem final_catalog_projects_policy_subfamilies :
    PolicySubfamilyStatus :=
  higher_order_rewriting_final_catalog.policySubfamilies

/-- The final catalog projects the capture/subfamily catalog. -/
theorem final_catalog_projects_capture_subfamily_catalog :
    HigherOrderCaptureSubfamilyCatalog :=
  higher_order_rewriting_final_catalog.captureSubfamilyCatalog

/-- The final catalog projects the executable classification catalog. -/
theorem final_catalog_projects_decidable_classification_catalog :
    HigherOrderDecidableClassificationCatalog :=
  higher_order_rewriting_final_catalog.decidableClassificationCatalog

/-- The final catalog projects the executable capture-decision catalog. -/
theorem final_catalog_projects_capture_decidable_catalog :
    HigherOrderCaptureDecidableCatalog :=
  higher_order_rewriting_final_catalog.captureDecidableCatalog

/-- The final catalog projects the finite policy audit catalog. -/
theorem final_catalog_projects_policy_audit_catalog :
    HigherOrderPolicyAuditCatalog :=
  higher_order_rewriting_final_catalog.policyAuditCatalog

/-- The final catalog projects the typed full-capture boundary catalog. -/
theorem final_catalog_projects_full_capture_boundary_catalog :
    OperatorKO7.HigherOrderRewritingFullCaptureBoundary.HigherOrderFullCaptureBoundaryCatalog :=
  OperatorKO7.HigherOrderRewritingFullCaptureBoundary.higher_order_full_capture_boundary_catalog

/-- The final catalog projects the finite M2 closeout catalog. -/
theorem final_catalog_projects_closeout_catalog :
    OperatorKO7.HigherOrderRewritingCloseout.HigherOrderRewritingCloseoutCatalog :=
  OperatorKO7.HigherOrderRewritingCloseout.higher_order_rewriting_closeout_catalog

/-- The final catalog projects the `isLam` classification iff theorem. -/
theorem final_catalog_projects_isLam_classification_eq_true_iff
    {t : HOTerm} :
    isLam t = true ↔ IsLam t :=
  final_catalog_projects_decidable_classification_catalog.isLamClassificationIff

/-- The final catalog projects the binder-free classification iff theorem. -/
theorem final_catalog_projects_binderFree_classification_eq_true_iff
    {t : HOTerm} :
    binderFree? t = true ↔ BinderFreeHOTerm t :=
  final_catalog_projects_decidable_classification_catalog.binderFreeClassificationIff

/-- The final catalog projects the share-free classification iff theorem. -/
theorem final_catalog_projects_shareFree_classification_eq_true_iff
    {t : HOTerm} :
    shareFree? t = true ↔ ShareFreeHOTerm t :=
  final_catalog_projects_decidable_classification_catalog.shareFreeClassificationIff

/-- The final catalog projects the beta-free classification iff theorem. -/
theorem final_catalog_projects_betaFree_classification_eq_true_iff
    {t : HOTerm} :
    betaFree? t = true ↔ BetaFreeHOTerm t :=
  final_catalog_projects_decidable_classification_catalog.betaFreeClassificationIff

/-- The final catalog projects the linear classification iff theorem. -/
theorem final_catalog_projects_linear_classification_eq_true_iff
    {t : HOTerm} :
    linear? t = true ↔ LinearHOTerm t :=
  final_catalog_projects_decidable_classification_catalog.linearClassificationIff

/-- The final catalog projects the DAG/shared classification iff theorem. -/
theorem final_catalog_projects_dagShared_classification_eq_true_iff
    {t : HOTerm} :
    dagShared? t = true ↔ DAGSharedHOTerm t :=
  final_catalog_projects_decidable_classification_catalog.dagSharedClassificationIff

/-- The final catalog projects the binder-free context classification iff theorem. -/
theorem final_catalog_projects_binderFreeContext_classification_eq_true_iff
    {c : Context} :
    binderFreeContext? c = true ↔ BinderFreeContext c :=
  final_catalog_projects_decidable_classification_catalog.binderFreeContextClassificationIff

/-- The final catalog projects the beta-free context classification iff theorem. -/
theorem final_catalog_projects_betaFreeContext_classification_eq_true_iff
    {c : Context} :
    betaFreeContext? c = true ↔ BetaFreeContext c :=
  final_catalog_projects_decidable_classification_catalog.betaFreeContextClassificationIff

/-- The final catalog projects the beta-free classification closure on the closed fragment. -/
theorem final_catalog_projects_closedFragment_implies_betaFree_classification_true
    {t : HOTerm} :
    ClosedFragment t → betaFree? t = true :=
  final_catalog_projects_decidable_classification_catalog.closedFragmentImpliesBetaFreeClassificationTrue

/-- The final catalog projects the binder-free classification closure on the closed fragment. -/
theorem final_catalog_projects_closedFragment_implies_binderFree_classification_true
    {t : HOTerm} :
    ClosedFragment t → binderFree? t = true :=
  final_catalog_projects_decidable_classification_catalog.closedFragmentImpliesBinderFreeClassificationTrue

/-- The final catalog projects the linear classification closure on share-free closed fragments. -/
theorem final_catalog_projects_shareFree_closedFragment_implies_linear_classification_true
    {t : HOTerm} :
    ClosedFragment t → ShareFreeHOTerm t → linear? t = true :=
  final_catalog_projects_decidable_classification_catalog.shareFreeClosedFragmentImpliesLinearClassificationTrue

/-- The final catalog projects the DAG/shared classification closure on embedded shared terms. -/
theorem final_catalog_projects_embedSharedTerm_implies_dagShared_classification_true
    (t : SharedTerm) :
    dagShared? (embedSharedTerm t) = true :=
  final_catalog_projects_decidable_classification_catalog.embedSharedTermImpliesDagSharedClassificationTrue t

/-- The final catalog projects binder-free connector preservation from the context classification. -/
theorem final_catalog_projects_binderFreeContext_classification_true_implies_connector_preserves_binderFree
    {c : Context} {t : HOTerm} :
    binderFreeContext? c = true → BinderFreeHOTerm t → BinderFreeHOTerm (Context.connector c t) :=
  final_catalog_projects_decidable_classification_catalog.binderFreeContextClassificationTrueImpliesConnectorPreservesBinderFree

/-- The final catalog projects beta-free connector preservation from the context classification. -/
theorem final_catalog_projects_betaFreeContext_classification_true_implies_connector_preserves_betaFree
    {c : Context} {t : HOTerm} :
    betaFreeContext? c = true → BetaFreeHOTerm t → BetaFreeHOTerm (Context.connector c t) :=
  final_catalog_projects_decidable_classification_catalog.betaFreeContextClassificationTrueImpliesConnectorPreservesBetaFree

/-- The final catalog projects beta-freeness of the old closed fragment. -/
theorem final_catalog_projects_closed_fragment_beta_free
    {t : HOTerm} :
    ClosedFragment t -> BetaFreeHOTerm t :=
  final_catalog_projects_capture_subfamily_catalog.closedFragmentBetaFree

/-- The final catalog projects binder-freeness of the old closed fragment. -/
theorem final_catalog_projects_closed_fragment_binder_free
    {t : HOTerm} :
    ClosedFragment t -> BinderFreeHOTerm t :=
  final_catalog_projects_capture_subfamily_catalog.closedFragmentBinderFree

/-- The final catalog projects binder-free term closure under binder-free contexts. -/
theorem final_catalog_projects_binder_free_term_context_closure
    {c : Context} {t : HOTerm} :
    BinderFreeContext c -> BinderFreeHOTerm t -> BinderFreeHOTerm (Context.connector c t) :=
  final_catalog_projects_capture_subfamily_catalog.binderFreeContextClosure

/-- The final catalog projects beta-free term closure under beta-free contexts. -/
theorem final_catalog_projects_beta_free_term_context_closure
    {c : Context} {t : HOTerm} :
    BetaFreeContext c -> BetaFreeHOTerm t -> BetaFreeHOTerm (Context.connector c t) :=
  final_catalog_projects_capture_subfamily_catalog.betaFreeContextClosure

/-- The final catalog projects the old-boundary embedding theorem for share-free fragments. -/
theorem final_catalog_projects_share_free_fragment_old_boundary_embedding
    {t : HOTerm} :
    ClosedFragment t -> ShareFreeHOTerm t -> ShareFreeBoundaryEmbedding t :=
  final_catalog_projects_capture_subfamily_catalog.shareFreeBoundaryEmbedding

/-- The final catalog projects the exact beta counterexample package. -/
theorem final_catalog_projects_beta_counterexample_package :
    BetaCounterexamplePackage :=
  final_catalog_projects_capture_subfamily_catalog.betaCounterexamplePackage

/-- The final catalog projects the exact capture-side freshness obligation. -/
theorem final_catalog_projects_capture_safe_freshness
    {name binderName : Nat} {arg body : HOTerm} :
    CaptureSafeSubstitutionObligation name binderName arg body ->
      FreshFor binderName arg :=
  final_catalog_projects_capture_subfamily_catalog.captureSafeFreshness

/-- The final catalog projects binder-free substitution closure under the exact capture obligation. -/
theorem final_catalog_projects_capture_safe_binder_free_closure
    {name binderName : Nat} {arg body : HOTerm} :
    CaptureSafeSubstitutionObligation name binderName arg body ->
      BinderFreeHOTerm (binderAwareSubstitute name arg body) :=
  final_catalog_projects_capture_subfamily_catalog.captureSafeBinderFreeClosure

/-- The final catalog projects share-free substitution closure under the exact capture obligation. -/
theorem final_catalog_projects_capture_safe_share_free_closure
    {name binderName : Nat} {arg body : HOTerm} :
    CaptureSafeSubstitutionObligation name binderName arg body ->
      ShareFreeHOTerm (binderAwareSubstitute name arg body) :=
  final_catalog_projects_capture_subfamily_catalog.captureSafeShareFreeClosure

/-- The final catalog projects the tree/binder-free branch split. -/
theorem final_catalog_projects_tree_binder_free_branch
    {t : HOTerm} :
    ClosedFragment t -> ShareFreeHOTerm t ->
      LinearHOTerm t /\ ShareFreeBoundaryEmbedding t :=
  final_catalog_projects_capture_subfamily_catalog.treeBinderFreeBranch

/-- The final catalog projects the shared/DAG branch split. -/
theorem final_catalog_projects_shared_dag_branch
    (t : SharedTerm) :
    DAGSharedHOTerm (embedSharedTerm t) :=
  final_catalog_projects_capture_subfamily_catalog.sharedDAGBranch t

/-- The final catalog projects the explicit-sharing branch split. -/
theorem final_catalog_projects_explicit_sharing_branch :
    ExplicitSharingHO explicitSharingPolicy :=
  final_catalog_projects_capture_subfamily_catalog.explicitSharingBranch

/-- The final catalog projects the beta-compatible branch split. -/
theorem final_catalog_projects_beta_compatible_branch :
    BetaCompatibleStatus betaCompatiblePolicy :=
  final_catalog_projects_capture_subfamily_catalog.betaCompatibleBranch

/-- The final catalog projects binder-free closure under the exact context-safe obligation. -/
theorem final_catalog_projects_context_safe_binder_free_closure
    {c : Context} {t : HOTerm} :
    ContextSafeSubstitutionObligation c t ->
      BinderFreeHOTerm (Context.connector c t) :=
  final_catalog_projects_capture_subfamily_catalog.contextSafeBinderFreeClosure

/-- The final catalog projects beta-free closure under the exact context-safe obligation. -/
theorem final_catalog_projects_context_safe_beta_free_closure
    {c : Context} {t : HOTerm} :
    ContextSafeSubstitutionObligation c t ->
      BetaFreeHOTerm (Context.connector c t) :=
  final_catalog_projects_capture_subfamily_catalog.contextSafeBetaFreeClosure

/-- The final catalog projects the still-open full-capture semantics marker. -/
theorem final_catalog_projects_full_capture_semantics_open :
    FullCaptureSemanticsStatus :=
  final_catalog_projects_capture_subfamily_catalog.fullCaptureSemanticsOpen

/-- The final catalog projects the blocker against an unqualified full lift. -/
theorem final_catalog_projects_unqualified_lift_blocker :
    ¬ UnqualifiedHigherOrderRewritingLiftClaim :=
  higher_order_rewriting_final_catalog.unqualifiedLiftBlocked

end OperatorKO7.HigherOrderRewritingFinalCatalog
