import OperatorKO7.Meta.HigherOrderRewriting_PolicyAudit
import OperatorKO7.Meta.HigherOrderRewriting_Closeout

/-!
# Higher-Order Rewriting Catalog

This file packages the explicit M2 higher-order rewriting layer within its declared scope.
It records the transported no-sharing boundary, the shared-surrogate and explicit-sharing
counterexamples, the stated policy-subfamily split, and the blocker against an unqualified
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
open OperatorKO7.HigherOrderRewritingDecidableClassifiers
open OperatorKO7.HigherOrderRewritingCaptureDecidable
open OperatorKO7.HigherOrderRewritingPolicyAudit

/-- Paper-facing M2 catalog for the explicit higher-order rewriting layer. -/
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
      ClosedFragment t → ClosedFragment (Context.plug c t)
  sharedBinderFreeContextClosed :
    ∀ {c : Context}, BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.plug c t)
  explicitSharingBinderFreeContextClosed :
    ∀ {c : Context}, BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.plug c t)
  betaStepTransport :
    ∀ {a b : HOTerm}, BetaStep a b → RewriteStep betaCompatiblePolicy a b
  betaContextualClosure :
    ∀ {a b : HOTerm}, BetaStep a b → ∀ context : Context,
      ContextualBetaStep (Context.plug context a) (Context.plug context b)
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
  decidableClassifierCatalog : HigherOrderDecidableClassifierCatalog
  captureDecidableCatalog : HigherOrderCaptureDecidableCatalog
  policyAuditCatalog : HigherOrderPolicyAuditCatalog
  unqualifiedLiftBlocked : ¬ UnqualifiedHigherOrderRewritingLiftClaim

/-- Canonical M2 catalog for the explicit higher-order rewriting layer. -/
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
  · exact higher_order_decidable_classifier_catalog
  · exact higher_order_capture_decidable_catalog
  · exact higher_order_policy_audit_catalog
  · exact shared_policy_blocks_unqualified_higher_order_rewriting_lift

/-- The catalog projects the transported restricted-fragment theorem. -/
theorem final_catalog_projects_restricted_fragment_transport :
    ∀ t : SharedTerm,
      ClosedFragment
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm t)) :=
  higher_order_rewriting_final_catalog.restrictedFragmentTransport

/-- The catalog projects the transported theorem-visible no-sharing boundary. -/
theorem final_catalog_projects_no_sharing_boundary_transport :
    NoSharingBoundaryStatus :=
  higher_order_rewriting_final_catalog.noSharingBoundaryTransport

/-- The catalog projects the shared-surrogate orienting counter. -/
theorem final_catalog_projects_shared_policy_orients_step :
    PolicyOrientsStep sharedPolicy :=
  higher_order_rewriting_final_catalog.sharedPolicyOrientsStep

/-- The catalog projects the explicit-sharing orienting counter. -/
theorem final_catalog_projects_explicit_sharing_policy_orients_step :
    PolicyOrientsStep explicitSharingPolicy :=
  higher_order_rewriting_final_catalog.explicitSharingPolicyOrientsStep

/-- The catalog projects the transported shared-surrogate counterexample. -/
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

/-- The catalog projects the explicit-sharing counterexample. -/
theorem final_catalog_projects_explicit_sharing_counterexample :
    ∀ b s n : SharedTerm,
      PolicyCounter explicitSharingPolicy
        (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
      PolicyCounter explicitSharingPolicy
        (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n))) :=
  higher_order_rewriting_final_catalog.explicitSharingCounterexample

/-- The catalog projects tree-policy binder-free substitution closure. -/
theorem final_catalog_projects_tree_binder_free_substitution_closed
    {name : Nat} {replacement t : HOTerm} :
    ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t) :=
  higher_order_rewriting_final_catalog.treeBinderFreeSubstitutionClosed

/-- The catalog projects shared-policy binder-free substitution closure. -/
theorem final_catalog_projects_shared_binder_free_substitution_closed
    {name : Nat} {replacement t : HOTerm} :
    ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t) :=
  higher_order_rewriting_final_catalog.sharedBinderFreeSubstitutionClosed

/-- The catalog projects explicit-sharing binder-free substitution closure. -/
theorem final_catalog_projects_explicit_sharing_binder_free_substitution_closed
    {name : Nat} {replacement t : HOTerm} :
    ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t) :=
  higher_order_rewriting_final_catalog.explicitSharingBinderFreeSubstitutionClosed

/-- The catalog projects tree-policy binder-free context closure. -/
theorem final_catalog_projects_tree_binder_free_context_closed
    {c : Context} : BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.plug c t) :=
  higher_order_rewriting_final_catalog.treeBinderFreeContextClosed

/-- The catalog projects shared-policy binder-free context closure. -/
theorem final_catalog_projects_shared_binder_free_context_closed
    {c : Context} : BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.plug c t) :=
  higher_order_rewriting_final_catalog.sharedBinderFreeContextClosed

/-- The catalog projects explicit-sharing binder-free context closure. -/
theorem final_catalog_projects_explicit_sharing_binder_free_context_closed
    {c : Context} : BinderFreeContext c → ∀ {t : HOTerm},
      ClosedFragment t → ClosedFragment (Context.plug c t) :=
  higher_order_rewriting_final_catalog.explicitSharingBinderFreeContextClosed

/-- The catalog projects beta-step transport into the beta-compatible rewrite branch. -/
theorem final_catalog_projects_beta_step_transport
    {a b : HOTerm} :
    BetaStep a b → RewriteStep betaCompatiblePolicy a b :=
  higher_order_rewriting_final_catalog.betaStepTransport

/-- The catalog projects contextual beta-step closure. -/
theorem final_catalog_projects_beta_contextual_closure
    {a b : HOTerm} :
    BetaStep a b → ∀ context : Context,
      ContextualBetaStep (Context.plug context a) (Context.plug context b) :=
  higher_order_rewriting_final_catalog.betaContextualClosure

/-- The catalog projects the named binder-aware freshness obligation. -/
theorem final_catalog_projects_binder_aware_freshness_obligation
    {name binderName : Nat} {arg body : HOTerm} :
    BinderAwareSubstitutionObligation name binderName arg body →
      FreshFor binderName arg :=
  higher_order_rewriting_final_catalog.binderAwareFreshnessObligation

/-- The catalog projects the concrete beta counterexample. -/
theorem final_catalog_projects_beta_compatible_counterexample :
    ∃ a b : HOTerm,
      BetaStep a b ∧
        ¬ PolicyCounter betaCompatiblePolicy b < PolicyCounter betaCompatiblePolicy a :=
  higher_order_rewriting_final_catalog.betaCompatibleCounterexample

/-- The catalog projects the blocker showing that the declared policy counter does not
orient every beta step for the beta-compatible policy. -/
theorem final_catalog_projects_beta_compatible_not_oriented :
    ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy :=
  higher_order_rewriting_final_catalog.betaCompatibleNotOriented

/-- The catalog projects the clean branch split for the declared policy classes. -/
theorem final_catalog_projects_policy_branch_split :
    PolicyBranchSplitStatus :=
  higher_order_rewriting_final_catalog.policyBranchSplit

/-- The catalog projects the stated policy-subfamily status split. -/
theorem final_catalog_projects_policy_subfamilies :
    PolicySubfamilyStatus :=
  higher_order_rewriting_final_catalog.policySubfamilies

/-- The catalog projects the capture/subfamily catalog. -/
theorem final_catalog_projects_capture_subfamily_catalog :
    HigherOrderCaptureSubfamilyCatalog :=
  higher_order_rewriting_final_catalog.captureSubfamilyCatalog

/-- The catalog projects the executable classifier catalog. -/
theorem final_catalog_projects_decidable_classifier_catalog :
    HigherOrderDecidableClassifierCatalog :=
  higher_order_rewriting_final_catalog.decidableClassifierCatalog

/-- The catalog projects the executable capture-decision catalog. -/
theorem final_catalog_projects_capture_decidable_catalog :
    HigherOrderCaptureDecidableCatalog :=
  higher_order_rewriting_final_catalog.captureDecidableCatalog

/-- The catalog projects the finite policy audit catalog. -/
theorem final_catalog_projects_policy_audit_catalog :
    HigherOrderPolicyAuditCatalog :=
  higher_order_rewriting_final_catalog.policyAuditCatalog

/-- The catalog projects the typed full-capture boundary catalog. -/
theorem final_catalog_projects_full_capture_boundary_catalog :
    OperatorKO7.HigherOrderRewritingFullCaptureBoundary.HigherOrderFullCaptureBoundaryCatalog :=
  OperatorKO7.HigherOrderRewritingFullCaptureBoundary.higher_order_full_capture_boundary_catalog

/-- The catalog projects the finite M2 catalog. -/
theorem final_catalog_projects_closeout_catalog :
    OperatorKO7.HigherOrderRewritingCloseout.HigherOrderRewritingCloseoutCatalog :=
  OperatorKO7.HigherOrderRewritingCloseout.higher_order_rewriting_closeout_catalog

/-- The catalog projects the `isLam` classifier iff theorem. -/
theorem final_catalog_projects_isLam_classifier_eq_true_iff
    {t : HOTerm} :
    isLam t = true ↔ IsLam t :=
  final_catalog_projects_decidable_classifier_catalog.isLamClassifierIff

/-- The catalog projects the binder-free classifier iff theorem. -/
theorem final_catalog_projects_binderFree_classifier_eq_true_iff
    {t : HOTerm} :
    binderFree? t = true ↔ BinderFreeHOTerm t :=
  final_catalog_projects_decidable_classifier_catalog.binderFreeClassifierIff

/-- The catalog projects the share-free classifier iff theorem. -/
theorem final_catalog_projects_shareFree_classifier_eq_true_iff
    {t : HOTerm} :
    shareFree? t = true ↔ ShareFreeHOTerm t :=
  final_catalog_projects_decidable_classifier_catalog.shareFreeClassifierIff

/-- The catalog projects the beta-free classifier iff theorem. -/
theorem final_catalog_projects_betaFree_classifier_eq_true_iff
    {t : HOTerm} :
    betaFree? t = true ↔ BetaFreeHOTerm t :=
  final_catalog_projects_decidable_classifier_catalog.betaFreeClassifierIff

/-- The catalog projects the linear classifier iff theorem. -/
theorem final_catalog_projects_linear_classifier_eq_true_iff
    {t : HOTerm} :
    linear? t = true ↔ LinearHOTerm t :=
  final_catalog_projects_decidable_classifier_catalog.linearClassifierIff

/-- The catalog projects the DAG/shared classifier iff theorem. -/
theorem final_catalog_projects_dagShared_classifier_eq_true_iff
    {t : HOTerm} :
    dagShared? t = true ↔ DAGSharedHOTerm t :=
  final_catalog_projects_decidable_classifier_catalog.dagSharedClassifierIff

/-- The catalog projects the binder-free context classifier iff theorem. -/
theorem final_catalog_projects_binderFreeContext_classifier_eq_true_iff
    {c : Context} :
    binderFreeContext? c = true ↔ BinderFreeContext c :=
  final_catalog_projects_decidable_classifier_catalog.binderFreeContextClassifierIff

/-- The catalog projects the beta-free context classifier iff theorem. -/
theorem final_catalog_projects_betaFreeContext_classifier_eq_true_iff
    {c : Context} :
    betaFreeContext? c = true ↔ BetaFreeContext c :=
  final_catalog_projects_decidable_classifier_catalog.betaFreeContextClassifierIff

/-- The catalog projects the beta-free classifier closure on the closed fragment. -/
theorem final_catalog_projects_closedFragment_implies_betaFree_classifier_true
    {t : HOTerm} :
    ClosedFragment t → betaFree? t = true :=
  final_catalog_projects_decidable_classifier_catalog.closedFragmentImpliesBetaFreeClassifierTrue

/-- The catalog projects the binder-free classifier closure on the closed fragment. -/
theorem final_catalog_projects_closedFragment_implies_binderFree_classifier_true
    {t : HOTerm} :
    ClosedFragment t → binderFree? t = true :=
  final_catalog_projects_decidable_classifier_catalog.closedFragmentImpliesBinderFreeClassifierTrue

/-- The catalog projects the linear classifier closure on share-free closed fragments. -/
theorem final_catalog_projects_shareFree_closedFragment_implies_linear_classifier_true
    {t : HOTerm} :
    ClosedFragment t → ShareFreeHOTerm t → linear? t = true :=
  final_catalog_projects_decidable_classifier_catalog.shareFreeClosedFragmentImpliesLinearClassifierTrue

/-- The catalog projects the DAG/shared classifier closure on embedded shared terms. -/
theorem final_catalog_projects_embedSharedTerm_implies_dagShared_classifier_true
    (t : SharedTerm) :
    dagShared? (embedSharedTerm t) = true :=
  final_catalog_projects_decidable_classifier_catalog.embedSharedTermImpliesDagSharedClassifierTrue t

/-- The catalog projects binder-free plug preservation from the context classifier. -/
theorem final_catalog_projects_binderFreeContext_classifier_true_implies_plug_preserves_binderFree
    {c : Context} {t : HOTerm} :
    binderFreeContext? c = true → BinderFreeHOTerm t → BinderFreeHOTerm (Context.plug c t) :=
  final_catalog_projects_decidable_classifier_catalog.binderFreeContextClassifierTrueImpliesPlugPreservesBinderFree

/-- The catalog projects beta-free plug preservation from the context classifier. -/
theorem final_catalog_projects_betaFreeContext_classifier_true_implies_plug_preserves_betaFree
    {c : Context} {t : HOTerm} :
    betaFreeContext? c = true → BetaFreeHOTerm t → BetaFreeHOTerm (Context.plug c t) :=
  final_catalog_projects_decidable_classifier_catalog.betaFreeContextClassifierTrueImpliesPlugPreservesBetaFree

/-- The catalog projects beta-freeness of the old closed fragment. -/
theorem final_catalog_projects_closed_fragment_beta_free
    {t : HOTerm} :
    ClosedFragment t -> BetaFreeHOTerm t :=
  final_catalog_projects_capture_subfamily_catalog.closedFragmentBetaFree

/-- The catalog projects binder-freeness of the old closed fragment. -/
theorem final_catalog_projects_closed_fragment_binder_free
    {t : HOTerm} :
    ClosedFragment t -> BinderFreeHOTerm t :=
  final_catalog_projects_capture_subfamily_catalog.closedFragmentBinderFree

/-- The catalog projects binder-free term closure under binder-free contexts. -/
theorem final_catalog_projects_binder_free_term_context_closure
    {c : Context} {t : HOTerm} :
    BinderFreeContext c -> BinderFreeHOTerm t -> BinderFreeHOTerm (Context.plug c t) :=
  final_catalog_projects_capture_subfamily_catalog.binderFreeContextClosure

/-- The catalog projects beta-free term closure under beta-free contexts. -/
theorem final_catalog_projects_beta_free_term_context_closure
    {c : Context} {t : HOTerm} :
    BetaFreeContext c -> BetaFreeHOTerm t -> BetaFreeHOTerm (Context.plug c t) :=
  final_catalog_projects_capture_subfamily_catalog.betaFreeContextClosure

/-- The catalog projects the old-boundary embedding theorem for share-free fragments. -/
theorem final_catalog_projects_share_free_fragment_old_boundary_embedding
    {t : HOTerm} :
    ClosedFragment t -> ShareFreeHOTerm t -> ShareFreeBoundaryEmbedding t :=
  final_catalog_projects_capture_subfamily_catalog.shareFreeBoundaryEmbedding

/-- The catalog projects the stated beta counterexample package. -/
theorem final_catalog_projects_beta_counterexample_package :
    BetaCounterexamplePackage :=
  final_catalog_projects_capture_subfamily_catalog.betaCounterexamplePackage

/-- The catalog projects the stated capture-side freshness obligation. -/
theorem final_catalog_projects_capture_safe_freshness
    {name binderName : Nat} {arg body : HOTerm} :
    CaptureSafeSubstitutionObligation name binderName arg body ->
      FreshFor binderName arg :=
  final_catalog_projects_capture_subfamily_catalog.captureSafeFreshness

/-- The catalog projects binder-free substitution closure under the stated capture obligation. -/
theorem final_catalog_projects_capture_safe_binder_free_closure
    {name binderName : Nat} {arg body : HOTerm} :
    CaptureSafeSubstitutionObligation name binderName arg body ->
      BinderFreeHOTerm (binderAwareSubstitute name arg body) :=
  final_catalog_projects_capture_subfamily_catalog.captureSafeBinderFreeClosure

/-- The catalog projects share-free substitution closure under the stated capture obligation. -/
theorem final_catalog_projects_capture_safe_share_free_closure
    {name binderName : Nat} {arg body : HOTerm} :
    CaptureSafeSubstitutionObligation name binderName arg body ->
      ShareFreeHOTerm (binderAwareSubstitute name arg body) :=
  final_catalog_projects_capture_subfamily_catalog.captureSafeShareFreeClosure

/-- The catalog projects the tree/binder-free branch split. -/
theorem final_catalog_projects_tree_binder_free_branch
    {t : HOTerm} :
    ClosedFragment t -> ShareFreeHOTerm t ->
      LinearHOTerm t /\ ShareFreeBoundaryEmbedding t :=
  final_catalog_projects_capture_subfamily_catalog.treeBinderFreeBranch

/-- The catalog projects the shared/DAG branch split. -/
theorem final_catalog_projects_shared_dag_branch
    (t : SharedTerm) :
    DAGSharedHOTerm (embedSharedTerm t) :=
  final_catalog_projects_capture_subfamily_catalog.sharedDAGBranch t

/-- The catalog projects the explicit-sharing branch split. -/
theorem final_catalog_projects_explicit_sharing_branch :
    ExplicitSharingHO explicitSharingPolicy :=
  final_catalog_projects_capture_subfamily_catalog.explicitSharingBranch

/-- The catalog projects the beta-compatible branch split. -/
theorem final_catalog_projects_beta_compatible_branch :
    BetaCompatibleStatus betaCompatiblePolicy :=
  final_catalog_projects_capture_subfamily_catalog.betaCompatibleBranch

/-- The catalog projects binder-free closure under the stated context-safe obligation. -/
theorem final_catalog_projects_context_safe_binder_free_closure
    {c : Context} {t : HOTerm} :
    ContextSafeSubstitutionObligation c t ->
      BinderFreeHOTerm (Context.plug c t) :=
  final_catalog_projects_capture_subfamily_catalog.contextSafeBinderFreeClosure

/-- The catalog projects beta-free closure under the stated context-safe obligation. -/
theorem final_catalog_projects_context_safe_beta_free_closure
    {c : Context} {t : HOTerm} :
    ContextSafeSubstitutionObligation c t ->
      BetaFreeHOTerm (Context.plug c t) :=
  final_catalog_projects_capture_subfamily_catalog.contextSafeBetaFreeClosure

/-- The catalog projects the proved full-capture boundary marker. -/
theorem final_catalog_projects_full_capture_semantics_exact_boundary :
    FullCaptureSemanticsStatus :=
  final_catalog_projects_capture_subfamily_catalog.fullCaptureSemanticsExactBoundary

/-- The catalog projects the typed obstruction to an unqualified full lift. -/
theorem final_catalog_projects_unqualified_lift_blocker :
    ¬ UnqualifiedHigherOrderRewritingLiftClaim :=
  higher_order_rewriting_final_catalog.unqualifiedLiftBlocked

end OperatorKO7.HigherOrderRewritingFinalCatalog
