import OperatorKO7.Meta.HigherOrderSharingBoundary_FinalCatalog
import OperatorKO7.Meta.HigherOrderRewriting_FinalCatalog

/-!
# M2 Higher-Order Sharing Boundary API

This module exposes the already-validated M2 sharing-boundary catalog through
stable API names only. It does not add a new theorem program.
-/

namespace OperatorKO7.HigherOrderSharingBoundaryAPI

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderSharingBoundary
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifications
open OperatorKO7.HigherOrderRewritingCaptureDecidable
open OperatorKO7.HigherOrderRewritingPolicyAudit

/-- Stable API alias for the final M2 catalog. -/
abbrev FinalCatalog : Prop := HigherOrderSharingBoundaryCatalog

/-- Stable API alias for the explicit M2 scope marker. -/
abbrev FullHigherOrderOutsideCatalog : Prop := FullHigherOrderRewritingOutsideCatalog

/-- Stable API entrypoint for the final M2 catalog. -/
theorem final_catalog : FinalCatalog :=
  higher_order_sharing_boundary_final_catalog

/-- Stable API projection for the shared-policy counterexample. -/
theorem shared_policy_counterexample :
    HOPolicyOrientsStep .shared
      ∧ (∀ b s n : SharedTerm,
        HOPolicyCounter .shared
          (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
        HOPolicyCounter .shared
          (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n)))) :=
  final_catalog_projects_shared_counterexample

/-- Stable API projection for the blocker against an unqualified lift. -/
theorem unqualified_lift_blocker :
    ¬ UnqualifiedHigherOrderLiftClaim :=
  final_catalog_projects_unqualified_lift_blocker

/-- Stable API projection for the theorem-visible no-sharing requirement. -/
theorem no_sharing_requirement :
    NoSharingBoundaryStatus :=
  final_catalog_projects_no_sharing_requirement

/-- Stable API projection marking full higher-order rewriting as outside the current
catalog. -/
theorem full_higher_order_outside_catalog :
    FullHigherOrderOutsideCatalog :=
  final_catalog_records_full_higher_order_not_claimed

/-- Stable API alias for the explicit higher-order rewriting policy carrier. -/
abbrev RewritingPolicyClass := OperatorKO7.HigherOrderRewritingSyntax.PolicyClass

/-- Stable API alias for the explicit higher-order rewriting term syntax. -/
abbrev RewritingTerm := OperatorKO7.HigherOrderRewritingSyntax.HOTerm

/-- Stable API alias for the explicit higher-order rewriting one-hole contexts. -/
abbrev RewritingContext := OperatorKO7.HigherOrderRewritingSyntax.Context

/-- Stable API alias for the explicit closed fragment. -/
abbrev RewritingClosedFragment := OperatorKO7.HigherOrderRewritingSyntax.ClosedFragment

/-- Stable API alias for the explicit higher-order rewriting step relation. -/
abbrev RewritingStep := OperatorKO7.HigherOrderRewritingBoundary.RewriteStep

/-- Stable API alias for the explicit higher-order rewriting counter. -/
abbrev RewritingCounter := OperatorKO7.HigherOrderRewritingBoundary.PolicyCounter

/-- Stable API alias for the explicit higher-order rewriting orientation predicate. -/
abbrev RewritingOrientsStep := OperatorKO7.HigherOrderRewritingBoundary.PolicyOrientsStep

/-- Stable API alias for the explicit beta-step relation. -/
abbrev RewritingBetaStep := OperatorKO7.HigherOrderRewritingBetaBinder.BetaStep

/-- Stable API alias for contextual beta closure over one-hole contexts. -/
abbrev RewritingContextualBetaStep :=
  OperatorKO7.HigherOrderRewritingBetaBinder.ContextualBetaStep

/-- Stable API alias for binder-free higher-order rewriting contexts. -/
abbrev RewritingBinderFreeContext :=
  OperatorKO7.HigherOrderRewritingBetaBinder.BinderFreeContext

/-- Stable API alias for beta-step orientation restricted to the policy counter. -/
abbrev RewritingBetaStepOrientsCounter (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingBetaBinder.BetaStepOrientsPolicyCounter policy

/-- Stable API alias for the named binder-aware freshness predicate. -/
abbrev RewritingFreshFor (binderName : Nat) (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingBetaBinder.FreshFor binderName t

/-- Stable API alias for the named binder-aware substitution obligation. -/
abbrev RewritingBinderAwareSubstitutionObligation
    (name binderName : Nat) (arg body : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingBetaBinder.BinderAwareSubstitutionObligation
    name binderName arg body

/-- Stable API alias for the conservative linear higher-order fragment. -/
abbrev RewritingLinearTerm (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.LinearHOTerm t

/-- Stable API alias for the conservative beta-free term fragment. -/
abbrev RewritingBetaFreeTerm (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.BetaFreeHOTerm t

/-- Stable API alias for the conservative binder-free term fragment. -/
abbrev RewritingBinderFreeTerm (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.BinderFreeHOTerm t

/-- Stable API alias for the conservative share-free term fragment. -/
abbrev RewritingShareFreeTerm (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.ShareFreeHOTerm t

/-- Stable API alias for the conservative DAG/shared fragment. -/
abbrev RewritingDAGSharedTerm (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.DAGSharedHOTerm t

/-- Stable API alias for beta-free connectorging contexts. -/
abbrev RewritingBetaFreeContext (c : RewritingContext) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.BetaFreeContext c

/-- Stable API alias for the exact capture-side substitution obligation. -/
abbrev RewritingCaptureSafeSubstitutionObligation
    (name binderName : Nat) (arg body : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.CaptureSafeSubstitutionObligation
    name binderName arg body

/-- Stable API alias for the exact context-side substitution obligation. -/
abbrev RewritingContextSafeSubstitutionObligation
    (c : RewritingContext) (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.ContextSafeSubstitutionObligation c t

/-- Stable API alias for the old-boundary embedding witness on share-free fragments. -/
abbrev RewritingShareFreeBoundaryEmbedding (t : RewritingTerm) : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.ShareFreeBoundaryEmbedding t

/-- Stable API alias for the packaged beta counterexample. -/
abbrev RewritingBetaCounterexamplePackage : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.BetaCounterexamplePackage

/-- Stable API alias for the capture/subfamily catalog. -/
abbrev RewritingCaptureSubfamilyCatalog : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.HigherOrderCaptureSubfamilyCatalog

/-- Stable API alias for the decidable classification catalog. -/
abbrev RewritingDecidableClassificationCatalog : Prop :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.HigherOrderDecidableClassificationCatalog

/-- Stable API alias for the executable capture-decision catalog. -/
abbrev RewritingCaptureDecidableCatalog : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureDecidable.HigherOrderCaptureDecidableCatalog

/-- Stable API alias for the finite higher-order policy audit catalog. -/
abbrev RewritingPolicyAuditCatalog : Prop :=
  OperatorKO7.HigherOrderRewritingPolicyAudit.HigherOrderPolicyAuditCatalog

/-- Stable API alias for the typed full-capture boundary catalog. -/
abbrev RewritingFullCaptureBoundaryCatalog : Prop :=
  OperatorKO7.HigherOrderRewritingFullCaptureBoundary.HigherOrderFullCaptureBoundaryCatalog

/-- Stable API alias for the finite M2 closeout catalog. -/
abbrev RewritingCloseoutCatalog : Prop :=
  OperatorKO7.HigherOrderRewritingCloseout.HigherOrderRewritingCloseoutCatalog

/-- Stable API alias for the still-open full-capture semantics marker. -/
abbrev RewritingFullCaptureSemanticsStatus : Prop :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.FullCaptureSemanticsStatus

/-- Stable API `isLam` classification. -/
def is_lam_classification : RewritingTerm → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.isLam

/-- Stable API binder-free classification. -/
def binder_free_classification : RewritingTerm → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.binderFree?

/-- Stable API share-free classification. -/
def share_free_classification : RewritingTerm → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.shareFree?

/-- Stable API beta-free classification. -/
def beta_free_classification : RewritingTerm → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.betaFree?

/-- Stable API conservative linear classification. -/
def linear_classification : RewritingTerm → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.linear?

/-- Stable API conservative DAG/shared classification. -/
def dag_shared_classification : RewritingTerm → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.dagShared?

/-- Stable API binder-free context classification. -/
def binder_free_context_classification : RewritingContext → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.binderFreeContext?

/-- Stable API beta-free context classification. -/
def beta_free_context_classification : RewritingContext → Bool :=
  OperatorKO7.HigherOrderRewritingDecidableClassifications.betaFreeContext?

/-- Stable API alias for the explicit higher-order rewriting final catalog. -/
abbrev RewritingFinalCatalog : Prop :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.HigherOrderRewritingCatalog

/-- Stable API alias for the exact higher-order rewriting policy-subfamily split. -/
abbrev RewritingPolicySubfamilies : Prop :=
  OperatorKO7.HigherOrderRewritingBoundary.PolicySubfamilyStatus

/-- Stable API alias for the clean policy-branch split after the beta/binder extension. -/
abbrev RewritingPolicyBranchSplit : Prop :=
  OperatorKO7.HigherOrderRewritingBetaBinder.PolicyBranchSplitStatus

/-- Stable API alias for the explicit higher-order rewriting tree subfamily. -/
abbrev TreeHigherOrder (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingSyntax.TreeHO policy

/-- Stable API alias for the explicit higher-order rewriting shared subfamily. -/
abbrev SharedHigherOrder (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingSyntax.SharedHO policy

/-- Stable API alias for the explicit higher-order rewriting explicit-sharing subfamily. -/
abbrev ExplicitSharingHigherOrder (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingSyntax.ExplicitSharingHO policy

/-- Stable API alias for sharing-aware higher-order rewriting status. -/
abbrev SharingAwareHigherOrder (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingBoundary.SharingAwareHO policy

/-- Stable API alias for typed substitution-closed status. -/
abbrev SubstitutionClosedStatus (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingBoundary.SubstitutionClosedHO policy

/-- Stable API alias for typed context-closed status. -/
abbrev ContextClosedStatus (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingBoundary.ContextClosedHO policy

/-- Stable API alias for the typed beta-compatible status. -/
abbrev BetaCompatibleHigherOrderStatus (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingSyntax.BetaCompatibleStatus policy

/-- Stable API alias for the typed binder-aware status. -/
abbrev BinderAwareStatus (policy : RewritingPolicyClass) : Prop :=
  OperatorKO7.HigherOrderRewritingSyntax.BinderStatus policy

/-- Stable API alias for the blocker against an unqualified full higher-order rewriting lift. -/
abbrev UnqualifiedRewritingLiftClaim : Prop :=
  OperatorKO7.HigherOrderRewritingBoundary.UnqualifiedHigherOrderRewritingLiftClaim

/-- Stable API tree/no-sharing policy. -/
def tree_policy : RewritingPolicyClass :=
  OperatorKO7.HigherOrderRewritingSyntax.treePolicy

/-- Stable API shared-surrogate policy. -/
def shared_policy : RewritingPolicyClass :=
  OperatorKO7.HigherOrderRewritingSyntax.sharedPolicy

/-- Stable API explicit-sharing policy. -/
def explicit_sharing_policy : RewritingPolicyClass :=
  OperatorKO7.HigherOrderRewritingSyntax.explicitSharingPolicy

/-- Stable API beta-compatible status policy. -/
def beta_compatible_policy : RewritingPolicyClass :=
  OperatorKO7.HigherOrderRewritingSyntax.betaCompatiblePolicy

/-- Stable API entrypoint for the explicit higher-order rewriting final catalog. -/
theorem rewriting_final_catalog : RewritingFinalCatalog :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.higher_order_rewriting_final_catalog

/-- Stable API projection for the transported restricted fragment. -/
theorem rewriting_restricted_fragment_transport
    (t : SharedTerm) :
    RewritingClosedFragment
      (OperatorKO7.HigherOrderRewritingSyntax.embedBoundaryHOTerm
        (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm t)) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_restricted_fragment_transport t

/-- Stable API projection for the transported no-sharing boundary. -/
theorem no_sharing_boundary_transport :
    NoSharingBoundaryStatus :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_no_sharing_boundary_transport

/-- Stable API projection for the shared-surrogate orienting counter. -/
theorem shared_policy_orients_step :
    RewritingOrientsStep shared_policy :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_shared_policy_orients_step

/-- Stable API projection for the explicit-sharing orienting counter. -/
theorem explicit_sharing_policy_orients_step :
    RewritingOrientsStep explicit_sharing_policy :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_explicit_sharing_policy_orients_step

/-- Stable API transported shared-surrogate counterexample. -/
theorem shared_surrogate_counterexample
    (b s n : SharedTerm) :
    RewritingCounter shared_policy
      (OperatorKO7.HigherOrderRewritingSyntax.embedBoundaryHOTerm
        (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
          (SharedTerm.shareApp s (SharedTerm.recur b s n)))) <
    RewritingCounter shared_policy
      (OperatorKO7.HigherOrderRewritingSyntax.embedBoundaryHOTerm
        (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
          (SharedTerm.recur b s (SharedTerm.succ n)))) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_shared_counterexample b s n

/-- Stable API explicit-sharing counterexample. -/
theorem explicit_sharing_counterexample
    (b s n : SharedTerm) :
    RewritingCounter explicit_sharing_policy
      (OperatorKO7.HigherOrderRewritingSyntax.embedSharedTerm
        (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
    RewritingCounter explicit_sharing_policy
      (OperatorKO7.HigherOrderRewritingSyntax.embedSharedTerm
        (SharedTerm.recur b s (SharedTerm.succ n))) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_explicit_sharing_counterexample b s n

/-- Stable API projection for the capture/subfamily catalog. -/
theorem rewriting_capture_subfamily_catalog :
    RewritingCaptureSubfamilyCatalog :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_capture_subfamily_catalog

/-- Stable API projection for the executable classification catalog. -/
theorem rewriting_decidable_classification_catalog :
    RewritingDecidableClassificationCatalog :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_decidable_classification_catalog

/-- Stable API projection for the executable capture-decision catalog. -/
theorem rewriting_capture_decidable_catalog :
    RewritingCaptureDecidableCatalog :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_capture_decidable_catalog

/-- Stable API projection for the finite higher-order policy audit catalog. -/
theorem rewriting_policy_audit_catalog :
    RewritingPolicyAuditCatalog :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_policy_audit_catalog

/-- Stable API projection for the typed full-capture boundary catalog. -/
theorem rewriting_full_capture_boundary_catalog :
    RewritingFullCaptureBoundaryCatalog :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_full_capture_boundary_catalog

/-- Stable API projection for the finite M2 closeout catalog. -/
theorem rewriting_closeout_catalog :
    RewritingCloseoutCatalog :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_closeout_catalog

/-- Stable API `isLam` classification iff theorem. -/
theorem is_lam_classification_eq_true_iff
    {t : RewritingTerm} :
    is_lam_classification t = true ↔ OperatorKO7.HigherOrderRewritingCaptureSubfamilies.IsLam t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_isLam_classification_eq_true_iff

/-- Stable API binder-free classification iff theorem. -/
theorem binder_free_classification_eq_true_iff
    {t : RewritingTerm} :
    binder_free_classification t = true ↔ RewritingBinderFreeTerm t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_binderFree_classification_eq_true_iff

/-- Stable API share-free classification iff theorem. -/
theorem share_free_classification_eq_true_iff
    {t : RewritingTerm} :
    share_free_classification t = true ↔ RewritingShareFreeTerm t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_shareFree_classification_eq_true_iff

/-- Stable API beta-free classification iff theorem. -/
theorem beta_free_classification_eq_true_iff
    {t : RewritingTerm} :
    beta_free_classification t = true ↔ RewritingBetaFreeTerm t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_betaFree_classification_eq_true_iff

/-- Stable API linear classification iff theorem. -/
theorem linear_classification_eq_true_iff
    {t : RewritingTerm} :
    linear_classification t = true ↔ RewritingLinearTerm t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_linear_classification_eq_true_iff

/-- Stable API DAG/shared classification iff theorem. -/
theorem dag_shared_classification_eq_true_iff
    {t : RewritingTerm} :
    dag_shared_classification t = true ↔ RewritingDAGSharedTerm t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_dagShared_classification_eq_true_iff

/-- Stable API binder-free context classification iff theorem. -/
theorem binder_free_context_classification_eq_true_iff
    {c : RewritingContext} :
    binder_free_context_classification c = true ↔ RewritingBinderFreeContext c :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_binderFreeContext_classification_eq_true_iff

/-- Stable API beta-free context classification iff theorem. -/
theorem beta_free_context_classification_eq_true_iff
    {c : RewritingContext} :
    beta_free_context_classification c = true ↔ RewritingBetaFreeContext c :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_betaFreeContext_classification_eq_true_iff

/-- Stable API beta-free classification closure on the closed fragment. -/
theorem closed_fragment_implies_beta_free_classification_true
    {t : RewritingTerm} :
    RewritingClosedFragment t → beta_free_classification t = true :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_closedFragment_implies_betaFree_classification_true

/-- Stable API binder-free classification closure on the closed fragment. -/
theorem closed_fragment_implies_binder_free_classification_true
    {t : RewritingTerm} :
    RewritingClosedFragment t → binder_free_classification t = true :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_closedFragment_implies_binderFree_classification_true

/-- Stable API linear classification closure on share-free closed fragments. -/
theorem share_free_closed_fragment_implies_linear_classification_true
    {t : RewritingTerm} :
    RewritingClosedFragment t → RewritingShareFreeTerm t → linear_classification t = true :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_shareFree_closedFragment_implies_linear_classification_true

/-- Stable API DAG/shared classification closure on embedded shared terms. -/
theorem embed_shared_term_implies_dag_shared_classification_true
    (t : SharedTerm) :
    dag_shared_classification (OperatorKO7.HigherOrderRewritingSyntax.embedSharedTerm t) = true :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_embedSharedTerm_implies_dagShared_classification_true t

/-- Stable API binder-free connector preservation from the context classification. -/
theorem binder_free_context_classification_true_implies_connector_preserves_binder_free
    {c : RewritingContext} {t : RewritingTerm} :
    binder_free_context_classification c = true → RewritingBinderFreeTerm t →
      RewritingBinderFreeTerm (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_binderFreeContext_classification_true_implies_connector_preserves_binderFree

/-- Stable API beta-free connector preservation from the context classification. -/
theorem beta_free_context_classification_true_implies_connector_preserves_beta_free
    {c : RewritingContext} {t : RewritingTerm} :
    beta_free_context_classification c = true → RewritingBetaFreeTerm t →
      RewritingBetaFreeTerm (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_betaFreeContext_classification_true_implies_connector_preserves_betaFree

/-- Stable API projection for beta-freeness of the old closed fragment. -/
theorem closed_fragment_beta_free
    {t : RewritingTerm} :
    RewritingClosedFragment t -> RewritingBetaFreeTerm t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_closed_fragment_beta_free

/-- Stable API projection for binder-freeness of the old closed fragment. -/
theorem closed_fragment_binder_free
    {t : RewritingTerm} :
    RewritingClosedFragment t -> RewritingBinderFreeTerm t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_closed_fragment_binder_free

/-- Stable API projection for binder-free term closure under binder-free contexts. -/
theorem binder_free_context_term_closure
    {c : RewritingContext} {t : RewritingTerm} :
    RewritingBinderFreeContext c -> RewritingBinderFreeTerm t ->
      RewritingBinderFreeTerm (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_binder_free_term_context_closure

/-- Stable API projection for beta-free term closure under beta-free contexts. -/
theorem beta_free_context_term_closure
    {c : RewritingContext} {t : RewritingTerm} :
    RewritingBetaFreeContext c -> RewritingBetaFreeTerm t ->
      RewritingBetaFreeTerm (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_beta_free_term_context_closure

/-- Stable API projection for the old-boundary embedding theorem on share-free fragments. -/
theorem share_free_fragment_old_boundary_embedding
    {t : RewritingTerm} :
    RewritingClosedFragment t -> RewritingShareFreeTerm t ->
      RewritingShareFreeBoundaryEmbedding t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_share_free_fragment_old_boundary_embedding

/-- Stable API projection for the packaged beta counterexample. -/
theorem beta_counterexample_package :
    RewritingBetaCounterexamplePackage :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_beta_counterexample_package

/-- Stable API projection for the exact capture-side freshness obligation. -/
theorem capture_safe_freshness
    {name binderName : Nat} {arg body : RewritingTerm} :
    RewritingCaptureSafeSubstitutionObligation name binderName arg body ->
      RewritingFreshFor binderName arg :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_capture_safe_freshness

/-- Stable API projection for binder-free substitution closure under the exact capture obligation. -/
theorem capture_safe_binder_free_closure
    {name binderName : Nat} {arg body : RewritingTerm} :
    RewritingCaptureSafeSubstitutionObligation name binderName arg body ->
      RewritingBinderFreeTerm (OperatorKO7.HigherOrderRewritingBetaBinder.binderAwareSubstitute name arg body) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_capture_safe_binder_free_closure

/-- Stable API projection for share-free substitution closure under the exact capture obligation. -/
theorem capture_safe_share_free_closure
    {name binderName : Nat} {arg body : RewritingTerm} :
    RewritingCaptureSafeSubstitutionObligation name binderName arg body ->
      RewritingShareFreeTerm (OperatorKO7.HigherOrderRewritingBetaBinder.binderAwareSubstitute name arg body) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_capture_safe_share_free_closure

/-- Stable API theorem for descent under a binder from the exact capture obligation. -/
theorem capture_safe_under_binder
    {name binderName : Nat} {arg body : RewritingTerm} :
    RewritingCaptureSafeSubstitutionObligation name binderName arg body ->
      OperatorKO7.HigherOrderRewritingBetaBinder.binderAwareSubstitute name arg
        (OperatorKO7.HigherOrderRewritingSyntax.HOTerm.lam binderName body) =
      OperatorKO7.HigherOrderRewritingSyntax.HOTerm.lam binderName
        (OperatorKO7.HigherOrderRewritingBetaBinder.binderAwareSubstitute name arg body) :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.captureSafeSubstitutionObligation_under_binder

/-- Stable API projection for the tree/binder-free branch split. -/
theorem tree_binder_free_branch
    {t : RewritingTerm} :
    RewritingClosedFragment t -> RewritingShareFreeTerm t ->
      RewritingLinearTerm t /\ RewritingShareFreeBoundaryEmbedding t :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_tree_binder_free_branch

/-- Stable API projection for the shared/DAG branch split. -/
theorem shared_dag_branch
    (t : SharedTerm) :
    RewritingDAGSharedTerm (OperatorKO7.HigherOrderRewritingSyntax.embedSharedTerm t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_shared_dag_branch t

/-- Stable API projection for the explicit-sharing branch split. -/
theorem explicit_sharing_branch :
    ExplicitSharingHigherOrder explicit_sharing_policy :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_explicit_sharing_branch

/-- Stable API projection for the beta-compatible branch split. -/
theorem beta_compatible_branch :
    BetaCompatibleHigherOrderStatus beta_compatible_policy :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_beta_compatible_branch

/-- Stable API projection for binder-free closure under the exact context-safe obligation. -/
theorem context_safe_binder_free_closure
    {c : RewritingContext} {t : RewritingTerm} :
    RewritingContextSafeSubstitutionObligation c t ->
      RewritingBinderFreeTerm (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_context_safe_binder_free_closure

/-- Stable API projection for beta-free closure under the exact context-safe obligation. -/
theorem context_safe_beta_free_closure
    {c : RewritingContext} {t : RewritingTerm} :
    RewritingContextSafeSubstitutionObligation c t ->
      RewritingBetaFreeTerm (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_context_safe_beta_free_closure

/-- Stable API projection for the still-open full-capture semantics marker. -/
theorem full_capture_semantics_open :
    RewritingFullCaptureSemanticsStatus :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_full_capture_semantics_open

/-- Stable API projection for the exact policy-subfamily split. -/
theorem rewriting_policy_subfamilies :
    RewritingPolicySubfamilies :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_policy_subfamilies

/-- Stable API tree higher-order subfamily status. -/
theorem tree_subfamily : TreeHigherOrder tree_policy :=
  rewriting_policy_subfamilies.treeSubfamily

/-- Stable API shared higher-order subfamily status. -/
theorem shared_subfamily : SharedHigherOrder shared_policy :=
  rewriting_policy_subfamilies.sharedSubfamily

/-- Stable API explicit-sharing higher-order subfamily status. -/
theorem explicit_sharing_subfamily :
    ExplicitSharingHigherOrder explicit_sharing_policy :=
  rewriting_policy_subfamilies.explicitSharingSubfamily

/-- Stable API sharing-aware status for the shared-surrogate policy. -/
theorem shared_sharing_aware_status :
    SharingAwareHigherOrder shared_policy :=
  rewriting_policy_subfamilies.sharedSharingAware

/-- Stable API sharing-aware status for the explicit-sharing policy. -/
theorem explicit_sharing_aware_status :
    SharingAwareHigherOrder explicit_sharing_policy :=
  rewriting_policy_subfamilies.explicitSharingAware

/-- Stable API typed substitution-closed status for the tree policy. -/
theorem tree_substitution_closed_status :
    SubstitutionClosedStatus tree_policy :=
  rewriting_policy_subfamilies.treeSubstitutionClosed

/-- Stable API typed substitution-closed status for the shared policy. -/
theorem shared_substitution_closed_status :
    SubstitutionClosedStatus shared_policy :=
  rewriting_policy_subfamilies.sharedSubstitutionClosed

/-- Stable API typed substitution-closed status for the explicit-sharing policy. -/
theorem explicit_sharing_substitution_closed_status :
    SubstitutionClosedStatus explicit_sharing_policy :=
  rewriting_policy_subfamilies.explicitSubstitutionClosed

/-- Stable API beta-compatible higher-order status. -/
theorem beta_compatible_status :
    BetaCompatibleHigherOrderStatus beta_compatible_policy :=
  rewriting_policy_subfamilies.betaCompatibleStatus

/-- Stable API binder-aware higher-order status. -/
theorem binder_status : BinderAwareStatus beta_compatible_policy :=
  rewriting_policy_subfamilies.binderStatus

/-- Stable API typed context-closed status for the tree policy. -/
theorem tree_context_closed_status :
    ContextClosedStatus tree_policy :=
  rewriting_policy_subfamilies.treeContextClosed

/-- Stable API typed context-closed status for the shared policy. -/
theorem shared_context_closed_status :
    ContextClosedStatus shared_policy :=
  rewriting_policy_subfamilies.sharedContextClosed

/-- Stable API typed context-closed status for the explicit-sharing policy. -/
theorem explicit_sharing_context_closed_status :
    ContextClosedStatus explicit_sharing_policy :=
  rewriting_policy_subfamilies.explicitContextClosed

/-- Stable API typed context-closed status for the beta-compatible policy. -/
theorem beta_compatible_context_closed_status :
    ContextClosedStatus beta_compatible_policy :=
  rewriting_policy_subfamilies.betaCompatibleContextClosed

/-- Stable API blocker against an unqualified full higher-order rewriting lift. -/
theorem unqualified_rewriting_lift_blocker :
    ¬ UnqualifiedRewritingLiftClaim :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_unqualified_lift_blocker

/-- Stable API tree-policy binder-free substitution closure. -/
theorem tree_binder_free_substitution_closed
    {name : Nat} {replacement t : RewritingTerm} :
    RewritingClosedFragment t →
      RewritingClosedFragment
        (OperatorKO7.HigherOrderRewritingBetaBinder.binderFreeSubstitute name replacement t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_tree_binder_free_substitution_closed

/-- Stable API shared-policy binder-free substitution closure. -/
theorem shared_binder_free_substitution_closed
    {name : Nat} {replacement t : RewritingTerm} :
    RewritingClosedFragment t →
      RewritingClosedFragment
        (OperatorKO7.HigherOrderRewritingBetaBinder.binderFreeSubstitute name replacement t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_shared_binder_free_substitution_closed

/-- Stable API explicit-sharing binder-free substitution closure. -/
theorem explicit_sharing_binder_free_substitution_closed
    {name : Nat} {replacement t : RewritingTerm} :
    RewritingClosedFragment t →
      RewritingClosedFragment
        (OperatorKO7.HigherOrderRewritingBetaBinder.binderFreeSubstitute name replacement t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_explicit_sharing_binder_free_substitution_closed

/-- Stable API tree-policy binder-free context closure. -/
theorem tree_binder_free_context_closed
    {c : RewritingContext} : RewritingBinderFreeContext c → ∀ {t : RewritingTerm},
      RewritingClosedFragment t → RewritingClosedFragment (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_tree_binder_free_context_closed

/-- Stable API shared-policy binder-free context closure. -/
theorem shared_binder_free_context_closed
    {c : RewritingContext} : RewritingBinderFreeContext c → ∀ {t : RewritingTerm},
      RewritingClosedFragment t → RewritingClosedFragment (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_shared_binder_free_context_closed

/-- Stable API explicit-sharing binder-free context closure. -/
theorem explicit_sharing_binder_free_context_closed
    {c : RewritingContext} : RewritingBinderFreeContext c → ∀ {t : RewritingTerm},
      RewritingClosedFragment t → RewritingClosedFragment (OperatorKO7.HigherOrderRewritingSyntax.Context.connector c t) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_explicit_sharing_binder_free_context_closed

/-- Stable API beta-step transport into the beta-compatible rewrite branch. -/
theorem beta_step_transport
    {a b : RewritingTerm} :
    RewritingBetaStep a b → RewritingStep beta_compatible_policy a b :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_beta_step_transport

/-- Stable API contextual beta-step closure. -/
theorem beta_step_contextual_closure
    {a b : RewritingTerm} :
    RewritingBetaStep a b → ∀ context : RewritingContext,
      RewritingContextualBetaStep (OperatorKO7.HigherOrderRewritingSyntax.Context.connector context a)
        (OperatorKO7.HigherOrderRewritingSyntax.Context.connector context b) :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_beta_contextual_closure

/-- Stable API named binder-aware freshness obligation. -/
theorem binder_aware_freshness_obligation
    {name binderName : Nat} {arg body : RewritingTerm} :
    RewritingBinderAwareSubstitutionObligation name binderName arg body →
      RewritingFreshFor binderName arg :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_binder_aware_freshness_obligation

/-- Stable API concrete beta counterexample. -/
theorem beta_compatible_counterexample :
    ∃ a b : RewritingTerm,
      RewritingBetaStep a b ∧
        ¬ RewritingCounter beta_compatible_policy b < RewritingCounter beta_compatible_policy a :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_beta_compatible_counterexample

/-- Stable API blocker showing that the current policy counter does not orient every beta step. -/
theorem beta_compatible_beta_step_blocker :
    ¬ RewritingBetaStepOrientsCounter beta_compatible_policy :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_beta_compatible_not_oriented

/-- Stable API clean split of the current policy branches after the beta/binder extension. -/
theorem beta_binder_branch_split :
    RewritingPolicyBranchSplit :=
  OperatorKO7.HigherOrderRewritingFinalCatalog.final_catalog_projects_policy_branch_split

end OperatorKO7.HigherOrderSharingBoundaryAPI
