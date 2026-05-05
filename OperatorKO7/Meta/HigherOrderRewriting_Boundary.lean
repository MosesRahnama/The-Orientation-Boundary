import OperatorKO7.Meta.HigherOrderSharingBoundary_FinalCatalog
import OperatorKO7.Meta.HigherOrderRewriting_Syntax

/-!
# Higher-Order Rewriting Boundary

This module upgrades M2 from the old higher-order sharing surrogate to an explicit
higher-order rewriting boundary layer. The theorem surface is intentionally exact:

- the existing shared-policy obstruction transports into the explicit syntax,
- explicit-sharing and policy-tagged shared fragments are separated,
- beta and binder branches are recorded as theorem-visible statuses,
- the strongest landed theorem is still a blocker against an unqualified lift.
-/

namespace OperatorKO7.HigherOrderRewritingBoundary

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
open OperatorKO7.HigherOrderRewritingSyntax

/-- Sharing-aware higher-order rewriting policies. -/
abbrev SharingAwareHO (policy : PolicyClass) : Prop :=
  SharedHO policy ∨ ExplicitSharingHO policy

/-- Typed substitution-closed status used in the current M2 higher-order rewriting layer. -/
abbrev SubstitutionClosedHO (policy : PolicyClass) : Prop :=
  BetaFreeHO policy ∧ BinderFreeStatus policy

/-- Typed context-closed status used in the current M2 higher-order rewriting layer. -/
abbrev ContextClosedHO (policy : PolicyClass) : Prop :=
  BinderFreeStatus policy ∨ BinderStatus policy

/-- Policy-indexed higher-order rewriting step. Tree and shared-surrogate policies keep the
application target explicit. The explicit-sharing policy lands on a dedicated `share` node.
The beta branch is recorded only under the typed beta-compatible status. -/
inductive RewriteStep : PolicyClass → HOTerm → HOTerm → Prop
  | rec_succ_tree (policy : PolicyClass) (htree : TreeHO policy) (b s n : HOTerm) :
      RewriteStep policy
        (HOTerm.recur b s (HOTerm.succ n))
        (HOTerm.app s (HOTerm.recur b s n))
  | rec_succ_shared (policy : PolicyClass) (hshared : SharedHO policy) (b s n : HOTerm) :
      RewriteStep policy
        (HOTerm.recur b s (HOTerm.succ n))
        (HOTerm.app s (HOTerm.recur b s n))
  | rec_succ_explicit (policy : PolicyClass) (hexplicit : ExplicitSharingHO policy)
      (b s n : HOTerm) :
      RewriteStep policy
        (HOTerm.recur b s (HOTerm.succ n))
        (HOTerm.share s (HOTerm.recur b s n))
  | beta (policy : PolicyClass) (hbeta : BetaCompatibleStatus policy)
      (name : Nat) (body arg : HOTerm) :
      RewriteStep policy
        (HOTerm.app (HOTerm.lam name body) arg)
        (substitute name arg body)

/-- Policy-sensitive direct counter. The tree fragment counts both application branches,
the shared-surrogate fragment counts only the continuation branch, and the explicit-sharing
fragment counts the dedicated `share` node by its continuation branch. -/
@[simp] def PolicyCounter : PolicyClass → HOTerm → Nat
  | _, .var _ => 0
  | _, .atom => 0
  | policy, .succ t => PolicyCounter policy t + 1
  | policy, .app f a =>
      match policy.sharing with
      | .tree => PolicyCounter policy f + PolicyCounter policy a
      | .shared => PolicyCounter policy a
      | .explicitSharing => PolicyCounter policy f + PolicyCounter policy a
  | policy, .lam _ body => PolicyCounter policy body
  | policy, .recur _ _ n => PolicyCounter policy n
  | policy, .share _ r => PolicyCounter policy r

/-- A policy orients its higher-order rewriting step if the policy counter strictly decreases. -/
abbrev PolicyOrientsStep (policy : PolicyClass) : Prop :=
  ∀ {a b : HOTerm}, RewriteStep policy a b → PolicyCounter policy b < PolicyCounter policy a

/-- Overclaiming higher-order lift statement. The boundary theorems below show that the
shared-surrogate branch defeats it. -/
abbrev UnqualifiedHigherOrderRewritingLiftClaim : Prop :=
  ∀ policy : PolicyClass, ¬ PolicyOrientsStep policy

/-- Exact theorem-visible split of the policy subfamilies tracked in the explicit M2 layer. -/
structure PolicySubfamilyStatus : Prop where
  treeSubfamily : TreeHO treePolicy
  sharedSubfamily : SharedHO sharedPolicy
  explicitSharingSubfamily : ExplicitSharingHO explicitSharingPolicy
  sharedSharingAware : SharingAwareHO sharedPolicy
  explicitSharingAware : SharingAwareHO explicitSharingPolicy
  treeBetaFree : BetaFreeHO treePolicy
  sharedBetaFree : BetaFreeHO sharedPolicy
  explicitBetaFree : BetaFreeHO explicitSharingPolicy
  betaCompatibleStatus : BetaCompatibleStatus betaCompatiblePolicy
  binderStatus : BinderStatus betaCompatiblePolicy
  treeSubstitutionClosed : SubstitutionClosedHO treePolicy
  sharedSubstitutionClosed : SubstitutionClosedHO sharedPolicy
  explicitSubstitutionClosed : SubstitutionClosedHO explicitSharingPolicy
  treeContextClosed : ContextClosedHO treePolicy
  sharedContextClosed : ContextClosedHO sharedPolicy
  explicitContextClosed : ContextClosedHO explicitSharingPolicy
  betaCompatibleContextClosed : ContextClosedHO betaCompatiblePolicy

/-- Canonical theorem-visible status split for the explicit M2 policy classes. -/
def policySubfamilyStatus : PolicySubfamilyStatus where
  treeSubfamily := treePolicy_is_treeHO
  sharedSubfamily := sharedPolicy_is_sharedHO
  explicitSharingSubfamily := explicitSharingPolicy_is_explicitSharingHO
  sharedSharingAware := Or.inl sharedPolicy_is_sharedHO
  explicitSharingAware := Or.inr explicitSharingPolicy_is_explicitSharingHO
  treeBetaFree := treePolicy_is_betaFree
  sharedBetaFree := sharedPolicy_is_betaFree
  explicitBetaFree := explicitSharingPolicy_is_betaFree
  betaCompatibleStatus := betaCompatiblePolicy_is_betaCompatible
  binderStatus := betaCompatiblePolicy_has_binderStatus
  treeSubstitutionClosed := ⟨treePolicy_is_betaFree, treePolicy_is_binderFree⟩
  sharedSubstitutionClosed := ⟨sharedPolicy_is_betaFree, sharedPolicy_is_binderFree⟩
  explicitSubstitutionClosed :=
    ⟨explicitSharingPolicy_is_betaFree, explicitSharingPolicy_is_binderFree⟩
  treeContextClosed := Or.inl treePolicy_is_binderFree
  sharedContextClosed := Or.inl sharedPolicy_is_binderFree
  explicitContextClosed := Or.inl explicitSharingPolicy_is_binderFree
  betaCompatibleContextClosed := Or.inr betaCompatiblePolicy_has_binderStatus

/-- The old higher-order boundary counter transports into the explicit syntax on the embedded
old M2 carrier. -/
theorem boundary_policy_counter_embed
    (policy : OperatorKO7.HigherOrderSharingBoundary.SharingPolicy) :
    ∀ t : OperatorKO7.HigherOrderSharingBoundary.HOTerm,
      PolicyCounter (policyOfBoundary policy) (embedBoundaryHOTerm t) =
        OperatorKO7.HigherOrderSharingBoundary.HOPolicyCounter policy t
  | .base => by
      cases policy <;> rfl
  | .succ t => by
      cases policy <;>
        simp [embedBoundaryHOTerm, PolicyCounter,
          OperatorKO7.HigherOrderSharingBoundary.HOPolicyCounter,
          boundary_policy_counter_embed]
  | .app f a => by
      cases policy <;>
        simp [embedBoundaryHOTerm, PolicyCounter,
          OperatorKO7.HigherOrderSharingBoundary.HOPolicyCounter,
          boundary_policy_counter_embed]
  | .recur b s n => by
      cases policy <;>
        simp [embedBoundaryHOTerm, PolicyCounter,
          OperatorKO7.HigherOrderSharingBoundary.HOPolicyCounter,
          boundary_policy_counter_embed]

/-- The sharing-aware surrogate counter transports into the explicit-sharing syntax. -/
theorem explicit_policy_counter_embedSharedTerm :
    ∀ t : SharedTerm,
      PolicyCounter explicitSharingPolicy (embedSharedTerm t) = sharedCounter t
  | .base => rfl
  | .succ t => by
      simp [embedSharedTerm, PolicyCounter, explicit_policy_counter_embedSharedTerm]
  | .shareApp s r => by
      simp [embedSharedTerm, PolicyCounter, explicit_policy_counter_embedSharedTerm]
  | .recur b s n => by
      simp [embedSharedTerm, PolicyCounter, explicit_policy_counter_embedSharedTerm]

/-- The old M2 duplicating step embeds into the explicit higher-order rewriting syntax. -/
theorem boundary_step_embeds
    {policy : OperatorKO7.HigherOrderSharingBoundary.SharingPolicy}
    {a b : OperatorKO7.HigherOrderSharingBoundary.HOTerm}
    (h : OperatorKO7.HigherOrderSharingBoundary.HODupStep policy a b) :
    RewriteStep (policyOfBoundary policy)
      (embedBoundaryHOTerm a)
      (embedBoundaryHOTerm b) := by
  cases h with
  | rec_succ b s n =>
      cases policy with
      | tree =>
          simpa [policyOfBoundary, embedBoundaryHOTerm] using
            RewriteStep.rec_succ_tree treePolicy rfl
              (embedBoundaryHOTerm b) (embedBoundaryHOTerm s) (embedBoundaryHOTerm n)
      | shared =>
          simpa [policyOfBoundary, embedBoundaryHOTerm] using
            RewriteStep.rec_succ_shared sharedPolicy rfl
              (embedBoundaryHOTerm b) (embedBoundaryHOTerm s) (embedBoundaryHOTerm n)

/-- The old sharing-aware surrogate step embeds into the explicit-sharing branch. -/
theorem shared_step_embeds_explicit
    {a b : SharedTerm} (h : SharedStep a b) :
    RewriteStep explicitSharingPolicy (embedSharedTerm a) (embedSharedTerm b) := by
  cases h with
  | rec_succ b s n =>
      simpa [embedSharedTerm] using
        RewriteStep.rec_succ_explicit explicitSharingPolicy rfl
          (embedSharedTerm b) (embedSharedTerm s) (embedSharedTerm n)

/-- The shared-surrogate policy counter orients the policy-tagged shared branch. -/
theorem shared_policy_counter_orients_step :
    PolicyOrientsStep sharedPolicy := by
  intro a b h
  cases h with
  | rec_succ_tree htree _ _ _ =>
      cases htree
  | rec_succ_shared _ b s n =>
      simp [PolicyCounter, sharedPolicy]
  | rec_succ_explicit hexplicit _ _ _ =>
      cases hexplicit
  | beta hbeta _ _ _ =>
      cases hbeta

/-- The explicit-sharing policy counter orients the explicit-sharing branch. -/
theorem explicit_sharing_counter_orients_step :
    PolicyOrientsStep explicitSharingPolicy := by
  intro a b h
  cases h with
  | rec_succ_tree htree _ _ _ =>
      cases htree
  | rec_succ_shared hshared _ _ _ =>
      cases hshared
  | rec_succ_explicit _ b s n =>
      simp [PolicyCounter, explicitSharingPolicy]
  | beta hbeta _ _ _ =>
      cases hbeta

/-- The explicit-sharing embedding preserves the original sharing-aware orienting counter. -/
theorem explicit_policy_counter_orients_embedded_step
    {a b : SharedTerm} (h : SharedStep a b) :
    PolicyCounter explicitSharingPolicy (embedSharedTerm b) <
      PolicyCounter explicitSharingPolicy (embedSharedTerm a) := by
  rw [explicit_policy_counter_embedSharedTerm, explicit_policy_counter_embedSharedTerm]
  exact sharedCounter_orients_step h

/-- Transport the old M2 catalog's fragment membership into the explicit syntax. -/
theorem catalog_transports_restricted_fragment
    (hcat : HigherOrderSharingBoundaryCatalog) :
    ∀ t : SharedTerm,
      ClosedFragment
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm t)) := by
  intro t
  exact
    embedBoundaryHOTerm_closed
      ((hcat.noSharingBoundary).restrictedFragmentCarriesFirstOrderShape t)

/-- Transport the old shared-surrogate M2 counterexample into the explicit syntax on the
embedded old higher-order carrier. -/
theorem catalog_transports_shared_counterexample
    (hcat : HigherOrderSharingBoundaryCatalog)
    (b s n : SharedTerm) :
    PolicyCounter sharedPolicy
      (embedBoundaryHOTerm
        (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
          (SharedTerm.shareApp s (SharedTerm.recur b s n)))) <
    PolicyCounter sharedPolicy
      (embedBoundaryHOTerm
        (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
          (SharedTerm.recur b s (SharedTerm.succ n)))) := by
  have hleft :
      PolicyCounter sharedPolicy
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.shareApp s (SharedTerm.recur b s n)))) =
        OperatorKO7.HigherOrderSharingBoundary.HOPolicyCounter .shared
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.shareApp s (SharedTerm.recur b s n))) := by
    simpa [policyOfBoundary, sharedPolicy] using
      (boundary_policy_counter_embed (policy := .shared)
        (t := OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
          (SharedTerm.shareApp s (SharedTerm.recur b s n))))
  have hright :
      PolicyCounter sharedPolicy
        (embedBoundaryHOTerm
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.recur b s (SharedTerm.succ n)))) =
        OperatorKO7.HigherOrderSharingBoundary.HOPolicyCounter .shared
          (OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
            (SharedTerm.recur b s (SharedTerm.succ n))) := by
    simpa [policyOfBoundary, sharedPolicy] using
      (boundary_policy_counter_embed (policy := .shared)
        (t := OperatorKO7.HigherOrderSharingBoundary.embedSharedTerm
          (SharedTerm.recur b s (SharedTerm.succ n))))
  rw [hleft, hright]
  exact hcat.sharedCounterexample b s n

/-- The old theorem-visible no-sharing boundary status is still part of the explicit syntax
layer through transport. -/
theorem catalog_transports_no_sharing_boundary
    (hcat : HigherOrderSharingBoundaryCatalog) :
    NoSharingBoundaryStatus :=
  hcat.noSharingBoundary

/-- Direct explicit-sharing version of the old sharing-aware counterexample. -/
theorem explicit_sharing_fragment_recovers_counterexample
    (b s n : SharedTerm) :
    PolicyCounter explicitSharingPolicy
      (embedSharedTerm (SharedTerm.shareApp s (SharedTerm.recur b s n))) <
    PolicyCounter explicitSharingPolicy
      (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n))) := by
  rw [explicit_policy_counter_embedSharedTerm, explicit_policy_counter_embedSharedTerm]
  exact sharing_breaks_tree_barrier b s n

/-- Strongest honest theorem landed in this sprint: the shared-surrogate policy still blocks
an unqualified full higher-order rewriting lift. -/
theorem shared_policy_blocks_unqualified_higher_order_rewriting_lift :
    ¬ UnqualifiedHigherOrderRewritingLiftClaim := by
  intro h
  exact h sharedPolicy shared_policy_counter_orients_step

end OperatorKO7.HigherOrderRewritingBoundary
