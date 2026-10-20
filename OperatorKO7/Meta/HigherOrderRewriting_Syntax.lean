import OperatorKO7.Meta.HigherOrderSharingBoundary

/-!
# Higher-Order Rewriting Syntax

This module defines an untyped term syntax, three policy-tag enumerations, a replacement operation,
one-hole contexts, and two syntax embeddings. It defines no rewrite relation. The policy fields are
metadata tags rather than proofs of beta compatibility or sharing semantics. `substitute` respects a
matching binder by stopping under it but performs no alpha-renaming, so replacement variables may be
captured by other binders.
-/

namespace OperatorKO7.HigherOrderRewritingSyntax

open OperatorKO7.SharingBarrierLift

/-- Sharing discipline for the explicit higher-order rewriting syntax. -/
inductive SharingMode
  | tree
  | shared
  | explicitSharing
  deriving DecidableEq, Repr

/-- Two metadata tags for beta status. -/
inductive BetaMode
  | betaFree
  | betaCompatible
  deriving DecidableEq, Repr

/-- Binder status tracked at the policy level. -/
inductive BinderMode
  | binderFree
  | binderAware
  deriving DecidableEq, Repr

/-- Product of sharing, beta, and binder metadata tags. -/
structure PolicyClass where
  sharing : SharingMode
  beta : BetaMode
  binder : BinderMode
  deriving DecidableEq, Repr

/-- Tree-only higher-order rewriting subfamily. -/
abbrev TreeHO (policy : PolicyClass) : Prop :=
  policy.sharing = .tree

/-- Shared-surrogate higher-order rewriting subfamily. -/
abbrev SharedHO (policy : PolicyClass) : Prop :=
  policy.sharing = .shared

/-- Explicit-sharing higher-order rewriting subfamily. -/
abbrev ExplicitSharingHO (policy : PolicyClass) : Prop :=
  policy.sharing = .explicitSharing

/-- Beta-free higher-order rewriting status. -/
abbrev BetaFreeHO (policy : PolicyClass) : Prop :=
  policy.beta = .betaFree

/-- Predicate that the beta metadata field equals `betaCompatible`. -/
abbrev BetaCompatibleStatus (policy : PolicyClass) : Prop :=
  policy.beta = .betaCompatible

/-- Binder-free higher-order rewriting status. -/
abbrev BinderFreeStatus (policy : PolicyClass) : Prop :=
  policy.binder = .binderFree

/-- Binder-aware higher-order rewriting status. -/
abbrev BinderStatus (policy : PolicyClass) : Prop :=
  policy.binder = .binderAware

/-- Canonical tree/no-sharing policy. -/
def treePolicy : PolicyClass :=
  ⟨.tree, .betaFree, .binderFree⟩

/-- Canonical shared-surrogate policy. -/
def sharedPolicy : PolicyClass :=
  ⟨.shared, .betaFree, .binderFree⟩

/-- Canonical explicit-sharing policy. -/
def explicitSharingPolicy : PolicyClass :=
  ⟨.explicitSharing, .betaFree, .binderFree⟩

/-- Fixture carrying the `betaCompatible` and `binderAware` tags. -/
def betaCompatiblePolicy : PolicyClass :=
  ⟨.tree, .betaCompatible, .binderAware⟩

/-- Map the two boundary sharing-policy constructors to policy-tag fixtures. -/
def policyOfBoundary : OperatorKO7.HigherOrderSharingBoundary.SharingPolicy → PolicyClass
  | .tree => treePolicy
  | .shared => sharedPolicy

@[simp] theorem treePolicy_is_treeHO : TreeHO treePolicy := rfl

@[simp] theorem sharedPolicy_is_sharedHO : SharedHO sharedPolicy := rfl

@[simp] theorem explicitSharingPolicy_is_explicitSharingHO :
    ExplicitSharingHO explicitSharingPolicy := rfl

@[simp] theorem treePolicy_is_betaFree : BetaFreeHO treePolicy := rfl

@[simp] theorem sharedPolicy_is_betaFree : BetaFreeHO sharedPolicy := rfl

@[simp] theorem explicitSharingPolicy_is_betaFree : BetaFreeHO explicitSharingPolicy := rfl

@[simp] theorem betaCompatiblePolicy_is_betaCompatible :
    BetaCompatibleStatus betaCompatiblePolicy := rfl

@[simp] theorem treePolicy_is_binderFree : BinderFreeStatus treePolicy := rfl

@[simp] theorem sharedPolicy_is_binderFree : BinderFreeStatus sharedPolicy := rfl

@[simp] theorem explicitSharingPolicy_is_binderFree :
    BinderFreeStatus explicitSharingPolicy := rfl

@[simp] theorem betaCompatiblePolicy_has_binderStatus : BinderStatus betaCompatiblePolicy := rfl

@[simp] theorem policyOfBoundary_tree_is_treeHO : TreeHO (policyOfBoundary .tree) := rfl

@[simp] theorem policyOfBoundary_shared_is_sharedHO : SharedHO (policyOfBoundary .shared) := rfl

/-- Untyped terms with numeric variables and binders, application, recursor structure, and an
explicit sharing node. -/
inductive HOTerm : Type
  | var : Nat → HOTerm
  | atom : HOTerm
  | succ : HOTerm → HOTerm
  | app : HOTerm → HOTerm → HOTerm
  | lam : Nat → HOTerm → HOTerm
  | recur : HOTerm → HOTerm → HOTerm → HOTerm
  | share : HOTerm → HOTerm → HOTerm
  deriving DecidableEq, Repr

open HOTerm

/-- Inductive fragment omitting `var` and `lam` constructors. -/
inductive ClosedFragment : HOTerm → Prop
  | atom : ClosedFragment atom
  | succ {t : HOTerm} : ClosedFragment t → ClosedFragment (succ t)
  | app {f a : HOTerm} : ClosedFragment f → ClosedFragment a → ClosedFragment (app f a)
  | recur {b s n : HOTerm} :
      ClosedFragment b → ClosedFragment s → ClosedFragment n →
      ClosedFragment (recur b s n)
  | share {s r : HOTerm} :
      ClosedFragment s → ClosedFragment r → ClosedFragment (share s r)

/-- Binder-shadowing replacement without alpha-renaming. A matching binder stops recursion; other
binders retain their names, so free variables of `replacement` may become captured. -/
@[simp] def substitute (name : Nat) (replacement : HOTerm) : HOTerm → HOTerm
  | var idx => if idx = name then replacement else var idx
  | atom => atom
  | succ t => succ (substitute name replacement t)
  | app f a => app (substitute name replacement f) (substitute name replacement a)
  | lam idx body =>
      if idx = name then
        lam idx body
      else
        lam idx (substitute name replacement body)
  | recur b s n =>
      recur (substitute name replacement b)
        (substitute name replacement s)
        (substitute name replacement n)
  | share s r =>
      share (substitute name replacement s) (substitute name replacement r)

/-- One-hole contexts for the explicit higher-order rewriting syntax. -/
inductive Context : Type
  | hole : Context
  | succ : Context → Context
  | appLeft : Context → HOTerm → Context
  | appRight : HOTerm → Context → Context
  | lam : Nat → Context → Context
  | recurBase : Context → HOTerm → HOTerm → Context
  | recurStep : HOTerm → Context → HOTerm → Context
  | recurArg : HOTerm → HOTerm → Context → Context
  | shareLeft : Context → HOTerm → Context
  | shareRight : HOTerm → Context → Context
  deriving DecidableEq, Repr

namespace Context

/-- Plug a term into a one-hole higher-order rewriting context. -/
@[simp] def plug : Context → HOTerm → HOTerm
  | .hole, t => t
  | .succ c, t => HOTerm.succ (plug c t)
  | .appLeft c arg, t => HOTerm.app (plug c t) arg
  | .appRight fn c, t => HOTerm.app fn (plug c t)
  | .lam idx c, t => HOTerm.lam idx (plug c t)
  | .recurBase c s n, t => HOTerm.recur (plug c t) s n
  | .recurStep b c n, t => HOTerm.recur b (plug c t) n
  | .recurArg b s c, t => HOTerm.recur b s (plug c t)
  | .shareLeft c r, t => HOTerm.share (plug c t) r
  | .shareRight s c, t => HOTerm.share s (plug c t)

end Context

/-- Embedding of `HigherOrderSharingBoundary.HOTerm` into this syntax. -/
@[simp] def embedBoundaryHOTerm : OperatorKO7.HigherOrderSharingBoundary.HOTerm → HOTerm
  | .base => atom
  | .succ t => succ (embedBoundaryHOTerm t)
  | .app f a => app (embedBoundaryHOTerm f) (embedBoundaryHOTerm a)
  | .recur b s n => recur (embedBoundaryHOTerm b) (embedBoundaryHOTerm s) (embedBoundaryHOTerm n)

/-- Map a source `HOClosedFragment` derivation to `ClosedFragment`. -/
theorem embedBoundaryHOTerm_closed :
    ∀ {t : OperatorKO7.HigherOrderSharingBoundary.HOTerm},
      OperatorKO7.HigherOrderSharingBoundary.HOClosedFragment t →
        ClosedFragment (embedBoundaryHOTerm t)
  | _, .base => ClosedFragment.atom
  | _, .succ ht => ClosedFragment.succ (embedBoundaryHOTerm_closed ht)
  | _, .app hf ha =>
      ClosedFragment.app (embedBoundaryHOTerm_closed hf) (embedBoundaryHOTerm_closed ha)
  | _, .recur hb hs hn =>
      ClosedFragment.recur
        (embedBoundaryHOTerm_closed hb)
        (embedBoundaryHOTerm_closed hs)
        (embedBoundaryHOTerm_closed hn)

/-- Embedding of the sharing-aware surrogate into the explicit higher-order rewriting syntax. -/
@[simp] def embedSharedTerm : SharedTerm → HOTerm
  | .base => atom
  | .succ t => succ (embedSharedTerm t)
  | .shareApp s r => share (embedSharedTerm s) (embedSharedTerm r)
  | .recur b s n => recur (embedSharedTerm b) (embedSharedTerm s) (embedSharedTerm n)

/-- Every embedded sharing-aware term lies in the explicit closed fragment. -/
theorem embedSharedTerm_closed :
    ∀ t : SharedTerm, ClosedFragment (embedSharedTerm t)
  | .base => ClosedFragment.atom
  | .succ t => ClosedFragment.succ (embedSharedTerm_closed t)
  | .shareApp s r =>
      ClosedFragment.share (embedSharedTerm_closed s) (embedSharedTerm_closed r)
  | .recur b s n =>
      ClosedFragment.recur
        (embedSharedTerm_closed b)
        (embedSharedTerm_closed s)
        (embedSharedTerm_closed n)

/-- The embedded shared recursor source belongs to `ClosedFragment`. -/
theorem shared_recursor_shape_closed_fragment
    (b s n : SharedTerm) :
    ClosedFragment (embedSharedTerm (SharedTerm.recur b s (SharedTerm.succ n))) :=
  embedSharedTerm_closed _

end OperatorKO7.HigherOrderRewritingSyntax
