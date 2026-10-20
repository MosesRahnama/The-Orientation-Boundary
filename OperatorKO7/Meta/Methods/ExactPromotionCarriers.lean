import OperatorKO7.Meta.ConfessionMethod_Unification
import OperatorKO7.Meta.Methods.DependencyPairTypedRows
import OperatorKO7.Meta.Methods.SubstrateChangeRows
import OperatorKO7.Meta.SafeStepCtx_Complexity_Cichon

set_option autoImplicit false

/-!
# Exact carriers for evidence-ledger promotions

This module is deliberately narrower than the exploratory `Meta/Methods/*Rows`
modules.  A row is represented here only when the repository already contains
an actual KO7-specialized object implementing the named method.

The carrier types below are closed singleton inductives.  They contain no proof
fields and no generic `proof : Prop` constructor. Their semantics are computed
into the existing method objects, and certification is derived in this module
from those semantics. Consequently a theorem-backed evidence constructor cannot be
forged by supplying a proof of an unrelated proposition.

The first exact cohort consists of:

* constructorwise argument filtering;
* the neutral identity dependency-pair processor;
* the concrete single-call size-change graph;
* the concrete Cichon bound on the guarded contextual relation;
* the merge-commutativity equational quotient;
* the explicit shared-node substrate.

Every theorem in this file is KO7-specific.  No generic soundness theorem for
all argument filters, all SCT systems, all quotients, or all sharing formalisms
is asserted here.
-/

namespace OperatorKO7.Methods.ExactPromotionCarriers

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Methods.DependencyPairTypedRows
open OperatorKO7.Methods.SubstrateChangeRows

/-! ## Argument filtering -/

/-- The exact KO7 argument-filtering method admitted by this evidence layer. -/
inductive KO7ArgumentFilteringMethod where
  | counterOnly
  deriving DecidableEq, Repr

namespace KO7ArgumentFilteringMethod

/-- The actual constructorwise filter computed by the method. -/
def constructorFilter : KO7ArgumentFilteringMethod → ConstructorwiseArgumentFilter
  | .counterOnly => counterOnlyConstructorFilter

/-- The selected recursor coordinate. -/
def witness : KO7ArgumentFilteringMethod → ArgumentFilteringWitness
  | .counterOnly => schemaArgumentFilteringWitness

/-- The actual rank computed by the filter. -/
def rank : KO7ArgumentFilteringMethod → Trace → Nat
  | .counterOnly => argumentFilteringRankFn

end KO7ArgumentFilteringMethod

/-- Exact certification predicate for the KO7 counter-only argument filter.
The method-specific filter is load-bearing: the second conjunct identifies the
recursive evaluator with the method's constructorwise filter, and the final
conjunct proves the filtered duplicating call is a unary predecessor step. -/
def ArgumentFilteringCertifies (M : KO7ArgumentFilteringMethod) : Prop :=
  M.witness.keepRecurCoordinate = ⟨2, by decide⟩
    ∧ argumentFilterTrace = applyConstructorwiseFilter M.constructorFilter
    ∧ M.rank = dpProjection
    ∧ (∀ s n : Trace, argumentFilterTrace (app s n) = argumentFilterTrace n)
    ∧ (∀ b s n : Trace, ∀ m : FilteredCounterTerm,
        argumentFilterTrace n = some m →
          argumentFilterTrace (recΔ b s (delta n)) =
              some (FilteredCounterTerm.succ m)
          ∧ argumentFilterTrace (app s (recΔ b s n)) = some m
          ∧ FilteredCounterStep (FilteredCounterTerm.succ m) m)

/-- Every inhabitant of the closed KO7 argument-filtering carrier is the
counter-only filter and satisfies its exact route certificate. -/
theorem argumentFiltering_certifies :
    ∀ M : KO7ArgumentFilteringMethod, ArgumentFilteringCertifies M := by
  intro M
  cases M with
  | counterOnly =>
      refine ⟨schemaArgumentFilteringWitness.keepRecurCoordinate_is_counter,
        ?_, argumentFilteringRankFn_eq_dpProjection, ?_, ?_⟩
      · exact argumentFilterTrace_eq_applyConstructorwiseFilter
      · intro s n
        rfl
      · intro b s n m hm
        refine ⟨?_, ?_, FilteredCounterStep.succ_step m⟩
        · simp [argumentFilterTrace, hm]
        · simpa [argumentFilterTrace] using hm

/-- Exact row proposition used by the evidence ledger. -/
abbrev ArgumentFilteringExactRowClaim : Prop :=
  ∀ M : KO7ArgumentFilteringMethod, ArgumentFilteringCertifies M

/-! ## Neutral dependency-pair processor -/

/-- The exact neutral processor implemented in the KO7 stack. -/
inductive KO7NeutralDPProcessorMethod where
  | identity
  deriving DecidableEq, Repr

namespace KO7NeutralDPProcessorMethod

/-- The processor relation computed by the method. -/
def processor : KO7NeutralDPProcessorMethod → ConcreteDPProcessor
  | .identity => identityDPProcessor

end KO7NeutralDPProcessorMethod

/-- Exact certification predicate for the identity DP processor. -/
def NeutralDPProcessorCertifies (M : KO7NeutralDPProcessorMethod) : Prop :=
  IsNeutralDPProcessor M.processor
    ∧ WellFounded (fun t s : Trace => M.processor.output s t)
    ∧ (WellFounded (fun t s : Trace => M.processor.output s t) ↔
        WellFounded DPPairRev)

/-- The closed neutral-processor carrier is extensionally the original DP
problem and preserves the already-proved reverse well-foundedness. -/
theorem neutralDPProcessor_certifies :
    ∀ M : KO7NeutralDPProcessorMethod, NeutralDPProcessorCertifies M := by
  intro M
  cases M with
  | identity =>
      refine ⟨identityDPProcessor_neutral, ?_, ?_⟩
      · simpa [KO7NeutralDPProcessorMethod.processor, identityDPProcessor] using wf_DPPairRev
      · rfl

/-- Exact row proposition used by the evidence ledger. -/
abbrev NeutralDPProcessorExactRowClaim : Prop :=
  ∀ M : KO7NeutralDPProcessorMethod, NeutralDPProcessorCertifies M

/-! ## Size-change termination -/

/-- The exact single-call size-change method instantiated by the KO7 recursor. -/
inductive KO7SizeChangeMethod where
  | schemaSingleCall
  deriving DecidableEq, Repr

namespace KO7SizeChangeMethod

/-- The concrete size-change graph. -/
def graph : KO7SizeChangeMethod → SizeChangeGraph 3
  | .schemaSingleCall => schemaRecCallGraph

/-- The rank extracted from the concrete size-change construction. -/
def rank : KO7SizeChangeMethod → StepDuplicating.StepDuplicatingSchema.ProjectionRank ko7Schema
  | .schemaSingleCall => sctDerivedRank

end KO7SizeChangeMethod

/-- Exact KO7 single-call SCT certificate.  The graph itself is load-bearing:
all three diagonal facts, uniqueness of the strict diagonal, and a
self-composition fact are stated on `M.graph`.  The extracted rank is then tied
to the canonical DP projection and shown to orient the duplicating call. -/
def SizeChangeCertifies (M : KO7SizeChangeMethod) : Prop :=
  M.graph.arcs ⟨2, by decide⟩ ⟨2, by decide⟩ = SCArc.strictDecrease
    ∧ M.graph.arcs ⟨0, by decide⟩ ⟨0, by decide⟩ = SCArc.nonIncreasing
    ∧ M.graph.arcs ⟨1, by decide⟩ ⟨1, by decide⟩ = SCArc.nonIncreasing
    ∧ (∀ i : Fin 3,
        M.graph.arcs i i = SCArc.strictDecrease → i = ⟨2, by decide⟩)
    ∧ (SizeChangeGraph.comp3 M.graph M.graph).arcs
        ⟨2, by decide⟩ ⟨2, by decide⟩ = SCArc.strictDecrease
    ∧ M.rank.rank = dpProjection
    ∧ (∀ b s n : Trace,
        M.rank.rank (ko7Schema.wrap s (ko7Schema.recur b s n)) <
          M.rank.rank (ko7Schema.recur b s (ko7Schema.succ n)))

/-- Every inhabitant of the closed SCT carrier is the concrete KO7 graph and
satisfies the exact local single-call certificate. -/
theorem sizeChange_certifies :
    ∀ M : KO7SizeChangeMethod, SizeChangeCertifies M := by
  intro M
  cases M with
  | schemaSingleCall =>
      refine ⟨schemaRecCallGraph_counter_descent,
        schemaRecCallGraph_base_nonincreasing,
        schemaRecCallGraph_step_nonincreasing,
        schema_sct_unique_descent,
        schemaRecCallGraph_comp3_counter_descent,
        ?_, sctDerivedRank_orients_dup_step⟩
      simpa [KO7SizeChangeMethod.rank, sctDerivedRank] using sctRankFn_eq_dpProjection

/-- Exact row proposition used by the evidence ledger. -/
abbrev SizeChangeExactRowClaim : Prop :=
  ∀ M : KO7SizeChangeMethod, SizeChangeCertifies M

/-! ## Cichon slow-growing bound -/

/-- The concrete guarded-contextual Cichon construction used by KO7. -/
inductive KO7CichonSlowGrowingMethod where
  | guardedContextual
  deriving DecidableEq, Repr

namespace KO7CichonSlowGrowingMethod

/-- Ordinal notation assigned to a starting trace. -/
def note : KO7CichonSlowGrowingMethod → Trace → NONote
  | .guardedContextual => MetaSN_KO7.ctxExpNote

/-- Cichon bound assigned to a starting trace. -/
def bound : KO7CichonSlowGrowingMethod → Trace → Nat
  | .guardedContextual => MetaSN_KO7.ctxExpCichonBound

end KO7CichonSlowGrowingMethod

/-- Exact certification of the concrete Cichon construction on the guarded
contextual relation. -/
def CichonSlowGrowingCertifies (M : KO7CichonSlowGrowingMethod) : Prop :=
  (∀ t : Trace, NONote.repr (M.note t) < Ordinal.omega0)
    ∧ (∀ t : Trace,
        MetaSN_KO7.contextualExpBound (MetaSN_KO7.termSize t) ≤ M.bound t)
    ∧ (∀ (t u : Trace) (n : Nat), MetaSN_KO7.SafeStepCtxPow n t u →
        n + 1 ≤ M.bound t)

/-- The closed Cichon carrier is exactly the existing KO7 contextual
construction and inherits its three proved bounds. -/
theorem cichonSlowGrowing_certifies :
    ∀ M : KO7CichonSlowGrowingMethod, CichonSlowGrowingCertifies M := by
  intro M
  cases M with
  | guardedContextual =>
      exact ⟨MetaSN_KO7.ctxExpNote_lt_omega,
        MetaSN_KO7.contextualExpBound_le_ctxExpCichonBound,
        MetaSN_KO7.safeStepCtx_length_le_ctxExpCichonBound⟩

/-- Exact row proposition used by the evidence ledger. -/
abbrev CichonSlowGrowingExactRowClaim : Prop :=
  ∀ M : KO7CichonSlowGrowingMethod, CichonSlowGrowingCertifies M

/-! ## Equational quotient -/

/-- The concrete equational quotient considered by the KO7 row. -/
inductive KO7EquationalQuotientMethod where
  | mergeCommutativity
  deriving DecidableEq, Repr

namespace KO7EquationalQuotientMethod

/-- The equation relation added by the quotient. -/
def equation : KO7EquationalQuotientMethod → Trace → Trace → Prop
  | .mergeCommutativity => MergeCommutativityEquation

end KO7EquationalQuotientMethod

/-- Exact nonconservativity certificate: the method's own equation identifies
two distinct root-normal forms of the source kernel. -/
def EquationalQuotientCertifies (M : KO7EquationalQuotientMethod) : Prop :=
  mergeLeft ≠ mergeRight
    ∧ RootNormal mergeLeft
    ∧ RootNormal mergeRight
    ∧ M.equation mergeLeft mergeRight

/-- Every inhabitant of the closed quotient carrier is merge commutativity and
has the concrete normal-form nonconservativity witness. -/
theorem equationalQuotient_certifies :
    ∀ M : KO7EquationalQuotientMethod, EquationalQuotientCertifies M := by
  intro M
  cases M with
  | mergeCommutativity =>
      exact ⟨merge_terms_distinct, mergeLeft_rootNormal, mergeRight_rootNormal,
        merge_commutativity_identifies_witness⟩

/-- Exact row proposition used by the evidence ledger. -/
abbrev EquationalQuotientExactRowClaim : Prop :=
  ∀ M : KO7EquationalQuotientMethod, EquationalQuotientCertifies M

/-! ## Sharing -/

/-- The concrete shared-node substrate used by the KO7 row. -/
inductive KO7SharingMethod where
  | explicitSharedNode
  deriving DecidableEq, Repr

namespace KO7SharingMethod

/-- Read-back from the actual shared carrier to source terms. -/
def readBack : KO7SharingMethod → SharedTerm → Trace
  | .explicitSharedNode => unshare

/-- Size on the actual shared carrier. -/
def size : KO7SharingMethod → SharedTerm → Nat
  | .explicitSharedNode => sharedSize

end KO7SharingMethod

/-- Exact sharing certificate.  The read-back and shared-size functions are the
method semantics themselves; the source-side copy-mass failure is included to
make the substrate change operationally visible rather than merely nominal. -/
def SharingCertifies (M : KO7SharingMethod) : Prop :=
  ¬ Function.Injective M.readBack
    ∧ (∀ x : SharedTerm,
        M.size (SharedTerm.shared x) < M.size (SharedTerm.node x x))
    ∧ ¬ (∃ μ : Trace → Nat, ∀ x : SharedTerm, M.size x = μ (M.readBack x))
    ∧ ¬ (∀ {a b : Trace}, MetaSN_KO7.SafeStep a b →
        MetaSN_KO7.copyMass b ≤ MetaSN_KO7.copyMass a)

/-- Every inhabitant of the closed sharing carrier is the explicit shared-node
representation and satisfies the exact substrate-change certificate. -/
theorem sharing_certifies : ∀ M : KO7SharingMethod, SharingCertifies M := by
  intro M
  cases M with
  | explicitSharedNode =>
      exact ⟨unshare_not_injective, sharedSize_shared_lt_node,
        sharedSize_not_factors_through_unshare,
        MetaSN_KO7.not_copyMass_mono_safe⟩

/-- Exact row proposition used by the evidence ledger. -/
abbrev SharingExactRowClaim : Prop :=
  ∀ M : KO7SharingMethod, SharingCertifies M

/-! ## Exact convergence on the confession core -/

/-- The two newly promoted projection methods compute exactly the same rank as
the canonical DP confession core.  This is equality of functions, not a route
analogy. -/
theorem argumentFiltering_sizeChange_rank_eq_dpProjection :
    KO7ArgumentFilteringMethod.rank .counterOnly = dpProjection
      ∧ (KO7SizeChangeMethod.rank .schemaSingleCall).rank = dpProjection := by
  exact ⟨argumentFilteringRankFn_eq_dpProjection, by
    simpa [KO7SizeChangeMethod.rank, sctDerivedRank] using sctRankFn_eq_dpProjection⟩

/-- The existing confession-method unification theorem identifies the full
argument-filtering and SCT projection-rank structures with the common DP core. -/
theorem argumentFiltering_sizeChange_share_confession_core :
    argumentFilteringConfession.toProjectionRank = confessionProjectionCore
      ∧ sctConfession.toProjectionRank = confessionProjectionCore :=
  ⟨argumentFiltering_route_eq_confession_core, sct_route_eq_confession_core⟩

end OperatorKO7.Methods.ExactPromotionCarriers
