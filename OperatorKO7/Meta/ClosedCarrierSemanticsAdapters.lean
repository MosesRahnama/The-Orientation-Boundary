import OperatorKO7.Meta.EscapeRouteRefined
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.RDRSNotesReconciliationAddendum
import Mathlib.Order.WellFounded

set_option autoImplicit false

/-!
# Closed-carrier semantics adapters for the KO7 root-step relation

An adapter in this module is **sound by construction**. `KO7StepAdapter` names
the exact source relation (`OperatorKO7.Step`, root single step on `Trace`),
and every value of the structure carries exactly three load-bearing fields:

* the exact target relation it orients into,
* well-foundedness of the reversed target relation, and
* the orientation/decrease theorem from source to target.

Source termination is **not** a field. It is the theorem
`KO7StepAdapter.sourceWellFounded`, derived from the two fields above. A caller
using the raw `KO7StepAdapter.mk` therefore cannot assert strong normalization
of `Step` without supplying the well-founded target and the orientation proof
that actually entail it; there is no constructor bypass.

Weak monotonicity, a tag, or membership in a carrier is **not** an adapter here
and cannot inhabit the structure.

## Dependency-pair adapters

A DP adapter would additionally require complete extraction over every source
rule, processor (SCC) soundness, and artifact identity where an external
certificate is cited. The Lean surface currently provides
`MetaDependencyPairs.DPPair`, which is the manually stated `rec_succ` pair only
(`rec_succ_extracts_dependency_pair`), and
`Meta/LCELTypedDPInstance.lean`'s fixed-system license, whose transport routes
the pair certificate through `natLt_wellFounded_of_DPPairRev` and then closes
source termination with the independent polynomial rank. That is not
dependency-pair processor soundness. The DP family therefore stays
NO-TRANSPORT here with the missing structure named explicitly.

## WP-3 notes carriers

The four WP-3 notes carriers are inhabited carrier-level incompatibilities.
Carrier incompatibility alone is not a real-method adapter, so all four stay
NO-TRANSPORT.

## Audit slots (Lean Development Bible W8 / R4)

```text
Relation:  OperatorKO7.Step (root single step on Trace) for every supported
           adapter.
Closure:   root. No contextual closure is claimed.
Strategy:  full rewriting.
Property:  SN of the reversed source relation.
Trust:     kernel-only.
Scope:     the seven named adapter families listed in `AdapterFamily`.
```
-/

namespace OperatorKO7.ClosedCarrierSemanticsAdapters

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-! ## 1. The sound adapter structure -/

/--
Proves: a sound closed-carrier adapter for the exact source relation
  `OperatorKO7.Step`. Every field is load-bearing: the target relation is
  named, its reverse is well-founded, every source step is oriented, and the
  source termination property is transported.
Does not prove: anything about contextual closure, `SafeStep`, or the
  reflexive-transitive closure.
Relation: `OperatorKO7.Step` (root single step).
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: adapters on the `Trace` carrier.
-/
structure KO7StepAdapter where
  /-- The exact target relation this adapter orients into. -/
  Target : Trace → Trace → Prop
  /-- Well-foundedness of the reversed target relation. -/
  targetWellFounded : WellFounded (fun a b : Trace => Target b a)
  /-- Orientation of every source root step by the target relation. -/
  orientsStep : ∀ a b : Trace, Step a b → Target a b

/--
Proves: sound transport. Strong normalization of the exact source relation
  `OperatorKO7.Step` is **derived** from the adapter's target
  well-foundedness and its orientation theorem.
Does not prove: contextual or reflexive-transitive strong normalization.
Relation: `OperatorKO7.Step` (root single step).
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: every `KO7StepAdapter`.

This is a theorem, not a structure field. There is no public constructor path
that asserts source well-foundedness independently of `targetWellFounded` and
`orientsStep`, so `KO7StepAdapter.mk` cannot bypass the transport argument.
-/
theorem KO7StepAdapter.sourceWellFounded (A : KO7StepAdapter) :
    WellFounded (fun a b : Trace => Step b a) := by
  have hsub :
      Subrelation (fun a b : Trace => Step b a) (fun a b : Trace => A.Target b a) := by
    intro x y hstep
    exact A.orientsStep y x hstep
  exact Subrelation.wf hsub A.targetWellFounded

/-- Canonical constructor. Every field is load-bearing: the target relation is
named, its reverse is well-founded, and every source step is oriented. Source
termination is not a field and cannot be supplied here. -/
def KO7StepAdapter.ofOrientation
    (Target : Trace → Trace → Prop)
    (targetWellFounded : WellFounded (fun a b : Trace => Target b a))
    (orientsStep : ∀ a b : Trace, Step a b → Target a b) : KO7StepAdapter where
  Target := Target
  targetWellFounded := targetWellFounded
  orientsStep := orientsStep

/-! ## 2. Concrete inhabited certified adapters -/

/-- Nonlinear polynomial interpretation adapter. Source relation `Step`, target
relation `fun a b => W b < W a`, decrease theorem
`PolyInterpretation.W_orients_step`, transport by inverse image of `Nat.lt`. -/
def polynomialInterpretationAdapter : KO7StepAdapter :=
  KO7StepAdapter.ofOrientation
    (fun a b : Trace => PolyInterpretation.W b < PolyInterpretation.W a)
    (InvImage.wf (f := PolyInterpretation.W) Nat.lt_wfRel.wf)
    (fun _ _ hstep => PolyInterpretation.W_orients_step hstep)

/-- KO7 MPO structural-order adapter. Source relation `Step`, target relation
`MetaMPO.MPO`, decrease theorem `MetaMPO.mpo_orients_step`, transport by the
ordinal interpretation behind `MetaMPO.wf_MPORev`. -/
def multisetPathOrderAdapter : KO7StepAdapter :=
  KO7StepAdapter.ofOrientation
    MetaMPO.MPO
    MetaMPO.wf_MPORev
    (fun _ _ hstep => MetaMPO.mpo_orients_step hstep)

/-- Both supported adapters name distinct target relations and both transport
to strong normalization of the exact same source relation. -/
theorem supported_adapters_transport_source_SN :
    polynomialInterpretationAdapter.Target =
        (fun a b : Trace => PolyInterpretation.W b < PolyInterpretation.W a) ∧
      multisetPathOrderAdapter.Target = MetaMPO.MPO ∧
      WellFounded (fun a b : Trace => Step b a) ∧
      WellFounded (fun a b : Trace => Step b a) :=
  ⟨rfl, rfl,
    polynomialInterpretationAdapter.sourceWellFounded,
    multisetPathOrderAdapter.sourceWellFounded⟩

/-! ## 3. Adapter families and their dispositions -/

/--
Proves: the closed catalog of adapter families considered by this module.
Does not prove: that any family is supported; see `AdapterDisposition`.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: seven families.
-/
inductive AdapterFamily where
  | polynomialInterpretation
  | multisetPathOrder
  | dependencyPairProcessor
  | signatureTransformation
  | probabilisticSubstrate
  | unionHierarchySubstrate
  | complexityOnly
  deriving DecidableEq, Repr

/--
Proves: the closed indexed record of the structure whose absence blocks an
  adapter family. Each constructor names the concrete missing object.
Does not prove: that the missing object cannot be built later.
Relation: closed indexed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the five NO-TRANSPORT families.
-/
inductive MissingAdapterStructure : AdapterFamily → Prop
  /-- Absent: complete all-rule dependency-pair extraction together with SCC /
  processor soundness transporting the pair certificate to source termination.
  The available `DPPair` covers the `rec_succ` rule only, and the available
  fixed-system license closes source termination with the independent
  polynomial rank. -/
  | noCompleteExtractionAndProcessorSoundness :
      MissingAdapterStructure .dependencyPairProcessor
  /-- Absent: a well-founded target relation on `Trace` plus a source
  orientation theorem. The signature-transformation carrier records a
  non-identity signature change only. -/
  | signatureCarrierIncompatibilityOnly :
      MissingAdapterStructure .signatureTransformation
  /-- Absent: a deterministic well-founded target relation. The probabilistic
  carrier records distribution data only. -/
  | probabilisticCarrierIncompatibilityOnly :
      MissingAdapterStructure .probabilisticSubstrate
  /-- Absent: a single well-founded target relation on the combined substrate.
  The union carrier records a second component only. -/
  | unionCarrierIncompatibilityOnly :
      MissingAdapterStructure .unionHierarchySubstrate
  /-- Absent: any strict orientation field. The complexity-only carrier records
  a complexity conclusion with no orientation. -/
  | complexityCarrierIncompatibilityOnly :
      MissingAdapterStructure .complexityOnly

/--
Proves: the indexed disposition of an adapter family. A supported branch
  stores an actual `KO7StepAdapter` together with the equality pinning its
  target relation to that family's named relation, so a supported disposition
  cannot be produced by an adapter for a different method. A NO-TRANSPORT
  branch stores the closed indexed missing-structure record.
Does not prove: uniqueness of a disposition.
Relation: `OperatorKO7.Step`.
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: seven families.
-/
inductive AdapterDisposition : AdapterFamily → Prop
  | polynomialSupported
      (A : KO7StepAdapter)
      (hTarget :
        A.Target = fun a b : Trace => PolyInterpretation.W b < PolyInterpretation.W a) :
      AdapterDisposition .polynomialInterpretation
  | pathOrderSupported
      (A : KO7StepAdapter)
      (hTarget : A.Target = MetaMPO.MPO) :
      AdapterDisposition .multisetPathOrder
  | noTransport {f : AdapterFamily} (missing : MissingAdapterStructure f) :
      AdapterDisposition f

/-- Total disposition over all seven adapter families. -/
theorem adapter_disposition_total (f : AdapterFamily) : AdapterDisposition f := by
  cases f with
  | polynomialInterpretation =>
      exact .polynomialSupported polynomialInterpretationAdapter rfl
  | multisetPathOrder =>
      exact .pathOrderSupported multisetPathOrderAdapter rfl
  | dependencyPairProcessor =>
      exact .noTransport .noCompleteExtractionAndProcessorSoundness
  | signatureTransformation =>
      exact .noTransport .signatureCarrierIncompatibilityOnly
  | probabilisticSubstrate =>
      exact .noTransport .probabilisticCarrierIncompatibilityOnly
  | unionHierarchySubstrate =>
      exact .noTransport .unionCarrierIncompatibilityOnly
  | complexityOnly =>
      exact .noTransport .complexityCarrierIncompatibilityOnly

/-! ## 4. Exact supported / NO-TRANSPORT split -/

/-- Families with at least one concrete inhabited certified adapter. -/
def supportedAdapterFamilies : List AdapterFamily :=
  [ .polynomialInterpretation, .multisetPathOrder ]

/-- Families kept indexed-curated / NO-TRANSPORT. -/
def noTransportAdapterFamilies : List AdapterFamily :=
  [ .dependencyPairProcessor, .signatureTransformation, .probabilisticSubstrate,
    .unionHierarchySubstrate, .complexityOnly ]

theorem supportedAdapterFamilies_length : supportedAdapterFamilies.length = 2 := rfl

theorem noTransportAdapterFamilies_length : noTransportAdapterFamilies.length = 5 := rfl

theorem adapterFamilies_partition_total :
    supportedAdapterFamilies.length + noTransportAdapterFamilies.length = 7 := rfl

theorem adapterFamilies_disjoint :
    ∀ f ∈ supportedAdapterFamilies, f ∉ noTransportAdapterFamilies := by decide

theorem supportedAdapterFamilies_nodup : supportedAdapterFamilies.Nodup := by decide

theorem noTransportAdapterFamilies_nodup : noTransportAdapterFamilies.Nodup := by decide

/-- Every family named supported has a concrete inhabited certified adapter. -/
theorem supported_families_are_inhabited :
    AdapterDisposition .polynomialInterpretation ∧
      AdapterDisposition .multisetPathOrder :=
  ⟨.polynomialSupported polynomialInterpretationAdapter rfl,
    .pathOrderSupported multisetPathOrderAdapter rfl⟩

/-! ## 5. WP-3 notes carriers stay NO-TRANSPORT -/

/-- The four WP-3 notes carriers are inhabited. Inhabitation of a carrier is a
carrier-level fact only. -/
theorem wp3_notes_carriers_inhabited :
    Nonempty RDRSNotesReconciliationAddendum.SignatureTransformationCarrier ∧
      Nonempty RDRSNotesReconciliationAddendum.ProbabilisticSubstrateCarrier ∧
      Nonempty RDRSNotesReconciliationAddendum.UnionSubstrateCarrier ∧
      Nonempty RDRSNotesReconciliationAddendum.ComplexityOnlyCarrier :=
  ⟨⟨RDRSNotesReconciliationAddendum.uncurryingSignatureTransformation⟩,
    ⟨RDRSNotesReconciliationAddendum.fairCoinProbabilisticSubstrate⟩,
    ⟨RDRSNotesReconciliationAddendum.twoComponentUnionSubstrate⟩,
    ⟨RDRSNotesReconciliationAddendum.constantComplexityOnlyCarrier⟩⟩

/-- Carrier incompatibility alone is not a real-method adapter: all four WP-3
notes carriers keep a NO-TRANSPORT disposition with named missing structure. -/
theorem wp3_notes_carriers_remain_noTransport :
    AdapterDisposition .signatureTransformation ∧
      AdapterDisposition .probabilisticSubstrate ∧
      AdapterDisposition .unionHierarchySubstrate ∧
      AdapterDisposition .complexityOnly :=
  ⟨.noTransport .signatureCarrierIncompatibilityOnly,
    .noTransport .probabilisticCarrierIncompatibilityOnly,
    .noTransport .unionCarrierIncompatibilityOnly,
    .noTransport .complexityCarrierIncompatibilityOnly⟩

/-- The dependency-pair processor family is NO-TRANSPORT. Its missing pieces are
named by the constructor: complete all-rule extraction plus processor
soundness. -/
theorem dependencyPairProcessor_remains_noTransport :
    AdapterDisposition .dependencyPairProcessor :=
  .noTransport .noCompleteExtractionAndProcessorSoundness

/-- The available DP extraction covers the `rec_succ` rule only; it is recorded
here as the exact scope of what does exist. -/
theorem dependencyPair_extraction_is_rec_succ_only (b s n : Trace) :
    Step (recΔ b s (delta n)) (app s (recΔ b s n)) ∧
      MetaDependencyPairs.DPPair (recΔ b s (delta n)) (recΔ b s n) :=
  MetaDependencyPairs.rec_succ_extracts_dependency_pair b s n

/-! ## 6. Capstone -/

/--
Proves: the closed-carrier adapter ledger. Two families are supported by
  concrete inhabited certified adapters, five are NO-TRANSPORT with named
  missing structure, the disposition is total over all seven, and the two
  lists are disjoint with exact counts.
Does not prove: dependency-pair processor soundness, or any adapter for the
  four WP-3 notes carriers.
Relation: `OperatorKO7.Step`.
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: the seven named families.
-/
theorem closed_carrier_adapter_ledger_closed :
    (∀ f : AdapterFamily, AdapterDisposition f) ∧
      supportedAdapterFamilies.length = 2 ∧
      noTransportAdapterFamilies.length = 5 ∧
      supportedAdapterFamilies.length + noTransportAdapterFamilies.length = 7 ∧
      WellFounded (fun a b : Trace => Step b a) :=
  ⟨adapter_disposition_total,
    supportedAdapterFamilies_length,
    noTransportAdapterFamilies_length,
    adapterFamilies_partition_total,
    polynomialInterpretationAdapter.sourceWellFounded⟩

end OperatorKO7.ClosedCarrierSemanticsAdapters
