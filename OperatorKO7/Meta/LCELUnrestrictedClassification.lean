import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELUniversalTheorem
import OperatorKO7.Meta.LCELSemanticCorrespondence
import OperatorKO7.Meta.LCELSubstrateMathematics
import OperatorKO7.Meta.LCELBenchmarkDpComparison
import OperatorKO7.Meta.LCELMathematicalSupportWitness
import OperatorKO7.Meta.LCELMathematicalStructuralIdentity
import OperatorKO7.Meta.LCELAdmissibilityData
import OperatorKO7.Meta.LCELUnrestrictedTheorem
import OperatorKO7.Meta.LCELUnrestrictedExistence

/-!
# LCEL Unrestricted Classification and Obstruction Analysis
(post-closure Phase P4A)

This file pursues the **classification theorem** for
`AdmitsLCELUnrestrictedWitness` on arbitrary raw `FormalLCELInstance`
pairs. The closure target is P4A of the post-closure program:

> strongest honest witness-existence classification theorem landed;
> exact scope documented.

Concretely:

- the predicate `AdmitsLCELUnrestrictedWitness L₁ L₂` holds iff both
  instances propositionally admit schema realization **and** the pair
  propositionally admits a mathematical support witness. This is
  proved as a biconditional.
- The three Nonempty components are exposed as a standalone
  classification structure `LCELRawPairClassificationData L₁ L₂`,
  which exists non-propositionally; its forward lift into
  `LCELUnrestrictedMathematicalWitness L₁ L₂` is the packaging lift.
- The obstruction to a universal `∀ L₁ L₂, AdmitsLCELUnrestrictedWitness
  L₁ L₂` theorem is named explicitly: every raw `FormalLCELInstance`
  carries its typed schema data but **not** an automatic
  `RealizesLCELSchema` witness on top of that data, and no raw pair
  carries an automatic `LCELMathematicalSupportWitness`. Those two
  Nonempties are the honest residual proof obligations for a
  witness-free theorem. This file does **not** discharge them
  universally — producing them is still a mathematical content problem
  outside the LCEL schema — but it does reduce the witness-free
  problem to exactly those two Nonempties.

Phase P4C (universal witness-free theorem) is **not** closed here and is
not claimed. Only P4A is closed by this file.
-/

namespace OperatorKO7.LCELUnrestrictedClassification

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELBenchmarkDpComparison
open OperatorKO7.LCELMathematical
open OperatorKO7.LCELMathematicalStructuralIdentity
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELUnrestrictedTheorem
open OperatorKO7.LCELUnrestrictedExistence
open OperatorKO7.ReflectionSchema

/-! ## The classification predicate -/

/-- Classification data for a raw pair of `FormalLCELInstance`s:
schema realization on both sides plus a mathematical support witness
between them. This is the data needed to build an
`LCELUnrestrictedMathematicalWitness`. -/
structure LCELRawPairClassificationData
    (L₁ L₂ : FormalLCELInstance) : Type 1 where
  /-- Schema realization for the source instance. -/
  sourceRealizes : RealizesLCELSchema L₁.toSlotProfile
  /-- Schema realization for the target instance. -/
  targetRealizes : RealizesLCELSchema L₂.toSlotProfile
  /-- Cross-instance mathematical support witness. -/
  comparison : LCELMathematicalSupportWitness L₁ L₂

namespace LCELRawPairClassificationData

/-- Classification data always lifts to an unrestricted mathematical
witness. -/
def toUnrestrictedWitness
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRawPairClassificationData L₁ L₂) :
    LCELUnrestrictedMathematicalWitness L₁ L₂ where
  sourceRealizes := D.sourceRealizes
  targetRealizes := D.targetRealizes
  comparison := D.comparison

end LCELRawPairClassificationData

/-! ## The classification theorem

The propositional predicate `AdmitsLCELUnrestrictedWitness` is
equivalent to the conjunction of the three Nonempty components of
`LCELRawPairClassificationData`. This gives the sharpest honest scope
for any future attempt at a universal witness-free theorem. -/

/-- **LCEL unrestricted-witness classification theorem (Phase P4A).**

`AdmitsLCELUnrestrictedWitness L₁ L₂` holds iff all three component
Nonempties hold: schema realization on the source, schema realization on
the target, and a cross-instance mathematical support witness. -/
theorem admitsUnrestrictedWitness_iff
    (L₁ L₂ : FormalLCELInstance) :
    AdmitsLCELUnrestrictedWitness L₁ L₂
      ↔ Nonempty (RealizesLCELSchema L₁.toSlotProfile)
          ∧ Nonempty (RealizesLCELSchema L₂.toSlotProfile)
          ∧ Nonempty (LCELMathematicalSupportWitness L₁ L₂) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨W⟩
    exact ⟨⟨W.sourceRealizes⟩, ⟨W.targetRealizes⟩, ⟨W.comparison⟩⟩
  · rintro ⟨⟨r₁⟩, ⟨r₂⟩, ⟨cmp⟩⟩
    exact
      ⟨{ sourceRealizes := r₁, targetRealizes := r₂, comparison := cmp }⟩

/-- Forward direction of the classification: an unrestricted witness
yields all three Nonempty components. -/
theorem classification_of_admitsUnrestrictedWitness
    {L₁ L₂ : FormalLCELInstance}
    (h : AdmitsLCELUnrestrictedWitness L₁ L₂) :
    Nonempty (RealizesLCELSchema L₁.toSlotProfile)
      ∧ Nonempty (RealizesLCELSchema L₂.toSlotProfile)
      ∧ Nonempty (LCELMathematicalSupportWitness L₁ L₂) :=
  (admitsUnrestrictedWitness_iff L₁ L₂).mp h

/-- Reverse direction of the classification: if all three components
exist propositionally, the raw pair admits an unrestricted witness. -/
theorem admitsUnrestrictedWitness_of_classification
    {L₁ L₂ : FormalLCELInstance}
    (h₁ : Nonempty (RealizesLCELSchema L₁.toSlotProfile))
    (h₂ : Nonempty (RealizesLCELSchema L₂.toSlotProfile))
    (hW : Nonempty (LCELMathematicalSupportWitness L₁ L₂)) :
    AdmitsLCELUnrestrictedWitness L₁ L₂ :=
  (admitsUnrestrictedWitness_iff L₁ L₂).mpr ⟨h₁, h₂, hW⟩

/-! ## The obstruction predicate

A named predicate enumerating the two kinds of proof obligation that
remain before a universal witness-free theorem could be claimed: schema
realization on each side, and a cross-instance mathematical support
witness for each pair. This predicate is **not** proved universally;
it is the honest boundary for Phase P4C. -/

/-- The two-tier obstruction between the admissibility-with-witness
theorem (closed) and the bare witness-free theorem (unclosed): for any
raw pair `L₁ L₂`, the residual proof obligations are the three Nonempty
components of `LCELRawPairClassificationData`. -/
abbrev LCELWitnessFreeResidualObligation
    (L₁ L₂ : FormalLCELInstance) : Prop :=
  Nonempty (RealizesLCELSchema L₁.toSlotProfile)
    ∧ Nonempty (RealizesLCELSchema L₂.toSlotProfile)
    ∧ Nonempty (LCELMathematicalSupportWitness L₁ L₂)

/-- Discharging the residual obligation is equivalent to admitting an
unrestricted witness. This is just `admitsUnrestrictedWitness_iff` under
the abbreviation. -/
theorem witnessFreeResidualObligation_iff
    (L₁ L₂ : FormalLCELInstance) :
    LCELWitnessFreeResidualObligation L₁ L₂
      ↔ AdmitsLCELUnrestrictedWitness L₁ L₂ :=
  (admitsUnrestrictedWitness_iff L₁ L₂).symm

/-! ## Canonical classification data -/

/-- Canonical Gödel ↔ native DP classification data. -/
def godel_dp_classificationData :
    LCELRawPairClassificationData
      godel1931LCELInstance
      dpEmitterLCELInstance where
  sourceRealizes := godel1931LCELInstance_realizesSchema
  targetRealizes := dpEmitterLCELInstance_realizesSchema
  comparison := godel_dp_lcelMathematicalSupportWitness

/-- Canonical Gödel ↔ benchmark-transport classification data. -/
def godel_benchmark_classificationData :
    LCELRawPairClassificationData
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  sourceRealizes := godel1931LCELInstance_realizesSchema
  targetRealizes := benchmarkTransportLCELInstance_realizesSchema
  comparison := godel_benchmark_lcelMathematicalSupportWitness

/-! ## Refined classification via pairwise bridge data (genuinely weaker)

The classification above is an honest tautology: it asserts that
`AdmitsLCELUnrestrictedWitness` is `Nonempty (LCELMathematicalSupportWitness)`
plus the two schema-realization Nonempties, and since
`LCELMathematicalSupportWitness` already packages schema-realization-
independent content, the equivalence does not meaningfully reduce the
witness-construction burden. The checker's review flagged this.

The refinement below supplies a strictly weaker set of inputs:
`LCELRawPairBridgeData` carries only a **strong slot correspondence** and
a **stagewise equivalence of profile shapes**, two components that are
pairwise (per-pair, not per-instance) and are independent of the
admissibility data packages on each side. Given:

- `LCELAdmissibilityData L₁` (per-side data on the source),
- `LCELAdmissibilityData L₂` (per-side data on the target), and
- `LCELRawPairBridgeData L₁ L₂` (pairwise bridging data),

a builder constructs a full `LCELMathematicalSupportWitness L₁ L₂`
without taking `Nonempty (LCELMathematicalSupportWitness L₁ L₂)` as a
hypothesis. This is a real decomposition: the inputs are strictly
simpler than the output carrier.

The construction produces an unrestricted mathematical witness whose
transport functions are **constant canonical transports** on the
generic pair (each transport returns the target canonical theorem
extracted from `A₂`'s support records). On the paper-facing canonical
pairs, the source-informed canonical transports of
`LCELMathematicalSupportWitness.lean` remain the authoritative
construction; this bridge-based builder is a separate, more primitive
entry point for arbitrary pairs.

The substantive content of the refined classification:

- witness admission is implied by having admissibility data on both
  sides plus pairwise bridging data (strong slot correspondence +
  stagewise equivalence) — this is a **strictly weaker** hypothesis set
  than `Nonempty (LCELMathematicalSupportWitness)`, in the sense that
  it does not package the support records and substrate data redundantly
  inside the cross-instance witness;
- the residual mathematical content still needed for an arbitrary raw
  pair is now **exactly** "do these two per-side admissibility data
  packages exist and does a pairwise bridge exist?", which is the
  cleanest possible reduction of the problem before one invents new
  mathematics outside the LCEL schema.
-/

/-- Pairwise bridge data between two raw `FormalLCELInstance`s: a
strong semantic slot correspondence plus a stagewise equivalence of
comparison-profile shapes. This is strictly pairwise data (no per-side
admissibility content) and is the minimal "relational layer" needed on
top of per-side admissibility to reconstruct a full
`LCELMathematicalSupportWitness`. -/
structure LCELRawPairBridgeData
    (L₁ L₂ : FormalLCELInstance) : Type 1 where
  /-- Strong semantic slot correspondence carrying preservation laws on
  all four slots plus typed base-sentence translation. -/
  strongSlot : LCELStrongSemanticSlotCorrespondence L₁ L₂
  /-- Stagewise equivalence of the two underlying comparison-profile
  shapes. -/
  stagewise :
    StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape

namespace LCELRawPairBridgeData

/-- Downgrade the strong slot correspondence to the plain semantic slot
correspondence via `toSlotCorrespondence`. -/
def toSemanticSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (B : LCELRawPairBridgeData L₁ L₂) :
    LCELSemanticSlotCorrespondence L₁ L₂ :=
  B.strongSlot.toSlotCorrespondence

end LCELRawPairBridgeData

/-! ### The bridge-data builder: LCELMathematicalSupportWitness from
two admissibility-data packages plus a pairwise bridge

This is the real content of the refined classification theorem. It
constructs every field of `LCELMathematicalSupportWitness` from the
admissibility data plus the pairwise bridge. Support equivalence iffs
are `iff_of_true` from both sides being inhabited (because each
admissibility data package supplies both propositional sides of its
support records). Theorem-strength substrate objects are extracted from
support records via the existing `_of_support` helpers. Transport
functions are constant canonical transports (returning the target
canonical theorem), so `transport...Source := rfl`. The external-license
and reimport-class slot iffs come from the downgraded strong
correspondence, matching the witness's coherence constraints. -/

private theorem baseSupport_supported_of_admissibilityData
    {L : FormalLCELInstance} (A : LCELAdmissibilityData L) :
    BaseReversibilitySupport.supported A.baseSupport :=
  ⟨A.baseSupport.internalSentenceProved, A.baseSupport.boundaryRealized⟩

private theorem licenseSupport_supported_of_admissibilityData
    {L : FormalLCELInstance} (A : LCELAdmissibilityData L) :
    LicenseIrreversibilitySupport.supported A.licenseSupport :=
  ⟨A.licenseSupport.strongerFrameworkReflectsBlocked,
    A.licenseSupport.externalLicenseHolds,
    A.licenseSupport.blockedNotProvable,
    A.licenseSupport.blockedTrue,
    A.licenseSupport.blockedLicensedAdmission⟩

private theorem reimportSupport_supported_of_admissibilityData
    {L : FormalLCELInstance} (A : LCELAdmissibilityData L) :
    ReimportReversibilitySupport.supported A.reimportSupport :=
  ⟨A.reimportSupport.witnessCertifiesBlocked,
    A.reimportSupport.reimportClassHolds,
    A.reimportSupport.annotationRealized,
    A.reimportSupport.witnessCertifiesImported,
    A.reimportSupport.importedTrue⟩

private theorem boundarySupport_supported_of_admissibilityData
    {L : FormalLCELInstance} (A : LCELAdmissibilityData L) :
    BoundaryFactorizationSupport.supported A.boundarySupport :=
  ⟨reimportSupport_supported_of_admissibilityData
      { realizes := A.realizes
        baseSupport := A.baseSupport
        licenseSupport := A.licenseSupport
        reimportSupport := A.boundarySupport.visibleSupport
        boundarySupport := A.boundarySupport },
    licenseSupport_supported_of_admissibilityData
      { realizes := A.realizes
        baseSupport := A.baseSupport
        licenseSupport := A.boundarySupport.sensitiveSupport
        reimportSupport := A.reimportSupport
        boundarySupport := A.boundarySupport },
    A.boundarySupport.boundaryRealized⟩

/-- Build a full `LCELMathematicalSupportWitness L₁ L₂` from two
admissibility-data packages and one pairwise bridge. Every field is
constructed; no witness-level hypothesis is taken. -/
def LCELMathematicalSupportWitness.ofBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELRawPairBridgeData L₁ L₂) :
    LCELMathematicalSupportWitness L₁ L₂ where
  toLCELSupportComparisonWitness :=
    { comparisonStagewise := bridge.stagewise
      externalLicenseEquivalent :=
        bridge.strongSlot.externalLicense.toExternalLicenseCorrespondence.toIff
      reimportClassEquivalent :=
        bridge.strongSlot.reimportClass.toReimportClassCorrespondence.toIff
      baseLayerSupportEquivalent :=
        Iff.intro
          (fun _ => A₂.baseSupport.semanticBaseHolds)
          (fun _ => A₁.baseSupport.semanticBaseHolds)
      licenseTransferSupportEquivalent :=
        Iff.intro
          (fun _ => A₂.licenseSupport.semanticTransferHolds)
          (fun _ => A₁.licenseSupport.semanticTransferHolds)
      reimportTransferSupportEquivalent :=
        Iff.intro
          (fun _ => A₂.reimportSupport.semanticTransferHolds)
          (fun _ => A₁.reimportSupport.semanticTransferHolds)
      sourceBaseSupport := A₁.baseSupport
      targetBaseSupport := A₂.baseSupport
      sourceLicenseSupport := A₁.licenseSupport
      targetLicenseSupport := A₂.licenseSupport
      sourceReimportSupport := A₁.reimportSupport
      targetReimportSupport := A₂.reimportSupport
      sourceBoundarySupport := A₁.boundarySupport
      targetBoundarySupport := A₂.boundarySupport
      baseSupportEquivalent :=
        Iff.intro
          (fun _ => baseSupport_supported_of_admissibilityData A₂)
          (fun _ => baseSupport_supported_of_admissibilityData A₁)
      licenseSupportEquivalent :=
        Iff.intro
          (fun _ => licenseSupport_supported_of_admissibilityData A₂)
          (fun _ => licenseSupport_supported_of_admissibilityData A₁)
      reimportSupportEquivalent :=
        Iff.intro
          (fun _ => reimportSupport_supported_of_admissibilityData A₂)
          (fun _ => reimportSupport_supported_of_admissibilityData A₁)
      boundarySupportEquivalent :=
        Iff.intro
          (fun _ => boundarySupport_supported_of_admissibilityData A₂)
          (fun _ => boundarySupport_supported_of_admissibilityData A₁) }
  slotCorrespondence := bridge.strongSlot
  externalLicense_fromCorrespondence := rfl
  reimportClass_fromCorrespondence := rfl
  sourceBaseTheorem := baseReversibilityTheorem_of_support A₁.baseSupport
  targetBaseTheorem := baseReversibilityTheorem_of_support A₂.baseSupport
  sourceBaseTheorem_fromSupport := rfl
  targetBaseTheorem_fromSupport := rfl
  sourceLicenseTheorem := licenseIrreversibilityTheorem_of_support A₁.licenseSupport
  targetLicenseTheorem := licenseIrreversibilityTheorem_of_support A₂.licenseSupport
  sourceLicenseTheorem_fromSupport := rfl
  targetLicenseTheorem_fromSupport := rfl
  sourceReimportTheorem := reimportReversibilityTheorem_of_support A₁.reimportSupport
  targetReimportTheorem := reimportReversibilityTheorem_of_support A₂.reimportSupport
  sourceReimportTheorem_fromSupport := rfl
  targetReimportTheorem_fromSupport := rfl
  sourceBoundaryTheorem := boundaryFactorizationTheorem_of_support A₁.boundarySupport
  targetBoundaryTheorem := boundaryFactorizationTheorem_of_support A₂.boundarySupport
  sourceBoundaryTheorem_fromSupport := rfl
  targetBoundaryTheorem_fromSupport := rfl
  transportBase := fun _ => baseReversibilityTheorem_of_support A₂.baseSupport
  transportBase_source := rfl
  transportLicense := fun _ => licenseIrreversibilityTheorem_of_support A₂.licenseSupport
  transportLicense_source := rfl
  transportReimport := fun _ => reimportReversibilityTheorem_of_support A₂.reimportSupport
  transportReimport_source := rfl
  transportBoundary := fun _ => boundaryFactorizationTheorem_of_support A₂.boundarySupport
  transportBoundary_source := rfl

/-- Build an unrestricted mathematical witness from admissibility data
plus bridge data, via the bridge-based `LCELMathematicalSupportWitness`
builder and the existing `LCELAdmissibilityData` → realization route. -/
def LCELUnrestrictedMathematicalWitness.ofAdmissibilityDataAndBridge
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELRawPairBridgeData L₁ L₂) :
    LCELUnrestrictedMathematicalWitness L₁ L₂ :=
  LCELUnrestrictedMathematicalWitness.ofAdmissibilityData
    A₁ A₂
    (LCELMathematicalSupportWitness.ofBridgeData A₁ A₂ bridge)

/-! ### The refined classification theorem (Phase P4A, strengthened) -/

/-- **LCEL unrestricted-witness refined classification theorem.**

A raw pair admits an unrestricted mathematical witness whenever two
`LCELAdmissibilityData` packages and a pairwise `LCELRawPairBridgeData`
exist. This is strictly weaker than the tautological `iff` above:
instead of assuming the whole `LCELMathematicalSupportWitness`
propositionally, it asks only for admissibility on each side plus a
pairwise bridge consisting of a strong slot correspondence and a
stagewise equivalence of shapes. The residual witness-construction
burden is reduced to constructing the bridge, not the full witness. -/
theorem admitsUnrestrictedWitness_of_bridgeData
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELRawPairBridgeData L₁ L₂) :
    AdmitsLCELUnrestrictedWitness L₁ L₂ :=
  ⟨LCELUnrestrictedMathematicalWitness.ofAdmissibilityDataAndBridge
    A₁ A₂ bridge⟩

/-! ### Canonical refined bridges

On the two paper-facing canonical pairs, the bridge data is supplied by
the existing strong slot correspondence and the stagewise equivalence
extracted from the canonical mathematical support witness. These
canonical bridges close the refined classification theorem on the
manuscript-critical endpoints without going through the tautological layer. -/

/-- Canonical Gödel ↔ native DP pairwise bridge data. -/
def godel_dp_bridgeData :
    LCELRawPairBridgeData
      godel1931LCELInstance
      dpEmitterLCELInstance where
  strongSlot := godel_dp_strongSemanticSlotCorrespondence
  stagewise :=
    godel_dp_lcelMathematicalSupportWitness.comparisonStagewise

/-- Canonical Gödel ↔ benchmark-transport pairwise bridge data. -/
def godel_benchmark_bridgeData :
    LCELRawPairBridgeData
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  strongSlot := godel_benchmark_strongSemanticSlotCorrespondence
  stagewise :=
    godel_benchmark_lcelMathematicalSupportWitness.comparisonStagewise

/-- Gödel ↔ DP admits an unrestricted witness via the refined
classification (admissibility data on each side plus canonical bridge). -/
theorem godel_dp_admitsUnrestrictedWitness_viaBridge :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      dpEmitterLCELInstance :=
  admitsUnrestrictedWitness_of_bridgeData
    godel1931LCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    godel_dp_bridgeData

/-- Gödel ↔ benchmark admits an unrestricted witness via the refined
classification. -/
theorem godel_benchmark_admitsUnrestrictedWitness_viaBridge :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      benchmarkTransportLCELInstance :=
  admitsUnrestrictedWitness_of_bridgeData
    godel1931LCELAdmissibilityData
    benchmarkTransportLCELAdmissibilityData
    godel_benchmark_bridgeData

/-! ## Audit theorems: the weak `ofBridgeData` route is constant

These four theorems make the collapse of the weak bridge-data route
visible at the theorem level: the `transportBase`, `transportLicense`,
`transportReimport`, and `transportBoundary` fields of
`LCELMathematicalSupportWitness.ofBridgeData A₁ A₂ bridge` are **constant**
functions, always returning the canonical target theorem extracted from
`A₂`'s support records regardless of the source theorem input. The
strong route below replaces each with a genuine transport function
supplied by the bridge itself. -/

theorem ofBridgeData_transportBase_constant
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELRawPairBridgeData L₁ L₂)
    (T : BaseReversibilityTheorem L₁) :
    (LCELMathematicalSupportWitness.ofBridgeData A₁ A₂ bridge).transportBase T
      = baseReversibilityTheorem_of_support A₂.baseSupport :=
  rfl

theorem ofBridgeData_transportLicense_constant
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELRawPairBridgeData L₁ L₂)
    (T : LicenseIrreversibilityTheorem L₁) :
    (LCELMathematicalSupportWitness.ofBridgeData A₁ A₂ bridge).transportLicense T
      = licenseIrreversibilityTheorem_of_support A₂.licenseSupport :=
  rfl

theorem ofBridgeData_transportReimport_constant
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELRawPairBridgeData L₁ L₂)
    (T : ReimportReversibilityTheorem L₁) :
    (LCELMathematicalSupportWitness.ofBridgeData A₁ A₂ bridge).transportReimport T
      = reimportReversibilityTheorem_of_support A₂.reimportSupport :=
  rfl

theorem ofBridgeData_transportBoundary_constant
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELRawPairBridgeData L₁ L₂)
    (T : BoundaryFactorizationTheorem L₁) :
    (LCELMathematicalSupportWitness.ofBridgeData A₁ A₂ bridge).transportBoundary T
      = boundaryFactorizationTheorem_of_support A₂.boundarySupport :=
  rfl

/-! ## Strong transport-bridge data

`LCELTransportBridgeData A₁ A₂` is a strictly stronger pairwise bridge
structure than `LCELRawPairBridgeData`. It carries, in addition to the
strong slot correspondence and stagewise equivalence, four **explicit
theorem-object transport functions** and four coherence equations tying
each transport's output on the canonical source theorem
(`baseReversibilityTheorem_of_support A₁.<slot>Support` etc.) to the
canonical target theorem extracted from `A₂`'s support records.

This is strictly smaller than a full `LCELMathematicalSupportWitness`:
it does not carry support records, support-equivalence iffs, or the
eight `source/target<Slot>Theorem` + `_fromSupport` fields. The
admissibility data supplies all of those; the bridge adds only the
transport layer that the weak `LCELRawPairBridgeData` lacks.

On a pair where the strong slot correspondence is non-constant (e.g.
the benchmark ↔ DP pair under the typed sentence translation
`benchmarkTransportSentence_to_dpEmitterSentence`), the bridge's
transport functions are the genuine source-informed transport helpers
rather than constant target-returning closures. -/
structure LCELTransportBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂) : Type 1 where
  /-- Strong semantic slot correspondence. -/
  strongSlot : LCELStrongSemanticSlotCorrespondence L₁ L₂
  /-- Stagewise equivalence of comparison-profile shapes. -/
  stagewise :
    StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape
  /-- Explicit base-theorem transport. -/
  transportBase :
    BaseReversibilityTheorem L₁ → BaseReversibilityTheorem L₂
  /-- Explicit license-theorem transport. -/
  transportLicense :
    LicenseIrreversibilityTheorem L₁ → LicenseIrreversibilityTheorem L₂
  /-- Explicit reimport-theorem transport. -/
  transportReimport :
    ReimportReversibilityTheorem L₁ → ReimportReversibilityTheorem L₂
  /-- Explicit boundary-theorem transport. -/
  transportBoundary :
    BoundaryFactorizationTheorem L₁ → BoundaryFactorizationTheorem L₂
  /-- Coherence: the bridge's base transport carries the canonical source
  base theorem (extracted from `A₁.baseSupport`) to the canonical target
  base theorem (extracted from `A₂.baseSupport`). -/
  transportBase_canonical :
    transportBase (baseReversibilityTheorem_of_support A₁.baseSupport)
      = baseReversibilityTheorem_of_support A₂.baseSupport
  /-- Coherence: the bridge's license transport carries the canonical
  source license theorem to the canonical target license theorem. -/
  transportLicense_canonical :
    transportLicense (licenseIrreversibilityTheorem_of_support A₁.licenseSupport)
      = licenseIrreversibilityTheorem_of_support A₂.licenseSupport
  /-- Coherence: the bridge's reimport transport carries the canonical
  source reimport theorem to the canonical target reimport theorem. -/
  transportReimport_canonical :
    transportReimport (reimportReversibilityTheorem_of_support A₁.reimportSupport)
      = reimportReversibilityTheorem_of_support A₂.reimportSupport
  /-- Coherence: the bridge's boundary transport carries the canonical
  source boundary theorem to the canonical target boundary theorem. -/
  transportBoundary_canonical :
    transportBoundary (boundaryFactorizationTheorem_of_support A₁.boundarySupport)
      = boundaryFactorizationTheorem_of_support A₂.boundarySupport

namespace LCELTransportBridgeData

/-- Downgrade a strong transport bridge to the weak pairwise bridge. -/
def toRawPairBridgeData
    {L₁ L₂ : FormalLCELInstance}
    {A₁ : LCELAdmissibilityData L₁}
    {A₂ : LCELAdmissibilityData L₂}
    (bridge : LCELTransportBridgeData A₁ A₂) :
    LCELRawPairBridgeData L₁ L₂ where
  strongSlot := bridge.strongSlot
  stagewise := bridge.stagewise

end LCELTransportBridgeData

/-! ### The strong bridge-data builder

Build a full `LCELMathematicalSupportWitness L₁ L₂` from two
admissibility-data packages and one strong transport bridge. The
admissibility data supply the support records, support-equivalence
iffs, and the eight `source/target<Slot>Theorem` + `_fromSupport`
fields (via the weak `ofBridgeData` underneath); the strong bridge
overrides the four transport fields with its explicit, non-constant
transport functions and supplies their coherence equations. -/
def LCELMathematicalSupportWitness.ofTransportBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELTransportBridgeData A₁ A₂) :
    LCELMathematicalSupportWitness L₁ L₂ :=
  let weak :=
    LCELMathematicalSupportWitness.ofBridgeData A₁ A₂ bridge.toRawPairBridgeData
  { toLCELSupportComparisonWitness := weak.toLCELSupportComparisonWitness
    slotCorrespondence := weak.slotCorrespondence
    externalLicense_fromCorrespondence := weak.externalLicense_fromCorrespondence
    reimportClass_fromCorrespondence := weak.reimportClass_fromCorrespondence
    sourceBaseTheorem := weak.sourceBaseTheorem
    targetBaseTheorem := weak.targetBaseTheorem
    sourceBaseTheorem_fromSupport := weak.sourceBaseTheorem_fromSupport
    targetBaseTheorem_fromSupport := weak.targetBaseTheorem_fromSupport
    sourceLicenseTheorem := weak.sourceLicenseTheorem
    targetLicenseTheorem := weak.targetLicenseTheorem
    sourceLicenseTheorem_fromSupport := weak.sourceLicenseTheorem_fromSupport
    targetLicenseTheorem_fromSupport := weak.targetLicenseTheorem_fromSupport
    sourceReimportTheorem := weak.sourceReimportTheorem
    targetReimportTheorem := weak.targetReimportTheorem
    sourceReimportTheorem_fromSupport := weak.sourceReimportTheorem_fromSupport
    targetReimportTheorem_fromSupport := weak.targetReimportTheorem_fromSupport
    sourceBoundaryTheorem := weak.sourceBoundaryTheorem
    targetBoundaryTheorem := weak.targetBoundaryTheorem
    sourceBoundaryTheorem_fromSupport := weak.sourceBoundaryTheorem_fromSupport
    targetBoundaryTheorem_fromSupport := weak.targetBoundaryTheorem_fromSupport
    transportBase := bridge.transportBase
    transportBase_source := by
      rw [weak.sourceBaseTheorem_fromSupport, weak.targetBaseTheorem_fromSupport]
      exact bridge.transportBase_canonical
    transportLicense := bridge.transportLicense
    transportLicense_source := by
      rw [weak.sourceLicenseTheorem_fromSupport, weak.targetLicenseTheorem_fromSupport]
      exact bridge.transportLicense_canonical
    transportReimport := bridge.transportReimport
    transportReimport_source := by
      rw [weak.sourceReimportTheorem_fromSupport, weak.targetReimportTheorem_fromSupport]
      exact bridge.transportReimport_canonical
    transportBoundary := bridge.transportBoundary
    transportBoundary_source := by
      rw [weak.sourceBoundaryTheorem_fromSupport, weak.targetBoundaryTheorem_fromSupport]
      exact bridge.transportBoundary_canonical }

/-! ### Audit theorems: the strong route uses the bridge transports

These four theorems make the strong route's source-sensitivity visible
at the theorem level: the `transportBase`, `transportLicense`,
`transportReimport`, and `transportBoundary` fields of the
strong-route witness are definitionally **the bridge's own transport
functions**, not constant target-returning closures. Contrast with
`ofBridgeData_transport..._constant` above. -/

theorem ofTransportBridgeData_transportBase_fromBridge
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELTransportBridgeData A₁ A₂)
    (T : BaseReversibilityTheorem L₁) :
    (LCELMathematicalSupportWitness.ofTransportBridgeData A₁ A₂ bridge).transportBase T
      = bridge.transportBase T :=
  rfl

theorem ofTransportBridgeData_transportLicense_fromBridge
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELTransportBridgeData A₁ A₂)
    (T : LicenseIrreversibilityTheorem L₁) :
    (LCELMathematicalSupportWitness.ofTransportBridgeData A₁ A₂ bridge).transportLicense T
      = bridge.transportLicense T :=
  rfl

theorem ofTransportBridgeData_transportReimport_fromBridge
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELTransportBridgeData A₁ A₂)
    (T : ReimportReversibilityTheorem L₁) :
    (LCELMathematicalSupportWitness.ofTransportBridgeData A₁ A₂ bridge).transportReimport T
      = bridge.transportReimport T :=
  rfl

theorem ofTransportBridgeData_transportBoundary_fromBridge
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELTransportBridgeData A₁ A₂)
    (T : BoundaryFactorizationTheorem L₁) :
    (LCELMathematicalSupportWitness.ofTransportBridgeData A₁ A₂ bridge).transportBoundary T
      = bridge.transportBoundary T :=
  rfl

/-! ### Strong-bridge unrestricted lifter and refined classification -/

/-- Build an unrestricted mathematical witness from admissibility data
plus strong transport-bridge data, via the strong bridge-based
`LCELMathematicalSupportWitness` builder. -/
def LCELUnrestrictedMathematicalWitness.ofAdmissibilityDataAndTransportBridge
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELTransportBridgeData A₁ A₂) :
    LCELUnrestrictedMathematicalWitness L₁ L₂ :=
  LCELUnrestrictedMathematicalWitness.ofAdmissibilityData
    A₁ A₂
    (LCELMathematicalSupportWitness.ofTransportBridgeData A₁ A₂ bridge)

/-- **LCEL unrestricted-witness refined classification theorem via strong
transport bridge.** A raw pair admits an unrestricted mathematical
witness whenever two admissibility data packages and a strong transport
bridge exist; the resulting witness's transport functions are the
bridge's own, not constant target-returning closures. -/
theorem admitsUnrestrictedWitness_of_transportBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (bridge : LCELTransportBridgeData A₁ A₂) :
    AdmitsLCELUnrestrictedWitness L₁ L₂ :=
  ⟨LCELUnrestrictedMathematicalWitness.ofAdmissibilityDataAndTransportBridge
    A₁ A₂ bridge⟩

/-! ### Canonical Gödel-side strong transport bridges

The canonical Gödel ↔ DP and Gödel ↔ benchmark pairs' mathematical
support witnesses use correspondence-driven transport helpers; the
transport-bridge record below packages exactly the transport functions
used in those canonical witnesses, now exposed explicitly. The
transport coherence equations are `rfl` because the canonical
correspondence's translate maps are constant on the Gödel side, so
transport applied to the canonical source theorem reduces definitionally
to the canonical target theorem. -/

/-- Canonical Gödel ↔ native DP strong transport bridge. -/
def godel_dp_transportBridgeData :
    LCELTransportBridgeData
      godel1931LCELAdmissibilityData
      dpEmitterLCELAdmissibilityData where
  strongSlot := godel_dp_strongSemanticSlotCorrespondence
  stagewise :=
    godel_dp_lcelMathematicalSupportWitness.comparisonStagewise
  transportBase := fun T =>
    baseReversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence T
  transportLicense := fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence
      dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission T
  transportReimport := fun T =>
    reimportReversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence T
  transportBoundary := fun T =>
    boundaryFactorizationTheorem_transport
      (fun T' =>
        reimportReversibilityTheorem_transport_viaStrongSlot
          godel_dp_strongSemanticSlotCorrespondence T')
      (fun T' =>
        licenseIrreversibilityTheorem_transport_viaStrongSlot
          godel_dp_strongSemanticSlotCorrespondence
          dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission T')
      dpEmitterBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
      dpEmitterBoundaryFactorizationSupport.reflectionBlockedEqImported
      dpEmitterBoundaryFactorizationSupport.boundaryRealized
      T
  transportBase_canonical := rfl
  transportLicense_canonical := rfl
  transportReimport_canonical := rfl
  transportBoundary_canonical := rfl

/-- Canonical Gödel ↔ benchmark-transport strong transport bridge. -/
def godel_benchmark_transportBridgeData :
    LCELTransportBridgeData
      godel1931LCELAdmissibilityData
      benchmarkTransportLCELAdmissibilityData where
  strongSlot := godel_benchmark_strongSemanticSlotCorrespondence
  stagewise :=
    godel_benchmark_lcelMathematicalSupportWitness.comparisonStagewise
  transportBase := fun T =>
    baseReversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence T
  transportLicense := fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence
      benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission T
  transportReimport := fun T =>
    reimportReversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence T
  transportBoundary := fun T =>
    boundaryFactorizationTheorem_transport
      (fun T' =>
        reimportReversibilityTheorem_transport_viaStrongSlot
          godel_benchmark_strongSemanticSlotCorrespondence T')
      (fun T' =>
        licenseIrreversibilityTheorem_transport_viaStrongSlot
          godel_benchmark_strongSemanticSlotCorrespondence
          benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission T')
      benchmarkTransportBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
      benchmarkTransportBoundaryFactorizationSupport.reflectionBlockedEqImported
      benchmarkTransportBoundaryFactorizationSupport.boundaryRealized
      T
  transportBase_canonical := rfl
  transportLicense_canonical := rfl
  transportReimport_canonical := rfl
  transportBoundary_canonical := rfl

/-- Gödel ↔ DP admits an unrestricted witness via the strong transport
bridge. -/
theorem godel_dp_admitsUnrestrictedWitness_viaTransportBridge :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      dpEmitterLCELInstance :=
  admitsUnrestrictedWitness_of_transportBridgeData
    godel1931LCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    godel_dp_transportBridgeData

/-- Gödel ↔ benchmark admits an unrestricted witness via the strong
transport bridge. -/
theorem godel_benchmark_admitsUnrestrictedWitness_viaTransportBridge :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      benchmarkTransportLCELInstance :=
  admitsUnrestrictedWitness_of_transportBridgeData
    godel1931LCELAdmissibilityData
    benchmarkTransportLCELAdmissibilityData
    godel_benchmark_transportBridgeData

/-- Downgrading the canonical Gödel ↔ native DP strong transport bridge to
the weak bridge recovers the canonical weak bridge exactly. -/
theorem godel_dp_transportBridgeData_toRawPairBridgeData_eq_bridgeData :
    godel_dp_transportBridgeData.toRawPairBridgeData = godel_dp_bridgeData :=
  rfl

/-- Downgrading the canonical Gödel ↔ benchmark strong transport bridge to
the weak bridge recovers the canonical weak bridge exactly. -/
theorem godel_benchmark_transportBridgeData_toRawPairBridgeData_eq_bridgeData :
    godel_benchmark_transportBridgeData.toRawPairBridgeData
      = godel_benchmark_bridgeData :=
  rfl

/-! ## Reverse direction of the refined bridge-data classification

Given an unrestricted mathematical witness, we can extract admissibility
data on each side and a pairwise bridge. That extraction completes the
refined classification into a true biconditional at the separated-input
level: admission is equivalent to having admissibility data on each
side plus pairwise bridging data.

The three extraction helpers are placed into the
`OperatorKO7.LCELUnrestrictedTheorem.LCELUnrestrictedMathematicalWitness`
namespace so that dot notation on a witness resolves them cleanly. -/

end OperatorKO7.LCELUnrestrictedClassification

namespace OperatorKO7.LCELUnrestrictedTheorem.LCELUnrestrictedMathematicalWitness

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELUnrestrictedTheorem
open OperatorKO7.LCELMathematical
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELUnrestrictedClassification

/-- Extract source-side admissibility data from an unrestricted witness. -/
def toSourceAdmissibilityData
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    LCELAdmissibilityData L₁ where
  realizes := W.sourceRealizes
  baseSupport := W.comparison.sourceBaseSupport
  licenseSupport := W.comparison.sourceLicenseSupport
  reimportSupport := W.comparison.sourceReimportSupport
  boundarySupport := W.comparison.sourceBoundarySupport

/-- Extract target-side admissibility data from an unrestricted witness. -/
def toTargetAdmissibilityData
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    LCELAdmissibilityData L₂ where
  realizes := W.targetRealizes
  baseSupport := W.comparison.targetBaseSupport
  licenseSupport := W.comparison.targetLicenseSupport
  reimportSupport := W.comparison.targetReimportSupport
  boundarySupport := W.comparison.targetBoundarySupport

/-- Extract the pairwise bridge from an unrestricted witness. The
witness already carries the strong slot correspondence (via the
mathematical support witness) and the stagewise equivalence (via the
inherited support-comparison witness), so the bridge is read off
directly. -/
def toBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    LCELRawPairBridgeData L₁ L₂ where
  strongSlot := W.comparison.slotCorrespondence
  stagewise := W.comparison.comparisonStagewise

/-- Extract the strong transport bridge from an unrestricted witness.
The witness's four `transport<Slot>` fields plus their `..._source`
coherence equations supply exactly the transport-bridge fields tied to
the extracted source/target admissibility data. -/
def toTransportBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    LCELTransportBridgeData
      W.toSourceAdmissibilityData
      W.toTargetAdmissibilityData where
  strongSlot := W.comparison.slotCorrespondence
  stagewise := W.comparison.comparisonStagewise
  transportBase := W.comparison.transportBase
  transportLicense := W.comparison.transportLicense
  transportReimport := W.comparison.transportReimport
  transportBoundary := W.comparison.transportBoundary
  transportBase_canonical := by
    show W.comparison.transportBase
        (baseReversibilityTheorem_of_support W.comparison.sourceBaseSupport)
      = baseReversibilityTheorem_of_support W.comparison.targetBaseSupport
    rw [← W.comparison.sourceBaseTheorem_fromSupport,
        ← W.comparison.targetBaseTheorem_fromSupport]
    exact W.comparison.transportBase_source
  transportLicense_canonical := by
    show W.comparison.transportLicense
        (licenseIrreversibilityTheorem_of_support W.comparison.sourceLicenseSupport)
      = licenseIrreversibilityTheorem_of_support W.comparison.targetLicenseSupport
    rw [← W.comparison.sourceLicenseTheorem_fromSupport,
        ← W.comparison.targetLicenseTheorem_fromSupport]
    exact W.comparison.transportLicense_source
  transportReimport_canonical := by
    show W.comparison.transportReimport
        (reimportReversibilityTheorem_of_support W.comparison.sourceReimportSupport)
      = reimportReversibilityTheorem_of_support W.comparison.targetReimportSupport
    rw [← W.comparison.sourceReimportTheorem_fromSupport,
        ← W.comparison.targetReimportTheorem_fromSupport]
    exact W.comparison.transportReimport_source
  transportBoundary_canonical := by
    show W.comparison.transportBoundary
        (boundaryFactorizationTheorem_of_support W.comparison.sourceBoundarySupport)
      = boundaryFactorizationTheorem_of_support W.comparison.targetBoundarySupport
    rw [← W.comparison.sourceBoundaryTheorem_fromSupport,
        ← W.comparison.targetBoundaryTheorem_fromSupport]
    exact W.comparison.transportBoundary_source

/-- Downgrading the strong extracted bridge from an unrestricted witness
recovers the weak extracted bridge exactly. -/
theorem toTransportBridgeData_toRawPairBridgeData_eq_toBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    W.toTransportBridgeData.toRawPairBridgeData = W.toBridgeData :=
  rfl

/-- The source admissible instance built by the unrestricted carrier
from the witness agrees with the lift of the extracted source
admissibility data, definitionally. -/
theorem sourceAdmissibleInstance_eq_toSourceAdmissibilityData
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    W.sourceAdmissibleInstance
      = W.toSourceAdmissibilityData.toAdmissibleInstance :=
  rfl

/-- The target admissible instance built by the unrestricted carrier
from the witness agrees with the lift of the extracted target
admissibility data, definitionally. -/
theorem targetAdmissibleInstance_eq_toTargetAdmissibilityData
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    W.targetAdmissibleInstance
      = W.toTargetAdmissibilityData.toAdmissibleInstance :=
  rfl

end OperatorKO7.LCELUnrestrictedTheorem.LCELUnrestrictedMathematicalWitness

namespace OperatorKO7.LCELUnrestrictedClassification

open OperatorKO7.LCELSchema
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELUnrestrictedTheorem
open OperatorKO7.LCELUnrestrictedExistence

/-- **LCEL unrestricted-witness refined classification biconditional.**

Genuine iff characterization: a raw pair admits an unrestricted
mathematical witness iff there is admissibility data on each side plus
a pairwise bridge. Strictly weaker on both directions than the
tautological `admitsUnrestrictedWitness_iff`, which packaged the whole
cross-instance mathematical support witness in a single Nonempty
component. -/
theorem admitsUnrestrictedWitness_iff_bridgeData
    (L₁ L₂ : FormalLCELInstance) :
    AdmitsLCELUnrestrictedWitness L₁ L₂
      ↔ Nonempty (LCELAdmissibilityData L₁)
          ∧ Nonempty (LCELAdmissibilityData L₂)
          ∧ Nonempty (LCELRawPairBridgeData L₁ L₂) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨W⟩
    exact ⟨⟨W.toSourceAdmissibilityData⟩,
      ⟨W.toTargetAdmissibilityData⟩,
      ⟨W.toBridgeData⟩⟩
  · rintro ⟨⟨A₁⟩, ⟨A₂⟩, ⟨bridge⟩⟩
    exact admitsUnrestrictedWitness_of_bridgeData A₁ A₂ bridge

/-- Forward direction of the refined iff: admission implies the three
separated-input Nonempties (admissibility on each side plus a pairwise
bridge). -/
theorem bridgeClassification_of_admitsUnrestrictedWitness
    {L₁ L₂ : FormalLCELInstance}
    (h : AdmitsLCELUnrestrictedWitness L₁ L₂) :
    Nonempty (LCELAdmissibilityData L₁)
      ∧ Nonempty (LCELAdmissibilityData L₂)
      ∧ Nonempty (LCELRawPairBridgeData L₁ L₂) :=
  (admitsUnrestrictedWitness_iff_bridgeData L₁ L₂).mp h

/-- **LCEL unrestricted-witness strong refined classification
biconditional.**

Dependent strong-route analogue of `admitsUnrestrictedWitness_iff_bridgeData`:
a raw pair admits an unrestricted witness iff there exist source-side and
target-side admissibility data packages together with a strong transport
bridge between those exact packages. -/
theorem admitsUnrestrictedWitness_iff_transportBridgeData
    (L₁ L₂ : FormalLCELInstance) :
    AdmitsLCELUnrestrictedWitness L₁ L₂
      ↔ ∃ A₁ : LCELAdmissibilityData L₁,
          ∃ A₂ : LCELAdmissibilityData L₂,
            Nonempty (LCELTransportBridgeData A₁ A₂) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨W⟩
    exact ⟨W.toSourceAdmissibilityData, W.toTargetAdmissibilityData,
      ⟨W.toTransportBridgeData⟩⟩
  · rintro ⟨A₁, A₂, ⟨bridge⟩⟩
    exact admitsUnrestrictedWitness_of_transportBridgeData A₁ A₂ bridge

/-- Forward direction of the strong refined classification: admission
implies the existence of source-side admissibility data, target-side
admissibility data, and a strong transport bridge between them. -/
theorem transportBridgeClassification_of_admitsUnrestrictedWitness
    {L₁ L₂ : FormalLCELInstance}
    (h : AdmitsLCELUnrestrictedWitness L₁ L₂) :
    ∃ A₁ : LCELAdmissibilityData L₁,
      ∃ A₂ : LCELAdmissibilityData L₂,
        Nonempty (LCELTransportBridgeData A₁ A₂) :=
  (admitsUnrestrictedWitness_iff_transportBridgeData L₁ L₂).mp h

end OperatorKO7.LCELUnrestrictedClassification
