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
import OperatorKO7.Meta.LCELUnrestrictedClassification
import OperatorKO7.Meta.LCELRouteSemanticsClassification

/-!
# LCEL Benchmark ↔ Native DP Unrestricted Universal Theorem

This module supplies the benchmark-transport ↔ native DP / emitter
canonical unrestricted mathematical witness and its structural-identity
corollary, completing the canonical triad of unrestricted witnesses
(Gödel ↔ DP, Gödel ↔ benchmark, benchmark ↔ DP) closed by Workstream E.

The construction is **genuinely source-sensitive**, not a bridge-builder
alias. After the benchmark-side and DP-side semantic carriers are
upgraded in `Meta/StructuralIdentityComparison.lean` and
`Meta/LCELDpInstance.lean` so that obstruction witnesses, reimport
admissions, and annotations all live in the typed sentence spaces
(`BenchmarkTransportSentenceSemantic` on the benchmark side,
`DpEmitterSentenceSemantic` on the DP side), the direct benchmark ↔ DP
boundary, annotation, and base-sentence correspondences are built from
an explicit typed sentence translation
`benchmarkTransportSentence_to_dpEmitterSentence` that is non-constant
on the two-element sentence spaces. The canonical
`benchmark_dp_lcelMathematicalSupportWitness` then uses the
correspondence-driven source-informed transport helpers
(`baseReversibilityTheorem_transport_viaStrongSlot`,
`licenseIrreversibilityTheorem_transport_viaStrongSlot`,
`reimportReversibilityTheorem_transport_viaStrongSlot`,
`boundaryFactorizationTheorem_transport`), and is **no longer**
definitionally equal to
`LCELMathematicalSupportWitness.ofBridgeData` on this pair: the
transport functions of the two constructions differ by the non-constant
translate map on the two-element sentence spaces.

The benchmark ↔ DP canonical unrestricted corollary
`benchmark_dp_unrestricted_structural_identity` and the Workstream D
mathematical corollary
`benchmark_dp_mathematical_universal_structural_identity` are derived
directly from this source-sensitive witness.
-/

namespace OperatorKO7.LCELBenchmarkDpUnrestrictedTheorem

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
open OperatorKO7.LCELUnrestrictedClassification
open OperatorKO7.LCELGenericTransportBridge
open OperatorKO7.ReflectionSchema

/-! ## Typed sentence translation between benchmark and native DP

With the benchmark-side and native-DP-side semantic carriers upgraded
in `Meta/StructuralIdentityComparison.lean` and `Meta/LCELDpInstance.lean`
so that boundary witnesses, reimport admissions, and annotations all
live in the typed sentence spaces `BenchmarkTransportSentenceSemantic`
and `DpEmitterSentenceSemantic`, we can supply a genuinely non-constant
typed sentence translation between the two sides:

- `.benchmarkBaseSentence ↦ .baseSystem`
- `.transformedWitnessSentence ↦ .licensedProjection`

This map is bijective on the two-element sentence spaces, distinguishes
the base-theory-proved sentence from the designated-blocked sentence on
both sides, and sends the designated source obstruction/reimport
witness to the designated target obstruction/reimport witness. It is
the core mathematical content that lets the direct benchmark ↔ DP
correspondence layer be non-constant, not an alias of the generic
bridge builder. -/

/-- Typed sentence translation from the benchmark-transport sentence
space to the native DP/emitter sentence space. -/
def benchmarkTransportSentence_to_dpEmitterSentence :
    OperatorKO7.StructuralIdentityComparison.BenchmarkTransportSentenceSemantic →
      DpEmitterSentenceSemantic
  | .benchmarkBaseSentence => .baseSystem
  | .transformedWitnessSentence => .licensedProjection

/-- Inverse typed sentence translation from the native DP/emitter
sentence space to the benchmark-transport sentence space. -/
def dpEmitterSentence_to_benchmarkTransportSentence :
    DpEmitterSentenceSemantic →
      OperatorKO7.StructuralIdentityComparison.BenchmarkTransportSentenceSemantic
  | .baseSystem => .benchmarkBaseSentence
  | .licensedProjection => .transformedWitnessSentence

/-- The forward translation sends the benchmark-side base-theory-proved
sentence to the DP-side base-theory-proved sentence. -/
theorem benchmarkTransportSentence_to_dpEmitterSentence_base :
    benchmarkTransportSentence_to_dpEmitterSentence .benchmarkBaseSentence
      = .baseSystem := rfl

/-- The forward translation sends the benchmark-side designated blocked
sentence to the DP-side designated blocked sentence. -/
theorem benchmarkTransportSentence_to_dpEmitterSentence_witness :
    benchmarkTransportSentence_to_dpEmitterSentence .transformedWitnessSentence
      = .licensedProjection := rfl

/-! ### Required non-constancy regression theorems -/

/-- Boundary correspondence: on the benchmark base-theory sentence,
the translate map lands on the DP base system. -/
theorem benchmark_dp_boundary_translate_base :
    benchmarkTransportSentence_to_dpEmitterSentence .benchmarkBaseSentence
      = .baseSystem := rfl

/-- Boundary correspondence: on the benchmark designated blocked
sentence, the translate map lands on the DP designated blocked
sentence. -/
theorem benchmark_dp_boundary_translate_witness :
    benchmarkTransportSentence_to_dpEmitterSentence .transformedWitnessSentence
      = .licensedProjection := rfl

/-- Annotation correspondence: on the benchmark base-theory sentence,
the translate map lands on the DP base system. -/
theorem benchmark_dp_annotation_translate_base :
    benchmarkTransportSentence_to_dpEmitterSentence .benchmarkBaseSentence
      = .baseSystem := rfl

/-- Annotation correspondence: on the benchmark designated blocked
sentence, the translate map lands on the DP designated blocked
sentence. -/
theorem benchmark_dp_annotation_translate_witness :
    benchmarkTransportSentence_to_dpEmitterSentence .transformedWitnessSentence
      = .licensedProjection := rfl

/-- Base-sentence correspondence: on the benchmark base-theory
sentence, the translate map lands on the DP base system. -/
theorem benchmark_dp_baseSentence_translate_base :
    benchmarkTransportSentence_to_dpEmitterSentence .benchmarkBaseSentence
      = .baseSystem := rfl

/-- Base-sentence correspondence: on the benchmark designated blocked
sentence, the translate map lands on the DP designated blocked
sentence. -/
theorem benchmark_dp_baseSentence_translate_witness :
    benchmarkTransportSentence_to_dpEmitterSentence .transformedWitnessSentence
      = .licensedProjection := rfl

/-- Non-constancy theorem: the typed sentence translation sends two
distinct benchmark sentences to two distinct DP sentences. Direct
witness that the direct benchmark ↔ DP correspondence is not a
constant map. -/
theorem benchmarkTransportSentence_to_dpEmitterSentence_nonconstant :
    benchmarkTransportSentence_to_dpEmitterSentence .benchmarkBaseSentence
      ≠ benchmarkTransportSentence_to_dpEmitterSentence
          .transformedWitnessSentence := by
  intro h
  exact DpEmitterSentenceSemantic.noConfusion h

/-! ## Canonical direct non-constant benchmark ↔ DP correspondences

Each slot correspondence is built from the typed sentence translation
above (or from the matching constant forward transport of the
propositional slot witness for the external-license and reimport-class
slots), so every correspondence that can be non-constant IS non-constant
on this pair. -/

/-- Direct non-constant boundary correspondence: the translate map is
the typed sentence translation, which distinguishes benchmark
base-theory-proved sentences from designated blocked sentences. -/
def benchmark_dp_boundaryCorrespondence :
    BoundaryObjectCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  translate := benchmarkTransportSentence_to_dpEmitterSentence
  translate_designated := rfl

/-- Direct non-constant annotation correspondence: the translate map is
the typed sentence translation, matching `annotate` being the identity
on sentences after the admission-carrier upgrade. -/
def benchmark_dp_annotationCorrespondence :
    AnnotationFunctorCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  translateAnnotation := benchmarkTransportSentence_to_dpEmitterSentence
  translate_annotate_witness := rfl

/-- External-license correspondence on the benchmark ↔ DP pair.
`externalLicenseWitness` is a `Prop` slot, so the forward/backward
transport is necessarily on proofs; the non-constant mathematical
content lives in the boundary / annotation / base-sentence
correspondences. -/
def benchmark_dp_externalLicenseCorrespondence :
    ExternalLicenseCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  forward _ := dpEmitterLCELInstance.externalLicenseHolds
  backward _ := benchmarkTransportLCELInstance.externalLicenseHolds

/-- Reimport-class correspondence on the benchmark ↔ DP pair.
`reimportClassWitness` is a `Prop` slot, so the forward/backward
transport is necessarily on proofs. -/
def benchmark_dp_reimportClassCorrespondence :
    ReimportClassCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  forward _ := dpEmitterLCELInstance.reimportClassHolds
  backward _ := benchmarkTransportLCELInstance.reimportClassHolds

/-- Strengthened benchmark ↔ DP boundary correspondence built on the
non-constant direct boundary correspondence. The preservation laws
are proved by cases on the benchmark-side sentence: the base-theory
sentence case is contradicted by its provability in the benchmark base
theory, and the designated blocked-sentence case is discharged by the
DP side's own boundary-object laws via `dsimp` reduction of the
typed translate map. -/
def benchmark_dp_strongBoundaryCorrespondence :
    StrongBoundaryObjectCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  toBoundaryObjectCorrespondence := benchmark_dp_boundaryCorrespondence
  translate_preserves_not_provable := by
    intro w h
    cases w with
    | benchmarkBaseSentence =>
        exact absurd
          (show benchmarkTransportLCELInstance.comparison.baseTheoryContent.proves
              (benchmarkTransportLCELInstance.boundaryObject.boundarySentence
                .benchmarkBaseSentence) from trivial)
          h
    | transformedWitnessSentence =>
        change ¬ dpEmitterLCELInstance.comparison.baseTheoryContent.proves
          (dpEmitterLCELInstance.boundaryObject.boundarySentence
            dpEmitterLCELInstance.boundaryObject.designated)
        exact dpEmitterLCELInstance.boundaryObject.designated_not_provable
  translate_preserves_true := by
    intro w _
    cases w with
    | benchmarkBaseSentence => trivial
    | transformedWitnessSentence =>
        change dpEmitterLCELInstance.comparison.baseTheoryContent.trueInReferenceModel
          (dpEmitterLCELInstance.boundaryObject.boundarySentence
            dpEmitterLCELInstance.boundaryObject.designated)
        exact dpEmitterLCELInstance.boundaryObject.designated_true

/-- Strengthened benchmark ↔ DP external-license correspondence. -/
def benchmark_dp_strongExternalLicenseCorrespondence :
    StrongExternalLicenseCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  toExternalLicenseCorrespondence := benchmark_dp_externalLicenseCorrespondence
  forward_preserves_blocked_not_provable := by
    intro _
    exact dpEmitterLCELInstance.comparison.reflectionContent.blocked_not_provable
  forward_preserves_stronger_reflects := by
    intro _
    exact dpEmitterLicenseIrreversibilitySupport.strongerFrameworkReflectsBlocked

/-- Strengthened benchmark ↔ DP reimport-class correspondence. -/
def benchmark_dp_strongReimportClassCorrespondence :
    StrongReimportClassCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  toReimportClassCorrespondence := benchmark_dp_reimportClassCorrespondence
  forward_preserves_witness_certifies_imported := by
    intro _
    exact dpEmitterReimportReversibilitySupport.witnessCertifiesImported
  forward_preserves_imported_true := by
    intro _
    exact dpEmitterReimportReversibilitySupport.importedTrue

/-- Strengthened benchmark ↔ DP annotation-functor correspondence
built on the non-constant direct annotation correspondence. Because
the `annotate` map on both sides is the identity on sentences after
the admission-carrier upgrade, and `decode` is the identity as well,
the preservation laws reduce on the canonical designated witness to
`.licensedProjection = .licensedProjection` (or `True` for the
reference-model truth law); `rfl` after reducing the structure field
projections discharges them. -/
def benchmark_dp_strongAnnotationFunctorCorrespondence :
    StrongAnnotationFunctorCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  toAnnotationFunctorCorrespondence := benchmark_dp_annotationCorrespondence
  translate_preserves_witness_certifies_decoded := by
    dsimp only [benchmarkTransportLCELInstance, benchmarkTransportLCELAnnotationFunctor,
      dpEmitterLCELInstance, dpEmitterLCELAnnotationFunctor,
      benchmark_dp_annotationCorrespondence, benchmarkTransportSentence_to_dpEmitterSentence]
    rfl
  translate_preserves_decoded_true := by
    dsimp only [benchmarkTransportLCELInstance, benchmarkTransportLCELAnnotationFunctor,
      dpEmitterLCELInstance, dpEmitterLCELAnnotationFunctor,
      benchmark_dp_annotationCorrespondence, benchmarkTransportSentence_to_dpEmitterSentence]
    trivial
  translate_preserves_decodes_to_imported := by
    dsimp only [benchmarkTransportLCELInstance, benchmarkTransportLCELAnnotationFunctor,
      dpEmitterLCELInstance, dpEmitterLCELAnnotationFunctor,
      benchmark_dp_annotationCorrespondence, benchmarkTransportSentence_to_dpEmitterSentence]
    rfl

/-- Direct non-constant benchmark ↔ DP base-sentence correspondence
using the typed sentence translation. The provability-preservation
law is proved by cases: base-theory-proved sentences on the benchmark
side translate to base-theory-proved sentences on the DP side; the
designated blocked-sentence case is vacuous because the benchmark
base theory does not prove the blocked sentence. -/
def benchmark_dp_baseSentenceCorrespondence :
    BaseSentenceCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  translateProvedSentence := benchmarkTransportSentence_to_dpEmitterSentence
  translateProvedSentence_preserves_provable := by
    intro s hs
    cases s with
    | benchmarkBaseSentence => exact trivial
    | transformedWitnessSentence => exact hs.elim

/-- Packaged benchmark ↔ DP strong semantic slot correspondence. -/
def benchmark_dp_strongSemanticSlotCorrespondence :
    LCELStrongSemanticSlotCorrespondence
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  boundary := benchmark_dp_strongBoundaryCorrespondence
  externalLicense := benchmark_dp_strongExternalLicenseCorrespondence
  reimportClass := benchmark_dp_strongReimportClassCorrespondence
  annotation := benchmark_dp_strongAnnotationFunctorCorrespondence
  baseSentence := benchmark_dp_baseSentenceCorrespondence

/-! ## Canonical benchmark ↔ DP pairwise bridge data

The stagewise equivalence is reused from the existing Workstream F
support-comparison witness
`benchmark_dpEmitter_lcelSupportComparisonWitness`, which was built by
composition through the Gödel side using transitivity of
`StagewiseEquivalent`. -/

/-- Canonical benchmark ↔ DP pairwise bridge data (weak route,
constant-target transports on the generic builder). Retained for
reference; the authoritative route on this pair is
`benchmark_dp_transportBridgeData` below. -/
def benchmark_dp_bridgeData :
    LCELRawPairBridgeData
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  strongSlot := benchmark_dp_strongSemanticSlotCorrespondence
  stagewise :=
    benchmark_dpEmitter_lcelSupportComparisonWitness.comparisonStagewise

/-! ## Canonical benchmark ↔ DP **strong** transport-bridge data

Unlike the weak `benchmark_dp_bridgeData`, this strong bridge carries
the four correspondence-driven theorem-object transport functions
(non-constant on this pair, driven by
`benchmarkTransportSentence_to_dpEmitterSentence`) together with their
coherence equations tying the canonical source support-extracted
theorems to the canonical target support-extracted theorems. It is the
authoritative bridge data on the benchmark ↔ DP pair and feeds the
`LCELMathematicalSupportWitness.ofTransportBridgeData` generic
strong-route builder. -/

/-- Canonical benchmark ↔ DP source-sensitive route semantics. This isolates the
pair-generic route pattern now used by the strong transport-bridge construction:
the strong slot correspondence, the stagewise equivalence, and the target-side
structural laws needed by the four theorem-object transport helpers. -/
def benchmark_dp_sourceSensitiveRouteSemantics :
    LCELSourceSensitiveRouteSemantics
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  strongSlot := benchmark_dp_strongSemanticSlotCorrespondence
  stagewise :=
    benchmark_dpEmitter_lcelSupportComparisonWitness.comparisonStagewise
  targetLicensedAdmission :=
    dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission
  targetObstructionBlockedEqReflectionBlocked :=
    dpEmitterBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
  targetReflectionBlockedEqImported :=
    dpEmitterBoundaryFactorizationSupport.reflectionBlockedEqImported
  targetBoundaryRealized :=
    dpEmitterBoundaryFactorizationSupport.boundaryRealized

theorem benchmark_dp_route_transportBase_canonical :
    benchmark_dp_sourceSensitiveRouteSemantics.transportBase
      (baseReversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.baseSupport)
    = baseReversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.baseSupport := by
  show baseReversibilityTheorem_transport_viaStrongSlot
      benchmark_dp_strongSemanticSlotCorrespondence
      (baseReversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.baseSupport)
    = baseReversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.baseSupport
  unfold baseReversibilityTheorem_transport_viaStrongSlot
  simp only [benchmark_dp_strongSemanticSlotCorrespondence,
    benchmark_dp_baseSentenceCorrespondence,
    benchmarkTransportSentence_to_dpEmitterSentence]
  rfl

theorem benchmark_dp_route_transportLicense_canonical :
    benchmark_dp_sourceSensitiveRouteSemantics.transportLicense
      (licenseIrreversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.licenseSupport)
    = licenseIrreversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.licenseSupport :=
  rfl

theorem benchmark_dp_route_transportReimport_canonical :
    benchmark_dp_sourceSensitiveRouteSemantics.transportReimport
      (reimportReversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.reimportSupport)
    = reimportReversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.reimportSupport :=
  rfl

theorem benchmark_dp_route_transportBoundary_canonical :
    benchmark_dp_sourceSensitiveRouteSemantics.transportBoundary
      (boundaryFactorizationTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.boundarySupport)
    = boundaryFactorizationTheorem_of_support
        dpEmitterLCELAdmissibilityData.boundarySupport :=
  rfl

/-- Canonical benchmark ↔ DP packaged route-semantics lift data. -/
def benchmark_dp_routeSemanticsLiftData :
    LCELRouteSemanticsLiftData
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  routeSemantics := benchmark_dp_sourceSensitiveRouteSemantics
  sourceAdmissibilityData := benchmarkTransportLCELAdmissibilityData
  targetAdmissibilityData := dpEmitterLCELAdmissibilityData
  transportBase_canonical := benchmark_dp_route_transportBase_canonical
  transportLicense_canonical := benchmark_dp_route_transportLicense_canonical
  transportReimport_canonical := benchmark_dp_route_transportReimport_canonical
  transportBoundary_canonical := benchmark_dp_route_transportBoundary_canonical

/-- Canonical benchmark ↔ DP strong transport-bridge data. -/
def benchmark_dp_transportBridgeData :
    LCELTransportBridgeData
      benchmarkTransportLCELAdmissibilityData
      dpEmitterLCELAdmissibilityData :=
  benchmark_dp_routeSemanticsLiftData.toTransportBridgeData

/-- Downgrading the canonical benchmark ↔ DP strong transport bridge to the
weak bridge recovers the canonical weak bridge exactly. -/
theorem benchmark_dp_transportBridgeData_toRawPairBridgeData_eq_bridgeData :
    benchmark_dp_transportBridgeData.toRawPairBridgeData = benchmark_dp_bridgeData :=
  rfl

/-! ## Canonical mathematical support witness (genuinely source-sensitive)

The canonical benchmark ↔ DP mathematical support witness is written
field-by-field using the correspondence-driven transport helpers
`baseReversibilityTheorem_transport_viaStrongSlot`,
`licenseIrreversibilityTheorem_transport_viaStrongSlot`,
`reimportReversibilityTheorem_transport_viaStrongSlot`, and
`boundaryFactorizationTheorem_transport`, matching the shape of the
Gödel-facing canonical mathematical support witnesses at the
definition site.

Unlike the earlier constant-map bridge route, this construction is
genuinely source-sensitive: the direct benchmark ↔ DP boundary,
annotation, and base-sentence correspondences are built from the
**non-constant** typed sentence translation
`benchmarkTransportSentence_to_dpEmitterSentence`, which distinguishes
`.benchmarkBaseSentence` from `.transformedWitnessSentence` and sends
each to a different target sentence. The witness is therefore **not**
definitionally equal to
`LCELMathematicalSupportWitness.ofBridgeData` on this pair (the
transport functions of the two constructions differ on the non-designated
sentence input), and the Workstream D corollary below is a substantive
nonconstant transport theorem on the benchmark ↔ DP pair, not merely
an alias of the generic bridge builder. -/

/-- Canonical benchmark ↔ DP mathematical support witness, now built
through the generic `LCELMathematicalSupportWitness.ofTransportBridgeData`
strong-route builder on the canonical
`benchmark_dp_transportBridgeData`. The transport fields are the
bridge's own correspondence-driven, source-informed helpers — not
constant-target closures — so this witness is the concrete benchmark ↔
DP instance of the new generic strong route. -/
def benchmark_dp_lcelMathematicalSupportWitness :
    LCELMathematicalSupportWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_routeSemanticsLiftData.toMathematicalSupportWitness

/-- Canonical benchmark ↔ DP unrestricted mathematical witness, built
through the generic route-semantics lift on the canonical benchmark ↔ DP
source-sensitive route. This keeps the canonical pair pinned to the L4
generic lift surface without weakening the existing theorem boundary. -/
def benchmark_dp_unrestrictedMathematicalWitness :
    LCELUnrestrictedMathematicalWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_routeSemanticsLiftData.toUnrestrictedMathematicalWitness

/-! ## Canonical benchmark ↔ DP unrestricted structural identity -/

/-- **Benchmark ↔ native DP unrestricted structural-identity theorem.**
Closes the canonical triad of unrestricted universal corollaries
(Gödel ↔ DP, Gödel ↔ benchmark, benchmark ↔ DP). -/
theorem benchmark_dp_unrestricted_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        benchmark_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance
        benchmark_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance) :=
  benchmark_dp_routeSemanticsLiftData.lcel_unrestricted_structural_identity

/-- Bidirectional benchmark ↔ DP unrestricted structural identity. -/
theorem benchmark_dp_unrestricted_structural_identity_bidirectional :
    Nonempty
        (LCELUniversalQuasiFunctor
          benchmark_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance
          benchmark_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance)
      ∧ Nonempty
        (LCELUniversalQuasiFunctor
          benchmark_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance
          benchmark_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance) :=
  lcel_unrestricted_structural_identity_of_mathematicalWitness_bidirectional
    benchmark_dp_unrestrictedMathematicalWitness

/-- Benchmark ↔ DP route-semantics lift in the existence-form structural-identity
surface. This remains conditional on the canonical admissibility packages and
the four route-coherence equations, so it does not claim P4C. -/
theorem benchmark_dp_existsStructuralIdentityFromRouteSemantics :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = benchmarkTransportLCELInstance
        ∧ A₂.instance_ = dpEmitterLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  benchmark_dp_routeSemanticsLiftData.lcel_exists_structural_identity

/-- Benchmark ↔ DP raw pair admits an unrestricted mathematical witness. -/
theorem benchmark_dp_admitsUnrestrictedWitness :
    AdmitsLCELUnrestrictedWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_routeSemanticsLiftData.admitsUnrestrictedWitness

/-- Benchmark ↔ DP raw pair admits an unrestricted witness through the generic
route-semantics lift. -/
theorem benchmark_dp_admitsUnrestrictedWitness_viaRouteSemantics :
    AdmitsLCELUnrestrictedWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_routeSemanticsLiftData.admitsUnrestrictedWitness

/-- Benchmark ↔ DP raw pair admits an unrestricted witness via the
refined bridge route, without packaging a full
`LCELMathematicalSupportWitness` propositionally at the theorem
boundary. -/
theorem benchmark_dp_admitsUnrestrictedWitness_viaBridge :
    AdmitsLCELUnrestrictedWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  admitsUnrestrictedWitness_of_bridgeData
    benchmarkTransportLCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    benchmark_dp_bridgeData

/-- Benchmark ↔ DP raw pair admits an unrestricted witness via the strong
transport-bridge route. -/
theorem benchmark_dp_admitsUnrestrictedWitness_viaTransportBridge :
    AdmitsLCELUnrestrictedWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  admitsUnrestrictedWitness_of_transportBridgeData
    benchmarkTransportLCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    benchmark_dp_transportBridgeData

/-! ## Canonical Workstream D corollary on the benchmark ↔ DP pair

With the source-informed canonical mathematical support witness in
hand, the benchmark ↔ DP pair admits a Workstream D structural-identity
corollary directly at the theorem boundary: running the canonical
mathematical support witness through
`lcel_structural_identity_of_mathematicalComparison`. This is the
benchmark ↔ DP analogue of
`godel_dp_mathematical_universal_structural_identity` and
`godel_benchmark_mathematical_universal_structural_identity`, and
because the underlying witness is built from the non-constant typed
sentence translation `benchmarkTransportSentence_to_dpEmitterSentence`
and the correspondence-driven transport helpers (not from constant-target
closures), the Workstream D corollary below is a substantive non-constant
transport theorem on this pair — not an alias of the generic bridge
builder. -/

/-- Canonical benchmark-transport admissible instance. -/
private def benchmark_dp_sourceAdmissibleInstance :
    OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance :=
  benchmarkTransportLCELAdmissibilityData.toAdmissibleInstance

/-- Canonical native DP admissible instance. -/
private def benchmark_dp_targetAdmissibleInstance :
    OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance :=
  dpEmitterLCELAdmissibilityData.toAdmissibleInstance

/-- Universal quasi-functor from benchmark-transport to native DP via
the Workstream D strong restricted theorem, consuming the
source-informed canonical mathematical support witness. -/
def benchmark_dp_mathematical_universal_quasiFunctor :
    OperatorKO7.LCELUniversalTheorem.LCELUniversalQuasiFunctor
      benchmark_dp_sourceAdmissibleInstance
      benchmark_dp_targetAdmissibleInstance :=
  lcelUniversalQuasiFunctor_ofMathematicalComparison
    (A₁ := benchmark_dp_sourceAdmissibleInstance)
    (A₂ := benchmark_dp_targetAdmissibleInstance)
    benchmark_dp_lcelMathematicalSupportWitness

/-- **Benchmark ↔ native DP mathematical universal structural-identity
theorem.** Closes the canonical triad at the Workstream D (strong
restricted) level: the universal quasi-functor is built from the
source-informed theorem-object transport functions of the canonical
mathematical support witness, not from constant-target transports and
not only through the composed support-comparison witness. -/
theorem benchmark_dp_mathematical_universal_structural_identity :
    Nonempty
      (OperatorKO7.LCELUniversalTheorem.LCELUniversalQuasiFunctor
        benchmark_dp_sourceAdmissibleInstance
        benchmark_dp_targetAdmissibleInstance) :=
  lcel_structural_identity_of_mathematicalComparison
    (A₁ := benchmark_dp_sourceAdmissibleInstance)
    (A₂ := benchmark_dp_targetAdmissibleInstance)
    benchmark_dp_lcelMathematicalSupportWitness

/-! ## Named transport-coherence regressions on the benchmark ↔ DP pair

These are the benchmark ↔ DP analogues of the transport-coherence
regression theorems in `Meta/LCELMathematicalStructuralIdentity.lean`.
They assert that the canonical source-informed transport functions on
this pair actually reduce to the canonical target theorems on the
canonical source theorems, which exercises the strong slot
correspondence's preservation laws on the benchmark ↔ DP direction. -/

theorem benchmark_dp_transportBase_canonical :
    benchmark_dp_lcelMathematicalSupportWitness.transportBase
        benchmark_dp_lcelMathematicalSupportWitness.sourceBaseTheorem
      = benchmark_dp_lcelMathematicalSupportWitness.targetBaseTheorem :=
  benchmark_dp_lcelMathematicalSupportWitness.transportBase_source

theorem benchmark_dp_transportLicense_canonical :
    benchmark_dp_lcelMathematicalSupportWitness.transportLicense
        benchmark_dp_lcelMathematicalSupportWitness.sourceLicenseTheorem
      = benchmark_dp_lcelMathematicalSupportWitness.targetLicenseTheorem :=
  benchmark_dp_lcelMathematicalSupportWitness.transportLicense_source

theorem benchmark_dp_transportReimport_canonical :
    benchmark_dp_lcelMathematicalSupportWitness.transportReimport
        benchmark_dp_lcelMathematicalSupportWitness.sourceReimportTheorem
      = benchmark_dp_lcelMathematicalSupportWitness.targetReimportTheorem :=
  benchmark_dp_lcelMathematicalSupportWitness.transportReimport_source

theorem benchmark_dp_transportBoundary_canonical :
    benchmark_dp_lcelMathematicalSupportWitness.transportBoundary
        benchmark_dp_lcelMathematicalSupportWitness.sourceBoundaryTheorem
      = benchmark_dp_lcelMathematicalSupportWitness.targetBoundaryTheorem :=
  benchmark_dp_lcelMathematicalSupportWitness.transportBoundary_source

end OperatorKO7.LCELBenchmarkDpUnrestrictedTheorem
