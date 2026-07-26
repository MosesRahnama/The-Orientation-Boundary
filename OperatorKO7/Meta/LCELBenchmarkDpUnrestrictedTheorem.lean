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
# LCEL benchmark-to-DP finite correspondence

This module defines a bijection between two two-constructor sentence types and
uses it to populate the benchmark-to-DP LCEL correspondence records. Boundary,
annotation, and base-sentence transport use the nonconstant sentence map.
External-license and reimport-class transport act on proposition proofs and
return the target instances' supplied proofs.

The later witness and quasi-functor declarations are record constructions from
these finite correspondences and the imported admissibility packages. In
particular, the declarations establish inhabitation of the named LCEL record
types; they do not establish a semantic equivalence between an independently
defined benchmark execution relation and dependency-pair rewriting.
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

The two finite sentence types are related by the following constructor map:

- `.benchmarkBaseSentence ↦ .baseSystem`
- `.transformedWitnessSentence ↦ .licensedProjection`

The inverse below proves that this map is a bijection on these two finite
carriers. The map itself supplies no execution or rewriting semantics beyond
the meanings already assigned to the constructors by the imported instances. -/

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

/-! ### Constructor equations and nonconstancy -/

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

/-! ## Direct benchmark-to-DP correspondence records

The boundary, annotation, and base-sentence records use the finite sentence
map. The external-license and reimport-class records map proof inputs to the
target instances' supplied proofs. -/

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
the typed sentence translation; `annotate` is the identity on sentences in
the two imported instances. -/
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
the `annotate` and `decode` maps on both imported instances are identities,
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

/-! ## Pairwise bridge data

The stagewise-equivalence field is taken from
`benchmark_dpEmitter_lcelSupportComparisonWitness`; the strong-slot field is
the finite correspondence package defined above. -/

/-- Benchmark-to-DP raw pair bridge data. -/
def benchmark_dp_bridgeData :
    LCELRawPairBridgeData
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  strongSlot := benchmark_dp_strongSemanticSlotCorrespondence
  stagewise :=
    benchmark_dpEmitter_lcelSupportComparisonWitness.comparisonStagewise

/-! ## Transport-bridge data

This record combines the strong slot correspondence, the imported stagewise
equivalence, target-side support fields, and four coherence equations. -/

/-- Benchmark-to-DP route-semantics record containing the strong slot
correspondence, stagewise equivalence, and target-side support fields required
by the four transport helpers. -/
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

/-! ## Support and unrestricted-witness records

The support witness is produced by the generic route-semantics builder. Its
sentence-valued boundary, annotation, and base-sentence fields use the
nonconstant two-constructor map. Its proposition-valued license and reimport
fields transport supplied proofs. -/

/-- Benchmark-to-DP support witness constructed from
`benchmark_dp_routeSemanticsLiftData`. -/
def benchmark_dp_lcelMathematicalSupportWitness :
    LCELMathematicalSupportWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_routeSemanticsLiftData.toMathematicalSupportWitness

/-- Benchmark-to-DP unrestricted-witness record constructed by the generic
route-semantics lift. -/
def benchmark_dp_unrestrictedMathematicalWitness :
    LCELUnrestrictedMathematicalWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_routeSemanticsLiftData.toUnrestrictedMathematicalWitness

/-! ## Quasi-functor inhabitation from the supplied witness -/

/-- The supplied benchmark-to-DP witness yields an inhabited
`LCELUniversalQuasiFunctor` type. -/
theorem benchmark_dp_unrestricted_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        benchmark_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance
        benchmark_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance) :=
  benchmark_dp_routeSemanticsLiftData.lcel_unrestricted_structural_identity

/-- The supplied witness yields inhabited quasi-functor types in both
directions. -/
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

/-- Existence form of the quasi-functor construction, with source and target
instances equal to the two imported LCEL instances. -/
theorem benchmark_dp_existsStructuralIdentityFromRouteSemantics :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = benchmarkTransportLCELInstance
        ∧ A₂.instance_ = dpEmitterLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  benchmark_dp_routeSemanticsLiftData.lcel_exists_structural_identity

/-- The raw pair satisfies the library's `AdmitsLCELUnrestrictedWitness`
predicate through the route-semantics data. -/
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

/-! ## Quasi-functor built from the support witness

The following definitions apply the generic LCEL constructors to the supplied
admissibility data and support witness. -/

/-- Canonical benchmark-transport admissible instance. -/
private def benchmark_dp_sourceAdmissibleInstance :
    OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance :=
  benchmarkTransportLCELAdmissibilityData.toAdmissibleInstance

/-- Canonical native DP admissible instance. -/
private def benchmark_dp_targetAdmissibleInstance :
    OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance :=
  dpEmitterLCELAdmissibilityData.toAdmissibleInstance

/-- Quasi-functor record from benchmark transport to native DP constructed
from the two admissibility packages and the support witness. -/
def benchmark_dp_mathematical_universal_quasiFunctor :
    OperatorKO7.LCELUniversalTheorem.LCELUniversalQuasiFunctor
      benchmark_dp_sourceAdmissibleInstance
      benchmark_dp_targetAdmissibleInstance :=
  lcelUniversalQuasiFunctor_ofMathematicalComparison
    (A₁ := benchmark_dp_sourceAdmissibleInstance)
    (A₂ := benchmark_dp_targetAdmissibleInstance)
    benchmark_dp_lcelMathematicalSupportWitness

/-- Inhabitation of the quasi-functor type constructed from the support
witness. -/
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

These equations state that each transport function maps its distinguished
source support object to the corresponding distinguished target support
object. -/

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
