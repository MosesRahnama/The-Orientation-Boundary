import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELUniversalTheorem

/-!
# LCEL Benchmark-Transport ↔ Native DP Comparison Witness

Workstream F of the LCEL universal-theorem roadmap: a direct support
comparison witness between the benchmark-transport LCEL instance and the
native DP / emitter LCEL instance, and the corresponding universal
structural-identity corollary via genuine source-to-target transport.

The witness is built by composing the two existing canonical witnesses
`godel_benchmark_lcelSupportComparisonWitness` and
`godel_dpEmitter_lcelSupportComparisonWitness` through the Gödel side, using
transitivity of `StagewiseEquivalent` and of `Iff`. Canonical support
records on both sides are reused from the existing admissibility packages.

This is an internal-consistency theorem: it certifies that the benchmark-
transport layer and the native DP / emitter layer present the same
substrate story on the canonical support-record level, without routing the
comparison through the Gödel-side canonical instance.
-/

namespace OperatorKO7.LCELBenchmarkDpComparison

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema

/-- Transitivity of `StagewiseEquivalent` on the six-step structural profile. -/
private theorem stagewiseEquivalent_trans
    {P Q R : SixStepStructuralProfile}
    (hPQ : StagewiseEquivalent P Q) (hQR : StagewiseEquivalent Q R) :
    StagewiseEquivalent P R := by
  intro s
  exact (hPQ s).trans (hQR s)

/-- Support-comparison witness between the benchmark-transport LCEL instance
and the native DP / emitter LCEL instance, obtained by composing through the
Gödel side: first transport from benchmark-transport back to Gödel via
`godel_benchmark_lcelSupportComparisonWitness.symm`, then forward from Gödel
to the native DP / emitter via
`godel_dpEmitter_lcelSupportComparisonWitness`. -/
def benchmark_dpEmitter_lcelSupportComparisonWitness :
    LCELSupportComparisonWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  comparisonStagewise :=
    stagewiseEquivalent_trans
      (StagewiseEquivalent.symm
        godel_benchmark_lcelSupportComparisonWitness.comparisonStagewise)
      godel_dpEmitter_lcelSupportComparisonWitness.comparisonStagewise
  externalLicenseEquivalent :=
    Iff.intro
      (fun _ => dpEmitterLCELInstance.externalLicenseHolds)
      (fun _ => benchmarkTransportLCELInstance.externalLicenseHolds)
  reimportClassEquivalent :=
    Iff.intro
      (fun _ => dpEmitterLCELInstance.reimportClassHolds)
      (fun _ => benchmarkTransportLCELInstance.reimportClassHolds)
  baseLayerSupportEquivalent :=
    Iff.intro
      (fun _ => dpEmitter_semanticBaseLayerSupport)
      (fun _ => benchmarkTransport_semanticBaseLayerSupport)
  licenseTransferSupportEquivalent :=
    Iff.intro
      (fun _ => dpEmitter_semanticLicenseTransferSupport)
      (fun _ => benchmarkTransport_semanticLicenseTransferSupport)
  reimportTransferSupportEquivalent :=
    Iff.intro
      (fun _ => dpEmitter_semanticReimportTransferSupport)
      (fun _ => benchmarkTransport_semanticReimportTransferSupport)
  sourceBaseSupport := benchmarkTransportBaseReversibilitySupport
  targetBaseSupport := dpEmitterBaseReversibilitySupport
  sourceLicenseSupport := benchmarkTransportLicenseIrreversibilitySupport
  targetLicenseSupport := dpEmitterLicenseIrreversibilitySupport
  sourceReimportSupport := benchmarkTransportReimportReversibilitySupport
  targetReimportSupport := dpEmitterReimportReversibilitySupport
  sourceBoundarySupport := benchmarkTransportBoundaryFactorizationSupport
  targetBoundarySupport := dpEmitterBoundaryFactorizationSupport
  baseSupportEquivalent :=
    Iff.intro
      (fun _ =>
        ⟨dpEmitterBaseReversibilitySupport.internalSentenceProved,
          dpEmitterBaseReversibilitySupport.boundaryRealized⟩)
      (fun _ =>
        ⟨benchmarkTransportBaseReversibilitySupport.internalSentenceProved,
          benchmarkTransportBaseReversibilitySupport.boundaryRealized⟩)
  licenseSupportEquivalent :=
    Iff.intro
      (fun _ =>
        ⟨dpEmitterLicenseIrreversibilitySupport.strongerFrameworkReflectsBlocked,
         dpEmitterLicenseIrreversibilitySupport.externalLicenseHolds,
         dpEmitterLicenseIrreversibilitySupport.blockedNotProvable,
         dpEmitterLicenseIrreversibilitySupport.blockedTrue,
         dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission⟩)
      (fun _ =>
        ⟨benchmarkTransportLicenseIrreversibilitySupport.strongerFrameworkReflectsBlocked,
         benchmarkTransportLicenseIrreversibilitySupport.externalLicenseHolds,
         benchmarkTransportLicenseIrreversibilitySupport.blockedNotProvable,
         benchmarkTransportLicenseIrreversibilitySupport.blockedTrue,
         benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission⟩)
  reimportSupportEquivalent :=
    Iff.intro
      (fun _ =>
        ⟨dpEmitterReimportReversibilitySupport.witnessCertifiesBlocked,
         dpEmitterReimportReversibilitySupport.reimportClassHolds,
         dpEmitterReimportReversibilitySupport.annotationRealized,
         dpEmitterReimportReversibilitySupport.witnessCertifiesImported,
         dpEmitterReimportReversibilitySupport.importedTrue⟩)
      (fun _ =>
        ⟨benchmarkTransportReimportReversibilitySupport.witnessCertifiesBlocked,
         benchmarkTransportReimportReversibilitySupport.reimportClassHolds,
         benchmarkTransportReimportReversibilitySupport.annotationRealized,
         benchmarkTransportReimportReversibilitySupport.witnessCertifiesImported,
         benchmarkTransportReimportReversibilitySupport.importedTrue⟩)
  boundarySupportEquivalent :=
    Iff.intro
      (fun _ =>
        ⟨⟨dpEmitterBoundaryFactorizationSupport.visibleSupport.witnessCertifiesBlocked,
          dpEmitterBoundaryFactorizationSupport.visibleSupport.reimportClassHolds,
          dpEmitterBoundaryFactorizationSupport.visibleSupport.annotationRealized,
          dpEmitterBoundaryFactorizationSupport.visibleSupport.witnessCertifiesImported,
          dpEmitterBoundaryFactorizationSupport.visibleSupport.importedTrue⟩,
         ⟨dpEmitterBoundaryFactorizationSupport.sensitiveSupport.strongerFrameworkReflectsBlocked,
          dpEmitterBoundaryFactorizationSupport.sensitiveSupport.externalLicenseHolds,
          dpEmitterBoundaryFactorizationSupport.sensitiveSupport.blockedNotProvable,
          dpEmitterBoundaryFactorizationSupport.sensitiveSupport.blockedTrue,
          dpEmitterBoundaryFactorizationSupport.sensitiveSupport.blockedLicensedAdmission⟩,
         dpEmitterBoundaryFactorizationSupport.boundaryRealized⟩)
      (fun _ =>
        ⟨⟨benchmarkTransportBoundaryFactorizationSupport.visibleSupport.witnessCertifiesBlocked,
          benchmarkTransportBoundaryFactorizationSupport.visibleSupport.reimportClassHolds,
          benchmarkTransportBoundaryFactorizationSupport.visibleSupport.annotationRealized,
          benchmarkTransportBoundaryFactorizationSupport.visibleSupport.witnessCertifiesImported,
          benchmarkTransportBoundaryFactorizationSupport.visibleSupport.importedTrue⟩,
         ⟨benchmarkTransportBoundaryFactorizationSupport.sensitiveSupport.strongerFrameworkReflectsBlocked,
          benchmarkTransportBoundaryFactorizationSupport.sensitiveSupport.externalLicenseHolds,
          benchmarkTransportBoundaryFactorizationSupport.sensitiveSupport.blockedNotProvable,
          benchmarkTransportBoundaryFactorizationSupport.sensitiveSupport.blockedTrue,
          benchmarkTransportBoundaryFactorizationSupport.sensitiveSupport.blockedLicensedAdmission⟩,
         benchmarkTransportBoundaryFactorizationSupport.boundaryRealized⟩)

/-! ## Universal corollary from the composed witness -/

/-- Admissibility-comparison witness between the benchmark-transport admissible
instance and the native DP / emitter admissible instance, built by composition
through the Gödel side. -/
def benchmark_dp_admissibleLCELComparisonWitness :
    AdmissibleLCELComparisonWitness
      benchmarkTransportAdmissibleLCELInstance
      dpEmitterAdmissibleLCELInstance :=
  benchmark_dpEmitter_lcelSupportComparisonWitness

/-- Universal quasi-functor from benchmark-transport to native DP / emitter,
via genuine source-to-target transport through the composed canonical
support-comparison witness. -/
def benchmark_dp_universal_quasiFunctor :
    LCELUniversalQuasiFunctor
      benchmarkTransportAdmissibleLCELInstance
      dpEmitterAdmissibleLCELInstance :=
  lcelUniversalQuasiFunctor_ofComparison
    benchmark_dp_admissibleLCELComparisonWitness

/-- Universal structural-identity corollary for the benchmark-transport ↔
native DP / emitter pair. This closes Workstream F of the LCEL universal-
theorem roadmap: the two non-Gödel canonical sides are structurally parallel
to each other via a direct universal quasi-functor, not only through the
Gödel side. -/
theorem benchmark_dp_universal_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        benchmarkTransportAdmissibleLCELInstance
        dpEmitterAdmissibleLCELInstance) :=
  lcel_universal_structural_identity_of_comparison
    benchmark_dp_admissibleLCELComparisonWitness

end OperatorKO7.LCELBenchmarkDpComparison
