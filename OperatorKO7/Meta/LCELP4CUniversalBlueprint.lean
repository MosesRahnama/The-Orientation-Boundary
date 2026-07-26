import OperatorKO7.Meta.LCELP4CCanonicalInstances

/-!
# Constant-target LCEL P4C blueprint

For any two certified LCEL instances, this module constructs the existing route-lift blueprint
record by selecting designated witnesses and support facts from the target instance. The transport
maps are constant in their source inputs. The resulting universal theorem closes this record-valued
interface, but it does not prove a faithful, injective, reflective, or nonconstant semantic
correspondence between arbitrary instances.

The later declarations give aliases and projections from these blueprint records to residual
packages, followed by three fixed-pair instances imported from the canonical-instance module.
-/

namespace OperatorKO7.LCELP4CUniversalBlueprint

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELGenericTransportBridge
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELUnrestrictedExistence
open OperatorKO7.LCELP4CResidualObligation
open OperatorKO7.LCELP4CCanonicalInstances

namespace CertifiedFormalLCELInstance

/-- A slot-correspondence record whose maps select target-designated witnesses and support facts.
The source values supplied to the maps are ignored. -/
def strongSemanticSlotCorrespondenceOfCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    LCELStrongSemanticSlotCorrespondence C₁.instance_ C₂.instance_ where
  boundary :=
    { toBoundaryObjectCorrespondence :=
        { translate := fun _ => C₂.instance_.boundaryObject.designated
          translate_designated := rfl }
      translate_preserves_not_provable := by
        intro _ _
        exact BaseReversibilitySupport.designatedBoundaryNotProvable C₂.baseSupport
      translate_preserves_true := by
        intro _ _
        exact BaseReversibilitySupport.designatedBoundaryTrueInReferenceModel
          C₂.baseSupport }
  externalLicense :=
    { toExternalLicenseCorrespondence :=
        { forward := fun _ => C₂.licenseSupport.externalLicenseHolds
          backward := fun _ => C₁.licenseSupport.externalLicenseHolds }
      forward_preserves_blocked_not_provable := by
        intro _
        exact C₂.licenseSupport.blockedNotProvable
      forward_preserves_stronger_reflects := by
        intro _
        exact C₂.licenseSupport.strongerFrameworkReflectsBlocked }
  reimportClass :=
    { toReimportClassCorrespondence :=
        { forward := fun _ => C₂.reimportSupport.reimportClassHolds
          backward := fun _ => C₁.reimportSupport.reimportClassHolds }
      forward_preserves_witness_certifies_imported := by
        intro _
        exact C₂.reimportSupport.witnessCertifiesImported
      forward_preserves_imported_true := by
        intro _
        exact C₂.reimportSupport.importedTrue }
  annotation :=
    { toAnnotationFunctorCorrespondence :=
        { translateAnnotation := fun _ =>
            C₂.instance_.annotationFunctor.annotate
              C₂.instance_.comparison.reimportContent.witness
          translate_annotate_witness := rfl }
      translate_preserves_witness_certifies_decoded :=
        C₂.reimportSupport.annotationCertifiesDecoded
      translate_preserves_decoded_true :=
        C₂.reimportSupport.annotationDecodedTrue
      translate_preserves_decodes_to_imported :=
        C₂.reimportSupport.annotationDecodesImported }
  baseSentence :=
    { translateProvedSentence := fun _ => C₂.baseSupport.internalSentence
      translateProvedSentence_preserves_provable := by
        intro _ _
        exact C₂.baseSupport.internalSentenceProved }

/-- Two certified profiles are stagewise equivalent by composing each profile's stored equivalence
with the same comparison shape. -/
theorem stagewiseEquivalentOfCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    OperatorKO7.ReflectionSchema.StagewiseEquivalent
      C₁.instance_.comparison.profile.shape
      C₂.instance_.comparison.profile.shape := by
  have h₁ := (C₁.instance_.comparison.supported).2.2
  have h₂ := (C₂.instance_.comparison.supported).2.2
  intro s
  exact (h₁ s).trans (h₂ s).symm

/-- Route-semantics record assembled from the constant-target slot correspondence, stagewise
equivalence, and target-instance support fields. The historical declaration name says
`sourceSensitive`, but the slot maps do not inspect source content. -/
def sourceSensitiveRouteSemanticsOfCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    LCELSourceSensitiveRouteSemantics C₁.instance_ C₂.instance_ where
  strongSlot := strongSemanticSlotCorrespondenceOfCertifiedInstances C₁ C₂
  stagewise := stagewiseEquivalentOfCertifiedInstances C₁ C₂
  targetLicensedAdmission := C₂.licenseSupport.blockedLicensedAdmission
  targetObstructionBlockedEqReflectionBlocked :=
    C₂.boundarySupport.obstructionBlockedEqReflectionBlocked
  targetReflectionBlockedEqImported :=
    C₂.boundarySupport.reflectionBlockedEqImported
  targetBoundaryRealized := C₂.boundarySupport.boundaryRealized

theorem transportBase_canonical_ofCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    (sourceSensitiveRouteSemanticsOfCertifiedInstances C₁ C₂).transportBase
        (baseReversibilityTheorem_of_support C₁.toAdmissibilityData.baseSupport)
      = baseReversibilityTheorem_of_support C₂.toAdmissibilityData.baseSupport := by
  cases C₁
  cases C₂
  rfl

theorem transportLicense_canonical_ofCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    (sourceSensitiveRouteSemanticsOfCertifiedInstances C₁ C₂).transportLicense
        (licenseIrreversibilityTheorem_of_support C₁.toAdmissibilityData.licenseSupport)
      = licenseIrreversibilityTheorem_of_support C₂.toAdmissibilityData.licenseSupport := by
  cases C₁
  cases C₂
  rfl

theorem transportReimport_canonical_ofCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    (sourceSensitiveRouteSemanticsOfCertifiedInstances C₁ C₂).transportReimport
        (reimportReversibilityTheorem_of_support C₁.toAdmissibilityData.reimportSupport)
      = reimportReversibilityTheorem_of_support C₂.toAdmissibilityData.reimportSupport := by
  cases C₁
  cases C₂
  rfl

theorem transportBoundary_canonical_ofCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    (sourceSensitiveRouteSemanticsOfCertifiedInstances C₁ C₂).transportBoundary
        (boundaryFactorizationTheorem_of_support C₁.toAdmissibilityData.boundarySupport)
      = boundaryFactorizationTheorem_of_support C₂.toAdmissibilityData.boundarySupport := by
  cases C₁
  cases C₂
  rfl

namespace CertifiedRouteLiftBlueprint

/-- Construct the route-lift blueprint record for a certified pair from constant-target maps and
the target instance's stored support facts. -/
def ofCertifiedInstances
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint C₁ C₂ where
  strongSlot := strongSemanticSlotCorrespondenceOfCertifiedInstances C₁ C₂
  stagewise := stagewiseEquivalentOfCertifiedInstances C₁ C₂
  targetObstructionBlockedEqReflectionBlocked :=
    C₂.boundarySupport.obstructionBlockedEqReflectionBlocked
  targetReflectionBlockedEqImported :=
    C₂.boundarySupport.reflectionBlockedEqImported
  transportBase_canonical := by
    simpa [sourceSensitiveRouteSemanticsOfCertifiedInstances] using
      transportBase_canonical_ofCertifiedInstances C₁ C₂
  transportLicense_canonical := by
    simpa [sourceSensitiveRouteSemanticsOfCertifiedInstances] using
      transportLicense_canonical_ofCertifiedInstances C₁ C₂
  transportReimport_canonical := by
    simpa [sourceSensitiveRouteSemanticsOfCertifiedInstances] using
      transportReimport_canonical_ofCertifiedInstances C₁ C₂
  transportBoundary_canonical := by
    simpa [sourceSensitiveRouteSemanticsOfCertifiedInstances] using
      transportBoundary_canonical_ofCertifiedInstances C₁ C₂

end CertifiedRouteLiftBlueprint

/-- Every certified pair inhabits the route-lift blueprint type defined by this weak interface. -/
theorem hasCertifiedRouteLiftBlueprint_universal
    (C₁ C₂ : CertifiedFormalLCELInstance) :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprint C₁ C₂ :=
  ⟨CertifiedRouteLiftBlueprint.ofCertifiedInstances C₁ C₂⟩

/-- Universal quantification of the preceding constructor over certified instance pairs. This
theorem does not add source-dependence or faithfulness conditions. -/
theorem universalCertifiedRouteLiftBlueprint_closed :
    CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprint := by
  intro C₁ C₂
  exact hasCertifiedRouteLiftBlueprint_universal C₁ C₂

end CertifiedFormalLCELInstance

/-- Existence of an LCEL route-lift residual package for the underlying instances of a certified
pair. -/
abbrev CertifiedFormalLCELInstance.HasCertifiedRouteLiftResidualPackage
    (C₁ C₂ : CertifiedFormalLCELInstance) : Prop :=
  HasLCELRouteLiftResidualPackage C₁.instance_ C₂.instance_

/-- Universal existence of residual packages for certified instance pairs. -/
abbrev CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftResidualPackage : Prop :=
  ∀ C₁ C₂ : CertifiedFormalLCELInstance,
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftResidualPackage C₁ C₂

/-- Alias of the route-lift blueprint type for a fixed certified pair. -/
abbrev CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprintBoundaryData
    (C₁ C₂ : CertifiedFormalLCELInstance) : Type 1 :=
  CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint C₁ C₂

/-- Nonemptiness of the aliased blueprint type for a fixed certified pair. -/
abbrev CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprintBoundaryData
    (C₁ C₂ : CertifiedFormalLCELInstance) : Prop :=
  Nonempty (CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprintBoundaryData C₁ C₂)

/-- Universal nonemptiness of the aliased blueprint type. -/
abbrev CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprintBoundaryData : Prop :=
  ∀ C₁ C₂ : CertifiedFormalLCELInstance,
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprintBoundaryData C₁ C₂

namespace CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint

/-- A route-lift blueprint supplies a residual package through its `toResidualPackage` field. -/
theorem hasCertifiedRouteLiftResidualPackage
    {C₁ C₂ : CertifiedFormalLCELInstance}
  (B : CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint C₁ C₂) :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftResidualPackage C₁ C₂ :=
  ⟨B.toResidualPackage⟩

/-- Project `HasLCELRouteSemanticsLiftData` from a blueprint's residual package. -/
theorem hasRouteSemanticsLiftData
    {C₁ C₂ : CertifiedFormalLCELInstance}
  (B : CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint C₁ C₂) :
    HasLCELRouteSemanticsLiftData C₁.instance_ C₂.instance_ :=
  B.toResidualPackage.hasRouteSemanticsLiftData

/-- Project the witness-free residual obligation from a blueprint's residual package. -/
theorem witnessFreeResidualObligation
    {C₁ C₂ : CertifiedFormalLCELInstance}
  (B : CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint C₁ C₂) :
    OperatorKO7.LCELUnrestrictedClassification.LCELWitnessFreeResidualObligation
      C₁.instance_ C₂.instance_ :=
  B.toResidualPackage.witnessFreeResidualObligation

end CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint

namespace CertifiedFormalLCELInstance

/-- The two fixed-pair nonemptiness propositions are definitionally equal aliases. -/
theorem hasCertifiedRouteLiftBlueprint_iff_hasCertifiedRouteLiftBlueprintBoundaryData
    {C₁ C₂ : CertifiedFormalLCELInstance} :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprint C₁ C₂ ↔
      CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprintBoundaryData C₁ C₂ :=
  Iff.rfl

/-- The two universally quantified blueprint propositions are definitionally equal aliases. -/
theorem universalCertifiedRouteLiftBlueprint_iff_universalCertifiedRouteLiftBlueprintBoundaryData :
    CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprint ↔
      CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprintBoundaryData :=
  Iff.rfl

/-- Eliminate blueprint nonemptiness and return residual-package nonemptiness for the same pair. -/
theorem hasCertifiedRouteLiftResidualPackage_of_hasCertifiedRouteLiftBlueprint
    {C₁ C₂ : CertifiedFormalLCELInstance}
    (h : CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprint C₁ C₂) :
    HasCertifiedRouteLiftResidualPackage C₁ C₂ := by
  rcases h with ⟨B⟩
  exact ⟨B.toResidualPackage⟩

/-- Map universal blueprint nonemptiness to universal residual-package nonemptiness. -/
theorem universalCertifiedRouteLiftResidualPackage_of_universalCertifiedRouteLiftBlueprint
    (h : CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprint) :
    UniversalCertifiedRouteLiftResidualPackage := by
  intro C₁ C₂
  exact hasCertifiedRouteLiftResidualPackage_of_hasCertifiedRouteLiftBlueprint (h C₁ C₂)

end CertifiedFormalLCELInstance

/-- Apply the imported residual-package constructor to universal certification and the blueprint
alias hypothesis. -/
theorem universal_residualPackage_of_universalCertification_and_universalCertifiedRouteLiftBlueprintBoundaryData
    (hCertification : CertifiedFormalLCELInstance.UniversalCertification)
    (hBoundaryData : CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprintBoundaryData) :
    UniversalLCELRouteLiftResidualPackage :=
  universal_residualPackage_of_universal_certification_and_blueprint
    hCertification
    (CertifiedFormalLCELInstance.universalCertifiedRouteLiftBlueprint_iff_universalCertifiedRouteLiftBlueprintBoundaryData.2
        hBoundaryData)

/-- Apply the imported raw-target theorem to universal certification and the blueprint alias
hypothesis. -/
theorem universal_rawTarget_of_universalCertification_and_universalCertifiedRouteLiftBlueprintBoundaryData
    (hCertification : CertifiedFormalLCELInstance.UniversalCertification)
    (hBoundaryData : CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprintBoundaryData) :
    LCELP4CRawTarget :=
  universal_lcel_witness_free_structural_identity_of_universal_certification_and_blueprint
    hCertification
    (CertifiedFormalLCELInstance.universalCertifiedRouteLiftBlueprint_iff_universalCertifiedRouteLiftBlueprintBoundaryData.2
        hBoundaryData)

/-- Imported benchmark-to-DP blueprint packaged as a nonempty proposition. -/
theorem benchmark_dp_hasCertifiedRouteLiftBlueprint :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprint
      benchmarkTransportCertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  ⟨benchmark_dp_certifiedRouteLiftBlueprint⟩

/-- The benchmark-to-DP blueprint reused through the boundary-data alias. -/
theorem benchmark_dp_hasCertifiedRouteLiftBlueprintBoundaryData :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprintBoundaryData
      benchmarkTransportCertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  benchmark_dp_hasCertifiedRouteLiftBlueprint

/-- Imported Godel-to-DP blueprint packaged as a nonempty proposition. -/
theorem godel_dp_hasCertifiedRouteLiftBlueprint :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprint
      godel1931CertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  ⟨godel_dp_certifiedRouteLiftBlueprint⟩

/-- The Godel-to-DP blueprint reused through the boundary-data alias. -/
theorem godel_dp_hasCertifiedRouteLiftBlueprintBoundaryData :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprintBoundaryData
      godel1931CertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  godel_dp_hasCertifiedRouteLiftBlueprint

/-- Imported Godel-to-benchmark blueprint packaged as a nonempty proposition. -/
theorem godel_benchmark_hasCertifiedRouteLiftBlueprint :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprint
      godel1931CertifiedFormalLCELInstance
      benchmarkTransportCertifiedFormalLCELInstance :=
  ⟨godel_benchmark_certifiedRouteLiftBlueprint⟩

/-- The Godel-to-benchmark blueprint reused through the boundary-data alias. -/
theorem godel_benchmark_hasCertifiedRouteLiftBlueprintBoundaryData :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftBlueprintBoundaryData
      godel1931CertifiedFormalLCELInstance
      benchmarkTransportCertifiedFormalLCELInstance :=
  godel_benchmark_hasCertifiedRouteLiftBlueprint

/-- Residual package projected from the imported benchmark-to-DP blueprint. -/
theorem benchmark_dp_hasCertifiedRouteLiftResidualPackage :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftResidualPackage
      benchmarkTransportCertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  ⟨benchmark_dp_certifiedRouteLiftBlueprint.toResidualPackage⟩

/-- Residual package projected from the imported Godel-to-DP blueprint. -/
theorem godel_dp_hasCertifiedRouteLiftResidualPackage :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftResidualPackage
      godel1931CertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  ⟨godel_dp_certifiedRouteLiftBlueprint.toResidualPackage⟩

/-- Residual package projected from the imported Godel-to-benchmark blueprint. -/
theorem godel_benchmark_hasCertifiedRouteLiftResidualPackage :
    CertifiedFormalLCELInstance.HasCertifiedRouteLiftResidualPackage
      godel1931CertifiedFormalLCELInstance
      benchmarkTransportCertifiedFormalLCELInstance :=
  ⟨godel_benchmark_certifiedRouteLiftBlueprint.toResidualPackage⟩

end OperatorKO7.LCELP4CUniversalBlueprint
