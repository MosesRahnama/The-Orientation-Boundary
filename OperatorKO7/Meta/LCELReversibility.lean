import OperatorKO7.Meta.LCELSchema

/-!
# LCEL proposition-support packages

Witness-parameterized packaging for Paper C Propositions 5.8
(`prop:lcel-reversibility`) and 5.9 (`prop:lcel-boundary-factorization`).

The records in this file contain supplied propositions and proofs for the
labels used in Paper C Propositions 5.8 and 5.9. Reversibility relations,
inverse or partial-injection laws, projection maps, and a projection-composition
equation require separate formal data. Instance packages below populate the
proposition slots from the available LCEL semantic-support fields.
-/

namespace OperatorKO7.LCELReversibility

open OperatorKO7.LCELSchema

/-- Supplied proposition slot for the base-reversibility clause. This record
contains the proposition and its proof. -/
structure BaseStepReversibilityWitness (L : FormalLCELInstance) : Type where
  isReversible : Prop
  holds : isReversible

/-- Supplied proposition slot for the license-irreversibility clause. This
record contains the proposition and its proof. -/
structure LicenseIrreversibilityWitness (L : FormalLCELInstance) : Type where
  isIrreversible : Prop
  holds : isIrreversible

/-- Supplied proposition slot for the designated reimport-class clause. -/
structure ReimportReversibilityWitness (L : FormalLCELInstance) : Type where
  isReversibleOnReimportClass : Prop
  holds : isReversibleOnReimportClass

/-- Three supplied propositions and their proofs, labeled for Paper C
Proposition 5.8. -/
structure LCELReversibilityAsymmetry (L : FormalLCELInstance) : Type where
  baseReversible : Prop
  licenseIrreversible : Prop
  reimportReversibleOnReimportClass : Prop
  holdsBase : baseReversible
  holdsLicense : licenseIrreversible
  holdsReimport : reimportReversibleOnReimportClass

/-- Repackage three supplied proposition witnesses as the named asymmetry
record. -/
def lcel_reversibility_asymmetry_of_witnesses
    {L : FormalLCELInstance}
    (hBaseRev : BaseStepReversibilityWitness L)
    (hLicenseIrrev : LicenseIrreversibilityWitness L)
    (hReimportRev : ReimportReversibilityWitness L) :
    LCELReversibilityAsymmetry L :=
  { baseReversible := hBaseRev.isReversible
    licenseIrreversible := hLicenseIrrev.isIrreversible
    reimportReversibleOnReimportClass := hReimportRev.isReversibleOnReimportClass
    holdsBase := hBaseRev.holds
    holdsLicense := hLicenseIrrev.holds
    holdsReimport := hReimportRev.holds }

/-- Two supplied proposition slots labeled for the visible and
boundary-sensitive components of Paper C Proposition 5.9. This record contains
propositions and proofs; projection maps and a composition equation require a
separate structure. -/
structure ProjectionFactorizationWitness (L : FormalLCELInstance) : Type where
  visibleViaReversible : Prop
  sensitiveToIrreversible : Prop
  visibleHolds : visibleViaReversible
  sensitiveHolds : sensitiveToIrreversible

/-- Three proposition slots and proofs labeled for Paper C Proposition 5.9. -/
structure LCELBoundaryFactorization (L : FormalLCELInstance) : Type where
  hasReversibleProjection : Prop
  hasIrreversibleQuotient : Prop
  boundarySensitiveToIrreversible : Prop
  holdsReversible : hasReversibleProjection
  holdsIrreversible : hasIrreversibleQuotient
  holdsBoundary : boundarySensitiveToIrreversible

/-- Repackage the two supplied proposition witnesses as the named boundary
record. -/
def lcel_boundary_factorization_of_witness
    {L : FormalLCELInstance}
    (hFact : ProjectionFactorizationWitness L) :
    LCELBoundaryFactorization L :=
  { hasReversibleProjection := hFact.visibleViaReversible
    hasIrreversibleQuotient := hFact.sensitiveToIrreversible
    boundarySensitiveToIrreversible := hFact.sensitiveToIrreversible
    holdsReversible := hFact.visibleHolds
    holdsIrreversible := hFact.sensitiveHolds
    holdsBoundary := hFact.sensitiveHolds }

/-! ## Proposition-support adapters -/

/-- Available base-layer support proposition read from a typed LCEL
instance. -/
def SemanticBaseLayerSupport (L : FormalLCELInstance) : Prop :=
  L.comparison.baseTheoryContent.hasInternalProofLayer

/-- Available obstruction-to-license support proposition read from a typed
LCEL instance. -/
def SemanticLicenseTransferSupport (L : FormalLCELInstance) : Prop :=
  L.comparison.semanticCoherence.obstructionTransfersToReflection

/-- Available licensed-reimport support proposition read from a typed LCEL
instance. -/
def SemanticReimportTransferSupport (L : FormalLCELInstance) : Prop :=
  L.comparison.semanticCoherence.reflectionTransfersToReimport

/-! ## Stronger proof-carrying substrate support records -/

/-- Stronger support record for the base-layer side of LCEL reversibility.

It stores the available semantic-support proposition, a designated internal
proof witness, and a designated boundary witness used by the named LCEL
instances. -/
structure BaseReversibilitySupport (L : FormalLCELInstance) : Type where
  semanticBaseHolds : SemanticBaseLayerSupport L
  internalSentence : L.comparison.baseTheoryContent.Sentence
  internalSentenceProved :
    L.comparison.baseTheoryContent.proves internalSentence
  designatedBoundaryWitness : L.boundaryObject.BoundaryWitness
  designatedBoundaryEq :
    designatedBoundaryWitness = L.boundaryObject.designated
  designatedBoundaryUnprovable :
    ¬ L.comparison.baseTheoryContent.proves
        (L.boundaryObject.boundarySentence designatedBoundaryWitness)
  designatedBoundaryTrue :
    L.comparison.baseTheoryContent.trueInReferenceModel
      (L.boundaryObject.boundarySentence designatedBoundaryWitness)
  boundaryRealized : L.boundaryObject.realized

namespace BaseReversibilitySupport

def supported {L : FormalLCELInstance} (S : BaseReversibilitySupport L) : Prop :=
  L.comparison.baseTheoryContent.proves S.internalSentence
    ∧ L.boundaryObject.realized

theorem supportsSemanticBase
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    SemanticBaseLayerSupport L :=
  S.semanticBaseHolds

theorem supportsBoundaryRealization
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    L.boundaryObject.realized :=
  S.boundaryRealized

theorem supportsBoundaryProfile
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    L.comparison.profile.shape.hasSelfObstruction :=
  L.boundaryMatchesProfile.mp S.boundaryRealized

theorem designatedBoundaryNotProvable
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    ¬ L.comparison.baseTheoryContent.proves
        (L.boundaryObject.boundarySentence L.boundaryObject.designated) := by
  simpa [S.designatedBoundaryEq] using S.designatedBoundaryUnprovable

theorem designatedBoundaryTrueInReferenceModel
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    L.comparison.baseTheoryContent.trueInReferenceModel
      (L.boundaryObject.boundarySentence L.boundaryObject.designated) := by
  simpa [S.designatedBoundaryEq] using S.designatedBoundaryTrue

def toBaseStepReversibilityWitness
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    BaseStepReversibilityWitness L :=
  { isReversible := BaseReversibilitySupport.supported S
    holds := ⟨S.internalSentenceProved, S.boundaryRealized⟩ }

end BaseReversibilitySupport

/-- Stronger support record for the external-license side of LCEL reversibility.

It stores the available obstruction-to-reflection transfer proposition, the
blocked sentence, proofs of its unprovability and truth, and the designated
stronger-framework and license data. -/
structure LicenseIrreversibilitySupport (L : FormalLCELInstance) : Type where
  semanticTransferHolds : SemanticLicenseTransferSupport L
  externalLicenseHolds : L.externalLicenseWitness
  obstructionWitnessSelfReferential :
    L.comparison.obstructionContent.selfReferential
      L.comparison.obstructionContent.witness
  obstructionWitnessesBlocked :
    L.comparison.obstructionContent.obstructs
      L.comparison.obstructionContent.witness
      (L.comparison.obstructionContent.blockedBy
        L.comparison.obstructionContent.witness)
  obstructionBlockedEqReflectionBlocked :
    L.comparison.obstructionContent.blockedBy
      L.comparison.obstructionContent.witness =
    L.comparison.reflectionContent.blockedSentence
  blockedNotProvable :
    ¬ L.comparison.baseTheoryContent.proves
        L.comparison.reflectionContent.blockedSentence
  blockedTrue :
    L.comparison.baseTheoryContent.trueInReferenceModel
      L.comparison.reflectionContent.blockedSentence
  strongerFrameworkExtendsBase :
    L.comparison.reflectionContent.extendsBase
      L.comparison.reflectionContent.strongerFramework
  strongerFrameworkReflectsBlocked :
    L.comparison.reflectionContent.reflects
      L.comparison.reflectionContent.strongerFramework
      L.comparison.reflectionContent.blockedSentence
  blockedLicensedAdmission :
    L.comparison.reflectionContent.licensedAdmission
      L.comparison.reflectionContent.blockedSentence

namespace LicenseIrreversibilitySupport

def supported {L : FormalLCELInstance}
    (S : LicenseIrreversibilitySupport L) : Prop :=
  let _hTransfer := S.semanticTransferHolds
  L.comparison.reflectionContent.reflects
      L.comparison.reflectionContent.strongerFramework
      L.comparison.reflectionContent.blockedSentence
    ∧ L.externalLicenseWitness
    ∧ ¬ L.comparison.baseTheoryContent.proves
        L.comparison.reflectionContent.blockedSentence
    ∧ L.comparison.baseTheoryContent.trueInReferenceModel
        L.comparison.reflectionContent.blockedSentence
    ∧ L.comparison.reflectionContent.licensedAdmission
        L.comparison.reflectionContent.blockedSentence

theorem supportsSemanticTransfer
    {L : FormalLCELInstance}
    (S : LicenseIrreversibilitySupport L) :
    SemanticLicenseTransferSupport L :=
  S.semanticTransferHolds

def toLicenseIrreversibilityWitness
    {L : FormalLCELInstance}
    (S : LicenseIrreversibilitySupport L) :
    LicenseIrreversibilityWitness L :=
  { isIrreversible := LicenseIrreversibilitySupport.supported S
    holds := ⟨S.strongerFrameworkReflectsBlocked, S.externalLicenseHolds,
      S.blockedNotProvable, S.blockedTrue, S.blockedLicensedAdmission⟩ }

end LicenseIrreversibilitySupport

/-- Stronger support record for the reimport side of LCEL reversibility.

This packages the available reflection-to-reimport transfer together with the
typed reimport witness, its imported sentence, and the designated annotation
evidence already present in the LCEL instance. -/
structure ReimportReversibilitySupport (L : FormalLCELInstance) : Type where
  semanticTransferHolds : SemanticReimportTransferSupport L
  reimportClassHolds : L.reimportClassWitness
  reflectionBlockedEqImported :
    L.comparison.reflectionContent.blockedSentence =
      L.comparison.reimportContent.importedSentence
  witnessCertifiesBlocked :
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      L.comparison.reflectionContent.blockedSentence
  witnessCertifiesImported :
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      L.comparison.reimportContent.importedSentence
  importedTrue :
    L.comparison.baseTheoryContent.trueInReferenceModel
      L.comparison.reimportContent.importedSentence
  annotationDecodesImported :
    L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness) =
      L.comparison.reimportContent.importedSentence
  annotationCertifiesDecoded :
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      (L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness))
  annotationDecodedTrue :
    L.comparison.baseTheoryContent.trueInReferenceModel
      (L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness))
  annotationRealized : L.annotationFunctor.realized

namespace ReimportReversibilitySupport

def supported {L : FormalLCELInstance}
    (S : ReimportReversibilitySupport L) : Prop :=
  let _hTransfer := S.semanticTransferHolds
  L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      L.comparison.reflectionContent.blockedSentence
    ∧ L.reimportClassWitness
    ∧ L.annotationFunctor.realized
    ∧ L.comparison.reimportContent.certifies
        L.comparison.reimportContent.witness
        L.comparison.reimportContent.importedSentence
    ∧ L.comparison.baseTheoryContent.trueInReferenceModel
        L.comparison.reimportContent.importedSentence

theorem supportsSemanticTransfer
    {L : FormalLCELInstance}
    (S : ReimportReversibilitySupport L) :
    SemanticReimportTransferSupport L :=
  S.semanticTransferHolds

theorem certifiesReflectionBlocked
    {L : FormalLCELInstance}
    (S : ReimportReversibilitySupport L) :
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      L.comparison.reflectionContent.blockedSentence :=
  S.witnessCertifiesBlocked

def toReimportReversibilityWitness
    {L : FormalLCELInstance}
    (S : ReimportReversibilitySupport L) :
    ReimportReversibilityWitness L :=
  { isReversibleOnReimportClass := ReimportReversibilitySupport.supported S
    holds := ⟨S.witnessCertifiesBlocked, S.reimportClassHolds,
      S.annotationRealized, S.witnessCertifiesImported, S.importedTrue⟩ }

end ReimportReversibilitySupport

/-- Stronger support record for the factorization package.

This instance-sensitive record carries reimport-visible support,
license-sensitive support, and coherence equalities between the obstruction,
reflection, and reimport layers. -/
structure BoundaryFactorizationSupport (L : FormalLCELInstance) : Type where
  visibleSupport : ReimportReversibilitySupport L
  sensitiveSupport : LicenseIrreversibilitySupport L
  obstructionBlockedEqReflectionBlocked :
    L.comparison.obstructionContent.blockedBy
      L.comparison.obstructionContent.witness =
    L.comparison.reflectionContent.blockedSentence
  reflectionBlockedEqImported :
    L.comparison.reflectionContent.blockedSentence =
      L.comparison.reimportContent.importedSentence
  boundaryRealized : L.boundaryObject.realized

namespace BoundaryFactorizationSupport

def supported {L : FormalLCELInstance}
    (S : BoundaryFactorizationSupport L) : Prop :=
  ReimportReversibilitySupport.supported (S.visibleSupport)
    ∧ LicenseIrreversibilitySupport.supported (S.sensitiveSupport)
    ∧ L.boundaryObject.realized

def toProjectionFactorizationWitness
    {L : FormalLCELInstance}
    (S : BoundaryFactorizationSupport L) :
    ProjectionFactorizationWitness L :=
  { visibleViaReversible := ReimportReversibilitySupport.supported (S.visibleSupport)
    sensitiveToIrreversible :=
      LicenseIrreversibilitySupport.supported (S.sensitiveSupport) ∧ L.boundaryObject.realized
    visibleHolds := ⟨S.visibleSupport.witnessCertifiesBlocked,
      S.visibleSupport.reimportClassHolds,
      S.visibleSupport.annotationRealized,
      S.visibleSupport.witnessCertifiesImported,
      S.visibleSupport.importedTrue⟩
    sensitiveHolds := ⟨⟨S.sensitiveSupport.strongerFrameworkReflectsBlocked,
        S.sensitiveSupport.externalLicenseHolds,
        S.sensitiveSupport.blockedNotProvable,
        S.sensitiveSupport.blockedTrue,
        S.sensitiveSupport.blockedLicensedAdmission⟩,
      S.boundaryRealized⟩ }

def toLCELBoundaryFactorization
    {L : FormalLCELInstance}
    (S : BoundaryFactorizationSupport L) :
    LCELBoundaryFactorization L :=
  lcel_boundary_factorization_of_witness S.toProjectionFactorizationWitness

end BoundaryFactorizationSupport

/-- Build base-layer proposition support from the LCEL carrier and its available
semantic theorem. -/
def baseReversibilitySupport_of_semanticBase
    {L : FormalLCELInstance}
    (hBase : SemanticBaseLayerSupport L) :
    BaseReversibilitySupport L :=
  { semanticBaseHolds := hBase
    internalSentence := L.comparison.baseTheoryContent.baseSentence
    internalSentenceProved := L.comparison.baseTheoryContent.baseSentence_proves
    designatedBoundaryWitness := L.boundaryObject.designated
    designatedBoundaryEq := rfl
    designatedBoundaryUnprovable := by
      simpa using L.boundaryObject.designated_not_provable
    designatedBoundaryTrue := by
      simpa using L.boundaryObject.designated_true
    boundaryRealized := L.boundaryObject.designated_realizes }

/-- Build license-side proposition support from the LCEL carrier and its
available obstruction-to-reflection transfer theorem. -/
def licenseIrreversibilitySupport_of_semanticTransfer
    {L : FormalLCELInstance}
    (hLicense : SemanticLicenseTransferSupport L) :
    LicenseIrreversibilitySupport L :=
  { semanticTransferHolds := hLicense
    externalLicenseHolds := L.externalLicenseHolds
    obstructionWitnessSelfReferential :=
      L.comparison.obstructionContent.witness_selfReferential
    obstructionWitnessesBlocked :=
      L.comparison.obstructionContent.witness_obstructs_blocked
    obstructionBlockedEqReflectionBlocked :=
      L.comparison.semanticCoherence.obstruction_blocked_eq_reflection_blocked
    blockedNotProvable := by
      simpa using L.comparison.reflectionContent.blocked_not_provable
    blockedTrue := by
      simpa using L.comparison.reflectionContent.blocked_true
    strongerFrameworkExtendsBase :=
      L.comparison.reflectionContent.stronger_extendsBase
    strongerFrameworkReflectsBlocked :=
      L.comparison.reflectionContent.stronger_reflects_blocked
    blockedLicensedAdmission :=
      L.comparison.reflectionContent.blocked_licensedAdmission }

/-- Build reimport-side proposition support from the LCEL carrier and its
available reflection-to-reimport transfer theorem. -/
def reimportReversibilitySupport_of_semanticTransfer
    {L : FormalLCELInstance}
    (hReimport : SemanticReimportTransferSupport L) :
    ReimportReversibilitySupport L :=
  { semanticTransferHolds := hReimport
    reimportClassHolds := L.reimportClassHolds
    reflectionBlockedEqImported :=
      L.comparison.semanticCoherence.reflection_blocked_eq_reimported
    witnessCertifiesBlocked :=
      L.comparison.semanticCoherence.reimport_certifies_reflection_blocked
    witnessCertifiesImported :=
      L.comparison.reimportContent.witness_certifies_imported
    importedTrue := L.comparison.reimportContent.imported_true
    annotationDecodesImported :=
      L.annotationFunctor.witness_decodes_to_imported
    annotationCertifiesDecoded :=
      L.annotationFunctor.witness_certifies_decoded
    annotationDecodedTrue :=
      L.annotationFunctor.witness_decoded_true
    annotationRealized := L.annotationFunctor.witness_realizes }

/-- Build stronger boundary-factorization support from the stronger visible and
sensitive substrate records. -/
def boundaryFactorizationSupport_of_supports
    {L : FormalLCELInstance}
    (hVisible : ReimportReversibilitySupport L)
    (hSensitive : LicenseIrreversibilitySupport L) :
    BoundaryFactorizationSupport L :=
  { visibleSupport := hVisible
    sensitiveSupport := hSensitive
    obstructionBlockedEqReflectionBlocked :=
      L.comparison.semanticCoherence.obstruction_blocked_eq_reflection_blocked
    reflectionBlockedEqImported :=
      L.comparison.semanticCoherence.reflection_blocked_eq_reimported
    boundaryRealized := L.boundaryObject.designated_realizes }

/-- Stronger substrate-support route back to the existing asymmetry package. -/
def lcelReversibilityAsymmetry_of_strongerSupports
    {L : FormalLCELInstance}
    (hBase : BaseReversibilitySupport L)
    (hLicense : LicenseIrreversibilitySupport L)
    (hReimport : ReimportReversibilitySupport L) :
    LCELReversibilityAsymmetry L :=
  lcel_reversibility_asymmetry_of_witnesses
    hBase.toBaseStepReversibilityWitness
    hLicense.toLicenseIrreversibilityWitness
    hReimport.toReimportReversibilityWitness

/-- Stronger substrate-support route back to the existing boundary-
factorization package. -/
def lcelBoundaryFactorization_of_strongerSupport
    {L : FormalLCELInstance}
    (hSupport : BoundaryFactorizationSupport L) :
    LCELBoundaryFactorization L :=
  hSupport.toLCELBoundaryFactorization

@[simp] theorem lcelReversibilityAsymmetry_of_strongerSupports_base
    {L : FormalLCELInstance}
    (hBase : BaseReversibilitySupport L)
    (hLicense : LicenseIrreversibilitySupport L)
    (hReimport : ReimportReversibilitySupport L) :
    (lcelReversibilityAsymmetry_of_strongerSupports hBase hLicense hReimport).baseReversible =
      BaseReversibilitySupport.supported hBase := rfl

@[simp] theorem lcelReversibilityAsymmetry_of_strongerSupports_license
    {L : FormalLCELInstance}
    (hBase : BaseReversibilitySupport L)
    (hLicense : LicenseIrreversibilitySupport L)
    (hReimport : ReimportReversibilitySupport L) :
    (lcelReversibilityAsymmetry_of_strongerSupports hBase hLicense hReimport).licenseIrreversible =
      LicenseIrreversibilitySupport.supported hLicense := rfl

@[simp] theorem lcelReversibilityAsymmetry_of_strongerSupports_reimport
    {L : FormalLCELInstance}
    (hBase : BaseReversibilitySupport L)
    (hLicense : LicenseIrreversibilitySupport L)
    (hReimport : ReimportReversibilitySupport L) :
    (lcelReversibilityAsymmetry_of_strongerSupports hBase hLicense hReimport).reimportReversibleOnReimportClass =
      ReimportReversibilitySupport.supported hReimport := rfl

@[simp] theorem lcelBoundaryFactorization_of_strongerSupport_reversibleProjection
    {L : FormalLCELInstance}
    (hSupport : BoundaryFactorizationSupport L) :
    (lcelBoundaryFactorization_of_strongerSupport hSupport).hasReversibleProjection =
      ReimportReversibilitySupport.supported (hSupport.visibleSupport) := rfl

@[simp] theorem lcelBoundaryFactorization_of_strongerSupport_irreversibleQuotient
    {L : FormalLCELInstance}
    (hSupport : BoundaryFactorizationSupport L) :
    (lcelBoundaryFactorization_of_strongerSupport hSupport).hasIrreversibleQuotient =
      (LicenseIrreversibilitySupport.supported (hSupport.sensitiveSupport)
        ∧ L.boundaryObject.realized) := rfl

/-- Place the available base-layer semantic-support proposition in the abstract
base-step witness slot. The result remains a proposition-support record. -/
def baseStepReversibilityWitness_of_semanticBase
    {L : FormalLCELInstance}
    (hBase : SemanticBaseLayerSupport L) :
    BaseStepReversibilityWitness L :=
  { isReversible := SemanticBaseLayerSupport L
    holds := hBase }

/-- Place the available obstruction-to-license transfer support in
the abstract LCEL license-irreversibility witness slot. -/
def licenseIrreversibilityWitness_of_semanticTransfer
    {L : FormalLCELInstance}
    (hLicense : SemanticLicenseTransferSupport L) :
    LicenseIrreversibilityWitness L :=
  { isIrreversible := SemanticLicenseTransferSupport L
    holds := hLicense }

/-- Place the available reflection-to-reimport transfer support in
the abstract LCEL reimport-reversibility witness slot. -/
def reimportReversibilityWitness_of_semanticTransfer
    {L : FormalLCELInstance}
    (hReimport : SemanticReimportTransferSupport L) :
    ReimportReversibilityWitness L :=
  { isReversibleOnReimportClass := SemanticReimportTransferSupport L
    holds := hReimport }

/-- Package two formal transfer propositions in the boundary-factorization
witness slots. The visible slot stores reflection-to-reimport transfer, and the
sensitive slot stores obstruction-to-reflection transfer. -/
def projectionFactorizationWitness_of_semanticTransfers
    {L : FormalLCELInstance}
    (hVisible : SemanticReimportTransferSupport L)
    (hSensitive : SemanticLicenseTransferSupport L) :
    ProjectionFactorizationWitness L :=
  { visibleViaReversible := SemanticReimportTransferSupport L
    sensitiveToIrreversible := SemanticLicenseTransferSupport L
    visibleHolds := hVisible
    sensitiveHolds := hSensitive }

/-- LCEL asymmetry proposition package assembled from the supplied semantic
support fields. -/
def lcelReversibilityAsymmetry_of_semanticSupports
    {L : FormalLCELInstance}
    (hBase : SemanticBaseLayerSupport L)
    (hLicense : SemanticLicenseTransferSupport L)
    (hReimport : SemanticReimportTransferSupport L) :
    LCELReversibilityAsymmetry L :=
  lcel_reversibility_asymmetry_of_witnesses
    (baseStepReversibilityWitness_of_semanticBase hBase)
    (licenseIrreversibilityWitness_of_semanticTransfer hLicense)
    (reimportReversibilityWitness_of_semanticTransfer hReimport)

@[simp] theorem lcelReversibilityAsymmetry_of_semanticSupports_baseReversible
    {L : FormalLCELInstance}
    (hBase : SemanticBaseLayerSupport L)
    (hLicense : SemanticLicenseTransferSupport L)
    (hReimport : SemanticReimportTransferSupport L) :
    (lcelReversibilityAsymmetry_of_semanticSupports hBase hLicense hReimport).baseReversible =
      SemanticBaseLayerSupport L := rfl

@[simp] theorem lcelReversibilityAsymmetry_of_semanticSupports_licenseIrreversible
    {L : FormalLCELInstance}
    (hBase : SemanticBaseLayerSupport L)
    (hLicense : SemanticLicenseTransferSupport L)
    (hReimport : SemanticReimportTransferSupport L) :
    (lcelReversibilityAsymmetry_of_semanticSupports hBase hLicense hReimport).licenseIrreversible =
      SemanticLicenseTransferSupport L := rfl

@[simp] theorem lcelReversibilityAsymmetry_of_semanticSupports_reimportReversible
    {L : FormalLCELInstance}
    (hBase : SemanticBaseLayerSupport L)
    (hLicense : SemanticLicenseTransferSupport L)
    (hReimport : SemanticReimportTransferSupport L) :
    (lcelReversibilityAsymmetry_of_semanticSupports hBase hLicense hReimport).reimportReversibleOnReimportClass =
      SemanticReimportTransferSupport L := rfl

/-- LCEL boundary proposition package assembled from the supplied semantic
support fields. -/
def lcelBoundaryFactorization_of_semanticSupports
    {L : FormalLCELInstance}
    (hVisible : SemanticReimportTransferSupport L)
    (hSensitive : SemanticLicenseTransferSupport L) :
    LCELBoundaryFactorization L :=
  lcel_boundary_factorization_of_witness
    (projectionFactorizationWitness_of_semanticTransfers hVisible hSensitive)

@[simp] theorem lcelBoundaryFactorization_of_semanticSupports_reversibleProjection
    {L : FormalLCELInstance}
    (hVisible : SemanticReimportTransferSupport L)
    (hSensitive : SemanticLicenseTransferSupport L) :
    (lcelBoundaryFactorization_of_semanticSupports hVisible hSensitive).hasReversibleProjection =
      SemanticReimportTransferSupport L := rfl

@[simp] theorem lcelBoundaryFactorization_of_semanticSupports_irreversibleQuotient
    {L : FormalLCELInstance}
    (hVisible : SemanticReimportTransferSupport L)
    (hSensitive : SemanticLicenseTransferSupport L) :
    (lcelBoundaryFactorization_of_semanticSupports hVisible hSensitive).hasIrreversibleQuotient =
      SemanticLicenseTransferSupport L := rfl

@[simp] theorem lcelBoundaryFactorization_of_semanticSupports_boundarySensitive
    {L : FormalLCELInstance}
    (hVisible : SemanticReimportTransferSupport L)
    (hSensitive : SemanticLicenseTransferSupport L) :
    (lcelBoundaryFactorization_of_semanticSupports hVisible hSensitive).boundarySensitiveToIrreversible =
      SemanticLicenseTransferSupport L := rfl

/-! ## Canonical LCEL witness packages -/

theorem godel1931_semanticBaseLayerSupport :
    SemanticBaseLayerSupport godel1931LCELInstance := by
  rcases OperatorKO7.ClassicalAscentProfile.godel1931FormalExternalClassicalComparison_semanticSupported with
    ⟨hBase, _, _, _, _, _, _⟩
  simpa [SemanticBaseLayerSupport, godel1931LCELInstance]

theorem godel1931_semanticLicenseTransferSupport :
    SemanticLicenseTransferSupport godel1931LCELInstance := by
  rcases OperatorKO7.ClassicalAscentProfile.godel1931FormalExternalClassicalComparison_transferSupported with
    ⟨hTransfer, _⟩
  simpa [SemanticLicenseTransferSupport, godel1931LCELInstance]

theorem godel1931_semanticReimportTransferSupport :
    SemanticReimportTransferSupport godel1931LCELInstance := by
  rcases OperatorKO7.ClassicalAscentProfile.godel1931FormalExternalClassicalComparison_transferSupported with
    ⟨_, hTransfer⟩
  simpa [SemanticReimportTransferSupport, godel1931LCELInstance]

/-- Gödel-side base support package assembled from the typed LCEL carrier and
its semantic base-layer theorem. -/
def godel1931BaseReversibilitySupport :
    BaseReversibilitySupport godel1931LCELInstance :=
  baseReversibilitySupport_of_semanticBase
    godel1931_semanticBaseLayerSupport

/-- Gödel-side license support package assembled from the typed LCEL carrier and
its semantic transfer theorem. -/
def godel1931LicenseIrreversibilitySupport :
    LicenseIrreversibilitySupport godel1931LCELInstance :=
  licenseIrreversibilitySupport_of_semanticTransfer
    godel1931_semanticLicenseTransferSupport

/-- Gödel-side reimport support package assembled from the typed LCEL carrier
and its semantic transfer theorem. -/
def godel1931ReimportReversibilitySupport :
    ReimportReversibilitySupport godel1931LCELInstance :=
  reimportReversibilitySupport_of_semanticTransfer
    godel1931_semanticReimportTransferSupport

/-- Stronger Gödel-side factorization support package assembled from the
stronger visible and sensitive substrate layers. -/
def godel1931BoundaryFactorizationSupport :
    BoundaryFactorizationSupport godel1931LCELInstance :=
  boundaryFactorizationSupport_of_supports
    godel1931ReimportReversibilitySupport
    godel1931LicenseIrreversibilitySupport

/-- Gödel-side LCEL asymmetry witness package assembled from the formal semantic
support layer. -/
def godel1931BaseStepReversibilityWitness :
    BaseStepReversibilityWitness godel1931LCELInstance :=
  baseStepReversibilityWitness_of_semanticBase
    godel1931_semanticBaseLayerSupport

/-- Gödel-side LCEL license witness assembled from the formal semantic transfer
layer. -/
def godel1931LicenseIrreversibilityWitness :
    LicenseIrreversibilityWitness godel1931LCELInstance :=
  licenseIrreversibilityWitness_of_semanticTransfer
    godel1931_semanticLicenseTransferSupport

/-- Gödel-side LCEL reimport witness assembled from the formal semantic transfer
layer. -/
def godel1931ReimportReversibilityWitness :
    ReimportReversibilityWitness godel1931LCELInstance :=
  reimportReversibilityWitness_of_semanticTransfer
    godel1931_semanticReimportTransferSupport

/-- Gödel-side LCEL boundary witness package assembled from the formal semantic
transfer layer. -/
def godel1931ProjectionFactorizationWitness :
    ProjectionFactorizationWitness godel1931LCELInstance :=
  projectionFactorizationWitness_of_semanticTransfers
    godel1931_semanticReimportTransferSupport
    godel1931_semanticLicenseTransferSupport

/-- Gödel-side LCEL asymmetry proposition package. -/
def godel1931LCELReversibilityAsymmetry :
    LCELReversibilityAsymmetry godel1931LCELInstance :=
  lcelReversibilityAsymmetry_of_semanticSupports
    godel1931_semanticBaseLayerSupport
    godel1931_semanticLicenseTransferSupport
    godel1931_semanticReimportTransferSupport

/-- Gödel-side LCEL boundary proposition package. -/
def godel1931LCELBoundaryFactorization :
    LCELBoundaryFactorization godel1931LCELInstance :=
  lcelBoundaryFactorization_of_semanticSupports
    godel1931_semanticReimportTransferSupport
    godel1931_semanticLicenseTransferSupport

/-- Stronger Gödel-side LCEL asymmetry package assembled from the proof-carrying
substrate support records. -/
def godel1931LCELReversibilityAsymmetryFromSupport :
    LCELReversibilityAsymmetry godel1931LCELInstance :=
  lcelReversibilityAsymmetry_of_strongerSupports
    godel1931BaseReversibilitySupport
    godel1931LicenseIrreversibilitySupport
    godel1931ReimportReversibilitySupport

/-- Stronger Gödel-side LCEL boundary-factorization package assembled from the
proof-carrying substrate support record. -/
def godel1931LCELBoundaryFactorizationFromSupport :
    LCELBoundaryFactorization godel1931LCELInstance :=
  lcelBoundaryFactorization_of_strongerSupport
    godel1931BoundaryFactorizationSupport

theorem benchmarkTransport_semanticBaseLayerSupport :
    SemanticBaseLayerSupport benchmarkTransportLCELInstance := by
  rcases OperatorKO7.StructuralIdentityComparison.benchmarkTransportFormalExternalClassicalComparison_semanticSupported with
    ⟨hBase, _, _, _, _, _, _⟩
  simpa [SemanticBaseLayerSupport, benchmarkTransportLCELInstance]

theorem benchmarkTransport_semanticLicenseTransferSupport :
    SemanticLicenseTransferSupport benchmarkTransportLCELInstance := by
  rcases OperatorKO7.StructuralIdentityComparison.benchmarkTransportFormalExternalClassicalComparison_transferSupported with
    ⟨hTransfer, _⟩
  simpa [SemanticLicenseTransferSupport, benchmarkTransportLCELInstance]

theorem benchmarkTransport_semanticReimportTransferSupport :
    SemanticReimportTransferSupport benchmarkTransportLCELInstance := by
  rcases OperatorKO7.StructuralIdentityComparison.benchmarkTransportFormalExternalClassicalComparison_transferSupported with
    ⟨_, hTransfer⟩
  simpa [SemanticReimportTransferSupport, benchmarkTransportLCELInstance]

/-- Benchmark-side base support package assembled from the typed LCEL carrier
and its semantic base-layer theorem. -/
def benchmarkTransportBaseReversibilitySupport :
    BaseReversibilitySupport benchmarkTransportLCELInstance :=
  baseReversibilitySupport_of_semanticBase
    benchmarkTransport_semanticBaseLayerSupport

/-- Benchmark-side license support package assembled from the typed LCEL carrier
and its semantic transfer theorem. -/
def benchmarkTransportLicenseIrreversibilitySupport :
    LicenseIrreversibilitySupport benchmarkTransportLCELInstance :=
  licenseIrreversibilitySupport_of_semanticTransfer
    benchmarkTransport_semanticLicenseTransferSupport

/-- Benchmark-side reimport support package assembled from the typed LCEL
carrier and its semantic transfer theorem. -/
def benchmarkTransportReimportReversibilitySupport :
    ReimportReversibilitySupport benchmarkTransportLCELInstance :=
  reimportReversibilitySupport_of_semanticTransfer
    benchmarkTransport_semanticReimportTransferSupport

/-- Stronger benchmark-side factorization support package assembled from the
stronger visible and sensitive substrate layers. -/
def benchmarkTransportBoundaryFactorizationSupport :
    BoundaryFactorizationSupport benchmarkTransportLCELInstance :=
  boundaryFactorizationSupport_of_supports
    benchmarkTransportReimportReversibilitySupport
    benchmarkTransportLicenseIrreversibilitySupport

/-- Benchmark-side LCEL asymmetry witness package assembled from the formal
semantic support layer. -/
def benchmarkTransportBaseStepReversibilityWitness :
    BaseStepReversibilityWitness benchmarkTransportLCELInstance :=
  baseStepReversibilityWitness_of_semanticBase
    benchmarkTransport_semanticBaseLayerSupport

/-- Benchmark-side LCEL license witness assembled from the formal semantic
transfer layer. -/
def benchmarkTransportLicenseIrreversibilityWitness :
    LicenseIrreversibilityWitness benchmarkTransportLCELInstance :=
  licenseIrreversibilityWitness_of_semanticTransfer
    benchmarkTransport_semanticLicenseTransferSupport

/-- Benchmark-side LCEL reimport witness assembled from the formal semantic
transfer layer. -/
def benchmarkTransportReimportReversibilityWitness :
    ReimportReversibilityWitness benchmarkTransportLCELInstance :=
  reimportReversibilityWitness_of_semanticTransfer
    benchmarkTransport_semanticReimportTransferSupport

/-- Benchmark-side LCEL boundary witness package assembled from the formal
semantic transfer layer. -/
def benchmarkTransportProjectionFactorizationWitness :
    ProjectionFactorizationWitness benchmarkTransportLCELInstance :=
  projectionFactorizationWitness_of_semanticTransfers
    benchmarkTransport_semanticReimportTransferSupport
    benchmarkTransport_semanticLicenseTransferSupport

/-- Benchmark-side LCEL asymmetry proposition package. -/
def benchmarkTransportLCELReversibilityAsymmetry :
    LCELReversibilityAsymmetry benchmarkTransportLCELInstance :=
  lcelReversibilityAsymmetry_of_semanticSupports
    benchmarkTransport_semanticBaseLayerSupport
    benchmarkTransport_semanticLicenseTransferSupport
    benchmarkTransport_semanticReimportTransferSupport

/-- Benchmark-side LCEL boundary proposition package. -/
def benchmarkTransportLCELBoundaryFactorization :
    LCELBoundaryFactorization benchmarkTransportLCELInstance :=
  lcelBoundaryFactorization_of_semanticSupports
    benchmarkTransport_semanticReimportTransferSupport
    benchmarkTransport_semanticLicenseTransferSupport

/-- Stronger benchmark-side LCEL asymmetry package assembled from the
proof-carrying substrate support records. -/
def benchmarkTransportLCELReversibilityAsymmetryFromSupport :
    LCELReversibilityAsymmetry benchmarkTransportLCELInstance :=
  lcelReversibilityAsymmetry_of_strongerSupports
    benchmarkTransportBaseReversibilitySupport
    benchmarkTransportLicenseIrreversibilitySupport
    benchmarkTransportReimportReversibilitySupport

/-- Stronger benchmark-side LCEL boundary-factorization package assembled from
the proof-carrying substrate support record. -/
def benchmarkTransportLCELBoundaryFactorizationFromSupport :
    LCELBoundaryFactorization benchmarkTransportLCELInstance :=
  lcelBoundaryFactorization_of_strongerSupport
    benchmarkTransportBoundaryFactorizationSupport

end OperatorKO7.LCELReversibility
