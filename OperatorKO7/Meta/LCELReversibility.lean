import OperatorKO7.Meta.LCELSchema

/-!
# LCEL Reversibility and Boundary Factorization

Witness-parameterized packaging for the operational-inexpressibility manuscript Propositions 5.8
(`prop:lcel-reversibility`) and 5.9 (`prop:lcel-boundary-factorization`).

This file is intentionally conservative. It does **not** pretend to derive the
paper's reversibility or factorization content from the LCEL carrier alone.
Those claims are instance-sensitive and require external mathematics:

- Axelsen--Glück / Nishida--Palacios--Vidal style partial-injection facts on
  the step-duplicating side, or
- Kreisel--Lévy / Beklemishev style conservativity facts on the reflection
  side.

What is mechanized here is the honest schema-level packaging:

- explicit witness structures for the three clauses of reversibility
  asymmetry, and
- an explicit witness structure for the projection factorization.

Any future substantive instance proof should enter by constructing these
witnesses, not by weakening the theorem statements.
-/

namespace OperatorKO7.LCELReversibility

open OperatorKO7.LCELSchema

/-- the operational-inexpressibility manuscript Proposition 5.8 clause (1): base step-relation is reversible after
projecting to the chosen observable boundary. -/
structure BaseStepReversibilityWitness (L : FormalLCELInstance) : Type where
  isReversible : Prop
  holds : isReversible

/-- the operational-inexpressibility manuscript Proposition 5.8 clause (2): adjoining the external license is not
reversible at that same projection level. -/
structure LicenseIrreversibilityWitness (L : FormalLCELInstance) : Type where
  isIrreversible : Prop
  holds : isIrreversible

/-- the operational-inexpressibility manuscript Proposition 5.8 clause (3): on the designated reimport class the
licensed import is reversible back to a base-layer derivation. -/
structure ReimportReversibilityWitness (L : FormalLCELInstance) : Type where
  isReversibleOnReimportClass : Prop
  holds : isReversibleOnReimportClass

/-- Three-clause output package for the operational-inexpressibility manuscript Proposition 5.8. -/
structure LCELReversibilityAsymmetry (L : FormalLCELInstance) : Type where
  baseReversible : Prop
  licenseIrreversible : Prop
  reimportReversibleOnReimportClass : Prop
  holdsBase : baseReversible
  holdsLicense : licenseIrreversible
  holdsReimport : reimportReversibleOnReimportClass

/-- the operational-inexpressibility manuscript Proposition 5.8 in honest artifact form: if the three constituent
reversibility witnesses are supplied, the named asymmetry package exists. -/
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

/-- Witness for the factorization `π_T = π_rev ∘ π_irr` used in the operational-inexpressibility manuscript
Proposition 5.9. The two proposition fields record exactly the two aspects that
matter at schema level:

- the reversible visible component, and
- the irreversible boundary-sensitive component.
-/
structure ProjectionFactorizationWitness (L : FormalLCELInstance) : Type where
  visibleViaReversible : Prop
  sensitiveToIrreversible : Prop
  visibleHolds : visibleViaReversible
  sensitiveHolds : sensitiveToIrreversible

/-- Named output package for the operational-inexpressibility manuscript Proposition 5.9. -/
structure LCELBoundaryFactorization (L : FormalLCELInstance) : Type where
  hasReversibleProjection : Prop
  hasIrreversibleQuotient : Prop
  boundarySensitiveToIrreversible : Prop
  holdsReversible : hasReversibleProjection
  holdsIrreversible : hasIrreversibleQuotient
  holdsBoundary : boundarySensitiveToIrreversible

/-- the operational-inexpressibility manuscript Proposition 5.9 in honest artifact form: once a factorization
witness is supplied, the boundary-factorization package is immediate. -/
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

/-! ## Honest semantic support adapters -/

/-- Current artifact-facing semantic support for the base layer of a typed LCEL
instance. This is the theorem-backed proposition currently available from the
formal external comparison object itself. -/
def SemanticBaseLayerSupport (L : FormalLCELInstance) : Prop :=
  L.comparison.baseTheoryContent.hasInternalProofLayer

/-- Current artifact-facing semantic support for the obstruction-to-license
transfer used by the LCEL asymmetry packaging. -/
def SemanticLicenseTransferSupport (L : FormalLCELInstance) : Prop :=
  L.comparison.semanticCoherence.obstructionTransfersToReflection

/-- Current artifact-facing semantic support for the licensed reimport stage used
by the LCEL asymmetry packaging. -/
def SemanticReimportTransferSupport (L : FormalLCELInstance) : Prop :=
  L.comparison.semanticCoherence.reflectionTransfersToReimport

/-! ## Stronger proof-carrying substrate support records -/

/-- Stronger support record for the base-layer side of LCEL reversibility.

This keeps the current artifact-facing semantic support proposition, but
adds the designated internal proof witness and the designated boundary witness
used by the current canonical LCEL instances. -/
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

This carries not just the current obstruction-to-reflection transfer
proposition, but also the concrete blocked sentence, its non-provability and
truth, and the designated stronger-framework / license data witnessing that
transfer. -/
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

This packages the current reflection-to-reimport transfer together with the
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

This is intentionally still instance-sensitive: it carries the stronger
reimport-visible support and the stronger license-sensitive support, together
with the coherence equalities that tie the obstruction, reflection, and
reimport layers into one boundary-sensitive factorization story. -/
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

/-- Build stronger base-layer support from the current LCEL carrier and the
currently available base-layer semantic theorem. -/
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

/-- Build stronger license-side support from the current LCEL carrier and the
currently available obstruction-to-reflection transfer theorem. -/
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

/-- Build stronger reimport-side support from the current LCEL carrier and the
currently available reflection-to-reimport transfer theorem. -/
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

/-- Turn the currently mechanized base-layer semantic support into the abstract
LCEL base-step reversibility witness slot. This does not claim that the full
paper proposition has been derived from the carrier alone; it only records the
current theorem-backed support surface honestly. -/
def baseStepReversibilityWitness_of_semanticBase
    {L : FormalLCELInstance}
    (hBase : SemanticBaseLayerSupport L) :
    BaseStepReversibilityWitness L :=
  { isReversible := SemanticBaseLayerSupport L
    holds := hBase }

/-- Turn the currently mechanized obstruction-to-license transfer support into
the abstract LCEL license-irreversibility witness slot. -/
def licenseIrreversibilityWitness_of_semanticTransfer
    {L : FormalLCELInstance}
    (hLicense : SemanticLicenseTransferSupport L) :
    LicenseIrreversibilityWitness L :=
  { isIrreversible := SemanticLicenseTransferSupport L
    holds := hLicense }

/-- Turn the currently mechanized reflection-to-reimport transfer support into
the abstract LCEL reimport-reversibility witness slot. -/
def reimportReversibilityWitness_of_semanticTransfer
    {L : FormalLCELInstance}
    (hReimport : SemanticReimportTransferSupport L) :
    ReimportReversibilityWitness L :=
  { isReversibleOnReimportClass := SemanticReimportTransferSupport L
    holds := hReimport }

/-- Package the current formal external transfer surface as a boundary-
factorization witness. The reversible-visible component is represented by the
reflection-to-reimport transfer, and the irreversible-sensitive component by the
obstruction-to-reflection transfer. -/
def projectionFactorizationWitness_of_semanticTransfers
    {L : FormalLCELInstance}
    (hVisible : SemanticReimportTransferSupport L)
    (hSensitive : SemanticLicenseTransferSupport L) :
    ProjectionFactorizationWitness L :=
  { visibleViaReversible := SemanticReimportTransferSupport L
    sensitiveToIrreversible := SemanticLicenseTransferSupport L
    visibleHolds := hVisible
    sensitiveHolds := hSensitive }

/-- Canonical LCEL reversibility-asymmetry package assembled directly from the
current semantic support surface. -/
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

/-- Canonical LCEL boundary-factorization package assembled directly from the
current semantic support surface. -/
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

/-- Stronger Gödel-side base support package assembled from the typed LCEL
carrier and the current semantic base-layer theorem. -/
def godel1931BaseReversibilitySupport :
    BaseReversibilitySupport godel1931LCELInstance :=
  baseReversibilitySupport_of_semanticBase
    godel1931_semanticBaseLayerSupport

/-- Stronger Gödel-side license-side support package assembled from the typed
LCEL carrier and the current semantic transfer theorem. -/
def godel1931LicenseIrreversibilitySupport :
    LicenseIrreversibilitySupport godel1931LCELInstance :=
  licenseIrreversibilitySupport_of_semanticTransfer
    godel1931_semanticLicenseTransferSupport

/-- Stronger Gödel-side reimport-side support package assembled from the typed
LCEL carrier and the current semantic transfer theorem. -/
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

/-- Honest Gödel-side LCEL asymmetry witness package assembled from the current
formal semantic support layer. -/
def godel1931BaseStepReversibilityWitness :
    BaseStepReversibilityWitness godel1931LCELInstance :=
  baseStepReversibilityWitness_of_semanticBase
    godel1931_semanticBaseLayerSupport

/-- Honest Gödel-side LCEL license witness assembled from the current formal
semantic transfer layer. -/
def godel1931LicenseIrreversibilityWitness :
    LicenseIrreversibilityWitness godel1931LCELInstance :=
  licenseIrreversibilityWitness_of_semanticTransfer
    godel1931_semanticLicenseTransferSupport

/-- Honest Gödel-side LCEL reimport witness assembled from the current formal
semantic transfer layer. -/
def godel1931ReimportReversibilityWitness :
    ReimportReversibilityWitness godel1931LCELInstance :=
  reimportReversibilityWitness_of_semanticTransfer
    godel1931_semanticReimportTransferSupport

/-- Honest Gödel-side LCEL boundary-factorization witness package assembled from
the current formal semantic transfer layer. -/
def godel1931ProjectionFactorizationWitness :
    ProjectionFactorizationWitness godel1931LCELInstance :=
  projectionFactorizationWitness_of_semanticTransfers
    godel1931_semanticReimportTransferSupport
    godel1931_semanticLicenseTransferSupport

/-- Honest Gödel-side LCEL reversibility-asymmetry package. -/
def godel1931LCELReversibilityAsymmetry :
    LCELReversibilityAsymmetry godel1931LCELInstance :=
  lcelReversibilityAsymmetry_of_semanticSupports
    godel1931_semanticBaseLayerSupport
    godel1931_semanticLicenseTransferSupport
    godel1931_semanticReimportTransferSupport

/-- Honest Gödel-side LCEL boundary-factorization package. -/
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

/-- Stronger benchmark-side base support package assembled from the typed LCEL
carrier and the current semantic base-layer theorem. -/
def benchmarkTransportBaseReversibilitySupport :
    BaseReversibilitySupport benchmarkTransportLCELInstance :=
  baseReversibilitySupport_of_semanticBase
    benchmarkTransport_semanticBaseLayerSupport

/-- Stronger benchmark-side license-side support package assembled from the
typed LCEL carrier and the current semantic transfer theorem. -/
def benchmarkTransportLicenseIrreversibilitySupport :
    LicenseIrreversibilitySupport benchmarkTransportLCELInstance :=
  licenseIrreversibilitySupport_of_semanticTransfer
    benchmarkTransport_semanticLicenseTransferSupport

/-- Stronger benchmark-side reimport-side support package assembled from the
typed LCEL carrier and the current semantic transfer theorem. -/
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

/-- Honest benchmark-side LCEL asymmetry witness package assembled from the
current formal semantic support layer. -/
def benchmarkTransportBaseStepReversibilityWitness :
    BaseStepReversibilityWitness benchmarkTransportLCELInstance :=
  baseStepReversibilityWitness_of_semanticBase
    benchmarkTransport_semanticBaseLayerSupport

/-- Honest benchmark-side LCEL license witness assembled from the current formal
semantic transfer layer. -/
def benchmarkTransportLicenseIrreversibilityWitness :
    LicenseIrreversibilityWitness benchmarkTransportLCELInstance :=
  licenseIrreversibilityWitness_of_semanticTransfer
    benchmarkTransport_semanticLicenseTransferSupport

/-- Honest benchmark-side LCEL reimport witness assembled from the current
formal semantic transfer layer. -/
def benchmarkTransportReimportReversibilityWitness :
    ReimportReversibilityWitness benchmarkTransportLCELInstance :=
  reimportReversibilityWitness_of_semanticTransfer
    benchmarkTransport_semanticReimportTransferSupport

/-- Honest benchmark-side LCEL boundary-factorization witness package assembled
from the current formal semantic transfer layer. -/
def benchmarkTransportProjectionFactorizationWitness :
    ProjectionFactorizationWitness benchmarkTransportLCELInstance :=
  projectionFactorizationWitness_of_semanticTransfers
    benchmarkTransport_semanticReimportTransferSupport
    benchmarkTransport_semanticLicenseTransferSupport

/-- Honest benchmark-side LCEL reversibility-asymmetry package. -/
def benchmarkTransportLCELReversibilityAsymmetry :
    LCELReversibilityAsymmetry benchmarkTransportLCELInstance :=
  lcelReversibilityAsymmetry_of_semanticSupports
    benchmarkTransport_semanticBaseLayerSupport
    benchmarkTransport_semanticLicenseTransferSupport
    benchmarkTransport_semanticReimportTransferSupport

/-- Honest benchmark-side LCEL boundary-factorization package. -/
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
