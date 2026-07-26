import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance

/-!
# Proof-carrying LCEL support objects

This file packages explicit sentences and proofs already supplied by the LCEL
support records. It defines four record types: a provable/unprovable sentence
pair, a blocked-sentence reflection package, a reimport certification package,
and a boundary-factorization package. The extraction functions project those
fields from `BaseReversibilitySupport`, `LicenseIrreversibilitySupport`,
`ReimportReversibilitySupport`, and `BoundaryFactorizationSupport`.

The declarations do not define a concrete step relation or prove that a
projection is a partial inverse. Terms such as "reversibility" and
"irreversibility" below refer to the corresponding LCEL record interfaces.
Each instantiated result therefore inherits the assumptions and semantics of
its supplied support record.
-/

namespace OperatorKO7.LCELSubstrateMathematics

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELDpInstance

/-! ## Provable/unprovable sentence package -/

/-- A proof-carrying pair of base-theory sentences: one provable sentence and
the designated boundary sentence, together with its non-provability, reference
truth, and distinctness from the first sentence. -/
structure BaseReversibilityTheorem (L : FormalLCELInstance) : Type where
  /-- A sentence that the base theory proves. -/
  provedSentence : L.comparison.baseTheoryContent.Sentence
  /-- Proof that the provable sentence is indeed provable. -/
  provedSentence_proved :
    L.comparison.baseTheoryContent.proves provedSentence
  /-- The designated boundary sentence, which the base theory does not prove. -/
  unprovedSentence : L.comparison.baseTheoryContent.Sentence
  /-- The unproved sentence is the designated boundary sentence. -/
  unprovedSentence_eq :
    unprovedSentence =
      L.boundaryObject.boundarySentence L.boundaryObject.designated
  /-- The unproved sentence is not provable in the base theory. -/
  unprovedSentence_not_provable :
    ¬ L.comparison.baseTheoryContent.proves unprovedSentence
  /-- The unproved sentence is true in the reference model. -/
  unprovedSentence_true :
    L.comparison.baseTheoryContent.trueInReferenceModel unprovedSentence
  /-- The provable and unprovable sentences are distinct. -/
  distinct : provedSentence ≠ unprovedSentence

namespace BaseReversibilityTheorem

/-- The proved sentence is not equal to the boundary sentence, via
`unprovedSentence_eq` and `distinct`. -/
theorem provedSentence_ne_boundary
    {L : FormalLCELInstance}
    (T : BaseReversibilityTheorem L) :
    T.provedSentence ≠
      L.boundaryObject.boundarySentence L.boundaryObject.designated := by
  intro h
  apply T.distinct
  rw [T.unprovedSentence_eq]
  exact h

/-- Project a `BaseReversibilityTheorem` to the two-proposition
`BaseStepReversibilityWitness` interface. -/
def toBaseStepReversibilityWitness
    {L : FormalLCELInstance}
    (T : BaseReversibilityTheorem L) :
    BaseStepReversibilityWitness L where
  isReversible :=
    L.comparison.baseTheoryContent.proves T.provedSentence
      ∧ ¬ L.comparison.baseTheoryContent.proves T.unprovedSentence
  holds := ⟨T.provedSentence_proved, T.unprovedSentence_not_provable⟩

end BaseReversibilityTheorem

/-! ## Extraction from proof-carrying support records -/

/-- Package the fields of a supplied `BaseReversibilitySupport` record. The
distinctness proof follows from its provability and non-provability fields. -/
def baseReversibilityTheorem_of_support
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    BaseReversibilityTheorem L where
  provedSentence := S.internalSentence
  provedSentence_proved := S.internalSentenceProved
  unprovedSentence :=
    L.boundaryObject.boundarySentence L.boundaryObject.designated
  unprovedSentence_eq := rfl
  unprovedSentence_not_provable := by
    simpa using BaseReversibilitySupport.designatedBoundaryNotProvable S
  unprovedSentence_true := by
    simpa using BaseReversibilitySupport.designatedBoundaryTrueInReferenceModel S
  distinct := by
    intro h
    apply BaseReversibilitySupport.designatedBoundaryNotProvable S
    rw [← h]
    exact S.internalSentenceProved

/-! ## Instantiations from the supplied support records -/

/-- Gödel-side proof-carrying base sentence package. -/
def godel1931BaseReversibilityTheorem :
    BaseReversibilityTheorem godel1931LCELInstance :=
  baseReversibilityTheorem_of_support godel1931BaseReversibilitySupport

/-- Benchmark-transport-side proof-carrying base sentence package. -/
def benchmarkTransportBaseReversibilityTheorem :
    BaseReversibilityTheorem benchmarkTransportLCELInstance :=
  baseReversibilityTheorem_of_support benchmarkTransportBaseReversibilitySupport

/-- Native DP / emitter-side proof-carrying base sentence package. -/
def dpEmitterBaseReversibilityTheorem :
    BaseReversibilityTheorem dpEmitterLCELInstance :=
  baseReversibilityTheorem_of_support dpEmitterBaseReversibilitySupport

/-! ## Projection to the proposition-only witness layer

The following definitions retain only the provability and non-provability
conjunction used by `BaseStepReversibilityWitness`. -/

/-- Gödel-side base-step witness projected from its sentence package. -/
def godel1931BaseStepReversibilityWitness_ofTheorem :
    BaseStepReversibilityWitness godel1931LCELInstance :=
  BaseReversibilityTheorem.toBaseStepReversibilityWitness
    godel1931BaseReversibilityTheorem

/-- Benchmark-transport-side base-step witness projected from its sentence
package. -/
def benchmarkTransportBaseStepReversibilityWitness_ofTheorem :
    BaseStepReversibilityWitness benchmarkTransportLCELInstance :=
  BaseReversibilityTheorem.toBaseStepReversibilityWitness
    benchmarkTransportBaseReversibilityTheorem

/-- Native DP-side base-step witness projected from its sentence package. -/
def dpEmitterBaseStepReversibilityWitness_ofTheorem :
    BaseStepReversibilityWitness dpEmitterLCELInstance :=
  BaseReversibilityTheorem.toBaseStepReversibilityWitness
    dpEmitterBaseReversibilityTheorem

/-! ## Blocked-sentence reflection package -/

/-- A proof-carrying blocked-sentence package containing base non-provability,
reference-model truth, stronger-framework reflection, external-license
inhabitation, licensed admission, and their packaged conjunction. -/
structure LicenseIrreversibilityTheorem (L : FormalLCELInstance) : Type where
  /-- The blocked sentence targeted by the external license. -/
  blockedSentence : L.comparison.baseTheoryContent.Sentence
  /-- The blocked sentence is the reflection-content's designated blocked
  sentence. -/
  blockedSentence_eq :
    blockedSentence = L.comparison.reflectionContent.blockedSentence
  /-- The blocked sentence is not provable in the base theory. -/
  blocked_not_provable :
    ¬ L.comparison.baseTheoryContent.proves blockedSentence
  /-- The blocked sentence is true in the reference model. -/
  blocked_true :
    L.comparison.baseTheoryContent.trueInReferenceModel blockedSentence
  /-- The stronger framework reflects the blocked sentence. -/
  stronger_reflects_blocked :
    L.comparison.reflectionContent.reflects
      L.comparison.reflectionContent.strongerFramework
      blockedSentence
  /-- The external-license slot is inhabited. -/
  externalLicenseHolds : L.externalLicenseWitness
  /-- The blocked sentence is licensed for admission. -/
  blocked_licensedAdmission :
    L.comparison.reflectionContent.licensedAdmission blockedSentence
  /-- The conjunction of base non-provability and stronger-framework
  reflection for the designated blocked sentence. -/
  licenseExtendsBase :
    (¬ L.comparison.baseTheoryContent.proves blockedSentence)
      ∧ L.comparison.reflectionContent.reflects
          L.comparison.reflectionContent.strongerFramework
          blockedSentence

namespace LicenseIrreversibilityTheorem

/-- Project to the proposition-only `LicenseIrreversibilityWitness` interface. -/
def toLicenseIrreversibilityWitness
    {L : FormalLCELInstance}
    (T : LicenseIrreversibilityTheorem L) :
    LicenseIrreversibilityWitness L where
  isIrreversible :=
    (¬ L.comparison.baseTheoryContent.proves T.blockedSentence)
      ∧ L.comparison.reflectionContent.reflects
          L.comparison.reflectionContent.strongerFramework
          T.blockedSentence
  holds := T.licenseExtendsBase

end LicenseIrreversibilityTheorem

/-- Package the fields of a supplied license support record. -/
def licenseIrreversibilityTheorem_of_support
    {L : FormalLCELInstance}
    (S : LicenseIrreversibilitySupport L) :
    LicenseIrreversibilityTheorem L where
  blockedSentence := L.comparison.reflectionContent.blockedSentence
  blockedSentence_eq := rfl
  blocked_not_provable := S.blockedNotProvable
  blocked_true := S.blockedTrue
  stronger_reflects_blocked := S.strongerFrameworkReflectsBlocked
  externalLicenseHolds := S.externalLicenseHolds
  blocked_licensedAdmission := S.blockedLicensedAdmission
  licenseExtendsBase := ⟨S.blockedNotProvable, S.strongerFrameworkReflectsBlocked⟩

/-- Gödel-side blocked-sentence reflection package. -/
def godel1931LicenseIrreversibilityTheorem :
    LicenseIrreversibilityTheorem godel1931LCELInstance :=
  licenseIrreversibilityTheorem_of_support
    godel1931LicenseIrreversibilitySupport

/-- Benchmark-transport-side blocked-sentence reflection package. -/
def benchmarkTransportLicenseIrreversibilityTheorem :
    LicenseIrreversibilityTheorem benchmarkTransportLCELInstance :=
  licenseIrreversibilityTheorem_of_support
    benchmarkTransportLicenseIrreversibilitySupport

/-- Native DP-side blocked-sentence reflection package. -/
def dpEmitterLicenseIrreversibilityTheorem :
    LicenseIrreversibilityTheorem dpEmitterLCELInstance :=
  licenseIrreversibilityTheorem_of_support
    dpEmitterLicenseIrreversibilitySupport

/-! ## Reimport certification package -/

/-- A proof-carrying package for the designated imported sentence, including
reference-model truth, witness certification, reimport-class inhabitation, and
annotation-decoder coherence. -/
structure ReimportReversibilityTheorem (L : FormalLCELInstance) : Type where
  /-- The imported sentence. -/
  importedSentence : L.comparison.baseTheoryContent.Sentence
  /-- The imported sentence is the reimport-content's designated imported
  sentence. -/
  importedSentence_eq :
    importedSentence = L.comparison.reimportContent.importedSentence
  /-- The imported sentence is true in the reference model. -/
  imported_true :
    L.comparison.baseTheoryContent.trueInReferenceModel importedSentence
  /-- The reimport witness certifies the imported sentence. -/
  witness_certifies_imported :
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      importedSentence
  /-- The reimport-class slot is inhabited. -/
  reimportClassHolds : L.reimportClassWitness
  /-- The annotation functor decodes the designated annotation to the
  imported sentence. -/
  annotationDecodes_imported :
    L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness)
      = importedSentence
  /-- Certification is inherited by the decoded annotation. -/
  annotationCertifiesDecoded :
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      (L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness))

namespace ReimportReversibilityTheorem

/-- Project to the proposition-only `ReimportReversibilityWitness` interface. -/
def toReimportReversibilityWitness
    {L : FormalLCELInstance}
    (T : ReimportReversibilityTheorem L) :
    ReimportReversibilityWitness L where
  isReversibleOnReimportClass :=
    L.reimportClassWitness
      ∧ L.comparison.reimportContent.certifies
          L.comparison.reimportContent.witness
          T.importedSentence
      ∧ L.comparison.baseTheoryContent.trueInReferenceModel T.importedSentence
  holds :=
    ⟨T.reimportClassHolds, T.witness_certifies_imported, T.imported_true⟩

end ReimportReversibilityTheorem

/-- Package the fields of a supplied reimport support record. -/
def reimportReversibilityTheorem_of_support
    {L : FormalLCELInstance}
    (S : ReimportReversibilitySupport L) :
    ReimportReversibilityTheorem L where
  importedSentence := L.comparison.reimportContent.importedSentence
  importedSentence_eq := rfl
  imported_true := S.importedTrue
  witness_certifies_imported := S.witnessCertifiesImported
  reimportClassHolds := S.reimportClassHolds
  annotationDecodes_imported := S.annotationDecodesImported
  annotationCertifiesDecoded := S.annotationCertifiesDecoded

/-- Gödel-side reimport certification package. -/
def godel1931ReimportReversibilityTheorem :
    ReimportReversibilityTheorem godel1931LCELInstance :=
  reimportReversibilityTheorem_of_support
    godel1931ReimportReversibilitySupport

/-- Benchmark-transport-side reimport certification package. -/
def benchmarkTransportReimportReversibilityTheorem :
    ReimportReversibilityTheorem benchmarkTransportLCELInstance :=
  reimportReversibilityTheorem_of_support
    benchmarkTransportReimportReversibilitySupport

/-- Native DP-side reimport certification package. -/
def dpEmitterReimportReversibilityTheorem :
    ReimportReversibilityTheorem dpEmitterLCELInstance :=
  reimportReversibilityTheorem_of_support
    dpEmitterReimportReversibilitySupport

/-! ## Boundary-factorization package -/

/-- A record combining the reimport and blocked-sentence packages with two
sentence equalities and the supplied boundary-realization witness. -/
structure BoundaryFactorizationTheorem (L : FormalLCELInstance) : Type where
  /-- Reimport-side certification package. -/
  visible : ReimportReversibilityTheorem L
  /-- Blocked-sentence reflection package. -/
  sensitive : LicenseIrreversibilityTheorem L
  /-- Coherence equality between the designated obstruction's blocked
  sentence and the reflection-content's blocked sentence. -/
  obstructionBlockedEqReflectionBlocked :
    L.comparison.obstructionContent.blockedBy
        L.comparison.obstructionContent.witness
      = L.comparison.reflectionContent.blockedSentence
  /-- Coherence equality between the reflection-content's blocked sentence
  and the reimport-content's imported sentence. -/
  reflectionBlockedEqImported :
    L.comparison.reflectionContent.blockedSentence
      = L.comparison.reimportContent.importedSentence
  /-- The boundary slot is realized. -/
  boundaryRealized : L.boundaryObject.realized

namespace BoundaryFactorizationTheorem

/-- Project to the proposition-only `ProjectionFactorizationWitness`
interface. -/
def toProjectionFactorizationWitness
    {L : FormalLCELInstance}
    (T : BoundaryFactorizationTheorem L) :
    ProjectionFactorizationWitness L where
  visibleViaReversible :=
    L.reimportClassWitness
      ∧ L.comparison.reimportContent.certifies
          L.comparison.reimportContent.witness
          T.visible.importedSentence
      ∧ L.comparison.baseTheoryContent.trueInReferenceModel
          T.visible.importedSentence
  sensitiveToIrreversible :=
    ((¬ L.comparison.baseTheoryContent.proves T.sensitive.blockedSentence)
      ∧ L.comparison.reflectionContent.reflects
          L.comparison.reflectionContent.strongerFramework
          T.sensitive.blockedSentence)
    ∧ L.boundaryObject.realized
  visibleHolds :=
    ⟨T.visible.reimportClassHolds,
      T.visible.witness_certifies_imported,
      T.visible.imported_true⟩
  sensitiveHolds :=
    ⟨T.sensitive.licenseExtendsBase, T.boundaryRealized⟩

end BoundaryFactorizationTheorem

/-- Package the fields of a supplied boundary-factorization support record. -/
def boundaryFactorizationTheorem_of_support
    {L : FormalLCELInstance}
    (S : BoundaryFactorizationSupport L) :
    BoundaryFactorizationTheorem L where
  visible := reimportReversibilityTheorem_of_support S.visibleSupport
  sensitive := licenseIrreversibilityTheorem_of_support S.sensitiveSupport
  obstructionBlockedEqReflectionBlocked :=
    S.obstructionBlockedEqReflectionBlocked
  reflectionBlockedEqImported := S.reflectionBlockedEqImported
  boundaryRealized := S.boundaryRealized

/-- Gödel-side boundary-factorization package. -/
def godel1931BoundaryFactorizationTheorem :
    BoundaryFactorizationTheorem godel1931LCELInstance :=
  boundaryFactorizationTheorem_of_support
    godel1931BoundaryFactorizationSupport

/-- Benchmark-transport-side boundary-factorization package. -/
def benchmarkTransportBoundaryFactorizationTheorem :
    BoundaryFactorizationTheorem benchmarkTransportLCELInstance :=
  boundaryFactorizationTheorem_of_support
    benchmarkTransportBoundaryFactorizationSupport

/-- Native DP-side boundary-factorization package. -/
def dpEmitterBoundaryFactorizationTheorem :
    BoundaryFactorizationTheorem dpEmitterLCELInstance :=
  boundaryFactorizationTheorem_of_support
    dpEmitterBoundaryFactorizationSupport

end OperatorKO7.LCELSubstrateMathematics
