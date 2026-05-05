import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance

/-!
# LCEL Theorem-Strength Substrate Mathematics

Workstream B of the LCEL universal-theorem roadmap: upgrade the witness
structures of `LCELReversibility.lean` from the current propositional-pair
packaging (`{isReversible : Prop, holds : isReversible}`) to theorem-strength
objects carrying the concrete mathematical content the paper gestures at.

This file makes a conservative first-pass upgrade. It does not attempt to
formalize literal `π_T`-reversibility as a partial-injection on a concrete
step relation; that is a larger program and would require explicit step-
relation data on each LCEL instance. What this file does supply is:

- `BaseReversibilityTheorem L`, a theorem-strength object that carries an
  explicit provable-sentence witness, an explicit unprovable-boundary-sentence
  witness, and a distinctness theorem between them;
- an extraction `baseReversibilityTheorem_of_support` from the proof-carrying
  `BaseReversibilitySupport` record of `LCELReversibility.lean`;
- canonical realizations of the theorem object on the Gödel, benchmark-
  transport, and native DP / emitter sides.

The distinctness component is the key theorem-strength content: on every
canonical LCEL instance the base theory does have some provable sentences
and does have a designated boundary sentence that it does not prove, and
these two sentences are therefore provably distinct. This is a stronger
statement than the propositional `isReversible` witness, because it produces
explicit separating sentences rather than an abstract proposition.
-/

namespace OperatorKO7.LCELSubstrateMathematics

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELDpInstance

/-! ## Theorem-strength base reversibility object -/

/-- Theorem-strength base-layer reversibility object for the operational-inexpressibility manuscript Proposition
5.8 clause (1).

The object carries two named sentences on the base theory together with
concrete proofs that they separate: one is provable, the other is the
designated boundary sentence (true but unprovable). Their distinctness is a
theorem, not a propositional packaging. -/
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
  /-- The two sentences are distinct. This is the theorem-strength content:
  a `provedSentence` that is provable and an `unprovedSentence` that is not
  cannot be equal. -/
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

/-- Downgrade a theorem-strength base reversibility object to the abstract
`BaseStepReversibilityWitness` packaging used elsewhere in the LCEL stack.
This shows the theorem-strength layer dominates the propositional packaging. -/
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

/-- Every `BaseReversibilitySupport` record extracts a theorem-strength base
reversibility object. The distinctness clause follows from the provability
of the internal sentence and the non-provability of the designated boundary
sentence: they cannot be equal. -/
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

/-! ## Canonical theorem-strength realizations -/

/-- Gödel-side theorem-strength base reversibility object. -/
def godel1931BaseReversibilityTheorem :
    BaseReversibilityTheorem godel1931LCELInstance :=
  baseReversibilityTheorem_of_support godel1931BaseReversibilitySupport

/-- Benchmark-transport-side theorem-strength base reversibility object. -/
def benchmarkTransportBaseReversibilityTheorem :
    BaseReversibilityTheorem benchmarkTransportLCELInstance :=
  baseReversibilityTheorem_of_support benchmarkTransportBaseReversibilitySupport

/-- Native DP / emitter-side theorem-strength base reversibility object. -/
def dpEmitterBaseReversibilityTheorem :
    BaseReversibilityTheorem dpEmitterLCELInstance :=
  baseReversibilityTheorem_of_support dpEmitterBaseReversibilitySupport

/-! ## Downgrade to the existing witness layer

The theorem-strength object yields the existing `BaseStepReversibilityWitness`
packaging used by `LCELReversibility.lean`, so it can be connectorged into the
existing LCEL substrate machinery without any other changes. -/

/-- Gödel-side base-step reversibility witness derived from the theorem-strength
object. -/
def godel1931BaseStepReversibilityWitness_ofTheorem :
    BaseStepReversibilityWitness godel1931LCELInstance :=
  BaseReversibilityTheorem.toBaseStepReversibilityWitness
    godel1931BaseReversibilityTheorem

/-- Benchmark-transport-side base-step reversibility witness derived from the
theorem-strength object. -/
def benchmarkTransportBaseStepReversibilityWitness_ofTheorem :
    BaseStepReversibilityWitness benchmarkTransportLCELInstance :=
  BaseReversibilityTheorem.toBaseStepReversibilityWitness
    benchmarkTransportBaseReversibilityTheorem

/-- Native DP-side base-step reversibility witness derived from the
theorem-strength object. -/
def dpEmitterBaseStepReversibilityWitness_ofTheorem :
    BaseStepReversibilityWitness dpEmitterLCELInstance :=
  BaseReversibilityTheorem.toBaseStepReversibilityWitness
    dpEmitterBaseReversibilityTheorem

/-! ## Theorem-strength license irreversibility object -/

/-- Theorem-strength license-side irreversibility object for the operational-inexpressibility manuscript
Proposition 5.8 clause (2).

The object carries the designated blocked sentence, its non-provability in
the base, its truth in the reference model, a reflection witness for it
from the stronger framework, an external-license witness, and a packaged
distinctness statement showing the stronger framework genuinely extends
the base on this sentence. -/
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
  /-- Packaged license-extension content: the base does not prove the
  blocked sentence, and the stronger framework does reflect it. This is
  the theorem-strength statement that the license genuinely extends the
  base on the designated blocked sentence. -/
  licenseExtendsBase :
    (¬ L.comparison.baseTheoryContent.proves blockedSentence)
      ∧ L.comparison.reflectionContent.reflects
          L.comparison.reflectionContent.strongerFramework
          blockedSentence

namespace LicenseIrreversibilityTheorem

/-- Downgrade to the abstract `LicenseIrreversibilityWitness` used in the
existing LCEL substrate machinery. -/
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

/-- Extraction of a theorem-strength license irreversibility object from the
proof-carrying license support record. -/
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

/-- Gödel-side theorem-strength license irreversibility object. -/
def godel1931LicenseIrreversibilityTheorem :
    LicenseIrreversibilityTheorem godel1931LCELInstance :=
  licenseIrreversibilityTheorem_of_support
    godel1931LicenseIrreversibilitySupport

/-- Benchmark-transport-side theorem-strength license irreversibility object. -/
def benchmarkTransportLicenseIrreversibilityTheorem :
    LicenseIrreversibilityTheorem benchmarkTransportLCELInstance :=
  licenseIrreversibilityTheorem_of_support
    benchmarkTransportLicenseIrreversibilitySupport

/-- Native DP-side theorem-strength license irreversibility object. -/
def dpEmitterLicenseIrreversibilityTheorem :
    LicenseIrreversibilityTheorem dpEmitterLCELInstance :=
  licenseIrreversibilityTheorem_of_support
    dpEmitterLicenseIrreversibilitySupport

/-! ## Theorem-strength reimport reversibility object -/

/-- Theorem-strength reimport-side reversibility object for the operational-inexpressibility manuscript
Proposition 5.8 clause (3).

The object carries the imported sentence, its truth, its certification by
the reimport witness, the reimport-class slot witness, and the decoder
coherence that ties the annotation functor back to the imported sentence.
Distinctness content: certification of the imported sentence is inherited
by the decoded annotation. -/
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

/-- Downgrade to the abstract `ReimportReversibilityWitness` used in the
existing LCEL substrate machinery. -/
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

/-- Extraction of a theorem-strength reimport reversibility object from the
proof-carrying reimport support record. -/
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

/-- Gödel-side theorem-strength reimport reversibility object. -/
def godel1931ReimportReversibilityTheorem :
    ReimportReversibilityTheorem godel1931LCELInstance :=
  reimportReversibilityTheorem_of_support
    godel1931ReimportReversibilitySupport

/-- Benchmark-transport-side theorem-strength reimport reversibility object. -/
def benchmarkTransportReimportReversibilityTheorem :
    ReimportReversibilityTheorem benchmarkTransportLCELInstance :=
  reimportReversibilityTheorem_of_support
    benchmarkTransportReimportReversibilitySupport

/-- Native DP-side theorem-strength reimport reversibility object. -/
def dpEmitterReimportReversibilityTheorem :
    ReimportReversibilityTheorem dpEmitterLCELInstance :=
  reimportReversibilityTheorem_of_support
    dpEmitterReimportReversibilitySupport

/-! ## Theorem-strength boundary factorization object -/

/-- Theorem-strength boundary-factorization object for the operational-inexpressibility manuscript Proposition 5.9.

Packages the reimport-side theorem (visible via the reversible projection)
and the license-side theorem (sensitive to the irreversible quotient)
together with the two coherence equalities that tie the obstruction,
reflection, and reimport layers into a single boundary-sensitive
factorization, plus the boundary-realization witness. -/
structure BoundaryFactorizationTheorem (L : FormalLCELInstance) : Type where
  /-- Reimport-side theorem-strength object (visible via reversible
  projection). -/
  visible : ReimportReversibilityTheorem L
  /-- License-side theorem-strength object (sensitive to irreversible
  quotient). -/
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

/-- Downgrade to the abstract `ProjectionFactorizationWitness` used in the
existing LCEL substrate machinery. -/
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

/-- Extraction of a theorem-strength boundary-factorization object from the
proof-carrying support record. -/
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

/-- Gödel-side theorem-strength boundary factorization object. -/
def godel1931BoundaryFactorizationTheorem :
    BoundaryFactorizationTheorem godel1931LCELInstance :=
  boundaryFactorizationTheorem_of_support
    godel1931BoundaryFactorizationSupport

/-- Benchmark-transport-side theorem-strength boundary factorization object. -/
def benchmarkTransportBoundaryFactorizationTheorem :
    BoundaryFactorizationTheorem benchmarkTransportLCELInstance :=
  boundaryFactorizationTheorem_of_support
    benchmarkTransportBoundaryFactorizationSupport

/-- Native DP-side theorem-strength boundary factorization object. -/
def dpEmitterBoundaryFactorizationTheorem :
    BoundaryFactorizationTheorem dpEmitterLCELInstance :=
  boundaryFactorizationTheorem_of_support
    dpEmitterBoundaryFactorizationSupport

end OperatorKO7.LCELSubstrateMathematics
