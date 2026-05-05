import OperatorKO7.Meta.ClassicalAscentProfile

/-!
# Typed LCEL `Σ` / `Γ'` Carriers

Generic typed carriers for the operational-inexpressibility manuscript's two explicit LCEL slots beyond the boundary
object `Π` and annotation functor `Imp`:

- the external-license slot `Σ`, and
- the reimport-class slot `Γ'`.

The comparison object already contains enough semantic structure to expose both
slots as genuine typed objects. This file factors out the reusable carrier
shapes and their compatibility theorems with the older proposition-level
readings used elsewhere in the LCEL stack.
-/

namespace OperatorKO7.LCELTypedSigmaGamma

open OperatorKO7.ClassicalAscentProfile

/-- Typed external-license object for the operational-inexpressibility manuscript's explicit LCEL slot `Σ`.

The designated witness carries not only a stronger-framework witness extending
base, but also the blocked sentence that it reflects, together with the theorem-
backed non-provability / truth / licensed-admission data attached to that
sentence. -/
structure LCELExternalLicenseObject
    (B : FormalBaseTheorySemantics) (R : FormalReflectionOperatorSemantics B) where
  LicenseWitness : Type
  framework : LicenseWitness → R.Framework
  licensedSentence : LicenseWitness → B.Sentence
  designated : LicenseWitness
  designated_sentence_eq_blocked :
    licensedSentence designated = R.blockedSentence
  designated_extendsBase : R.extendsBase (framework designated)
  designated_reflects :
    R.reflects (framework designated) (licensedSentence designated)
  designated_not_provable :
    ¬ B.proves (licensedSentence designated)
  designated_true :
    B.trueInReferenceModel (licensedSentence designated)
  designated_licensedAdmission :
    R.licensedAdmission (licensedSentence designated)

namespace LCELExternalLicenseObject

/-- Propositional realization of a typed external-license object.

This preserves the older proposition-level reading of `Σ`: some external
framework witness extends the base theory. The richer sentence-level semantic
content remains available at the designated witness. -/
def realized
    {B : FormalBaseTheorySemantics} {R : FormalReflectionOperatorSemantics B}
    (Sigma : LCELExternalLicenseObject B R) : Prop :=
  ∃ w, R.extendsBase (Sigma.framework w)

/-- The designated witness realizes the proposition-level external-license slot.
-/
theorem designated_realizes
    {B : FormalBaseTheorySemantics} {R : FormalReflectionOperatorSemantics B}
    (Sigma : LCELExternalLicenseObject B R) :
    Sigma.realized :=
  ⟨Sigma.designated, Sigma.designated_extendsBase⟩

end LCELExternalLicenseObject

/-- Typed reimport-class object for the operational-inexpressibility manuscript's explicit LCEL slot `Γ'`.

The designated witness packages a typed admission witness together with the
sentence it certifies and the theorem-backed truth of that sentence in the base
reference model. -/
structure LCELReimportClassObject
    (B : FormalBaseTheorySemantics) (R : FormalReimportSemantics B) where
  ReimportWitness : Type
  admission : ReimportWitness → R.Admission
  importedSentence : ReimportWitness → B.Sentence
  designated : ReimportWitness
  designated_sentence_eq_imported :
    importedSentence designated = R.importedSentence
  designated_certifies :
    R.certifies (admission designated) (importedSentence designated)
  designated_true :
    B.trueInReferenceModel (importedSentence designated)

namespace LCELReimportClassObject

/-- Propositional realization of a typed reimport-class object.

This preserves the older proposition-level reading of `Γ'`: some typed
admission witness certifies a sentence that is true in the reference model. -/
def realized
    {B : FormalBaseTheorySemantics} {R : FormalReimportSemantics B}
    (Gamma : LCELReimportClassObject B R) : Prop :=
  ∃ w,
    R.certifies (Gamma.admission w) (Gamma.importedSentence w)
      ∧ B.trueInReferenceModel (Gamma.importedSentence w)

/-- The designated witness realizes the proposition-level reimport-class slot.
-/
theorem designated_realizes
    {B : FormalBaseTheorySemantics} {R : FormalReimportSemantics B}
    (Gamma : LCELReimportClassObject B R) :
    Gamma.realized :=
  ⟨Gamma.designated, Gamma.designated_certifies, Gamma.designated_true⟩

end LCELReimportClassObject

/-- Default typed external-license object induced by any formal external
classical comparison object.

The witness carrier is the comparison object's typed framework space itself, and
its designated witness is the comparison object's designated stronger
framework. The sentence tracked by the object is the comparison object's blocked
sentence. -/
def defaultExternalLicenseObject
    (E : FormalExternalClassicalComparisonObject) :
    LCELExternalLicenseObject E.baseTheoryContent E.reflectionContent where
  LicenseWitness := E.reflectionContent.Framework
  framework := id
  licensedSentence := fun _ => E.reflectionContent.blockedSentence
  designated := E.reflectionContent.strongerFramework
  designated_sentence_eq_blocked := rfl
  designated_extendsBase := E.reflectionContent.stronger_extendsBase
  designated_reflects := by
    simpa using E.reflectionContent.stronger_reflects_blocked
  designated_not_provable := by
    simpa using E.reflectionContent.blocked_not_provable
  designated_true := by
    simpa using E.reflectionContent.blocked_true
  designated_licensedAdmission := by
    simpa using E.reflectionContent.blocked_licensedAdmission

/-- The default typed external-license object is propositionally equivalent to
`hasReflectionOperator` on the underlying reflection semantics. -/
theorem defaultExternalLicenseObject_realized_iff_hasReflectionOperator
    (E : FormalExternalClassicalComparisonObject) :
    (defaultExternalLicenseObject E).realized
      ↔ E.reflectionContent.hasReflectionOperator := by
  constructor
  · intro h
    rcases h with ⟨w, hw⟩
    exact ⟨w, hw⟩
  · intro h
    rcases h with ⟨w, hw⟩
    exact ⟨w, hw⟩

/-- Default typed reimport-class object induced by any formal external classical
comparison object.

The witness carrier is the full typed pair `(admission, sentence)`, so its
realization proposition is definitionally aligned with the older existential
`hasSemanticReimport` reading. The designated witness is the comparison
object's own designated imported sentence pair. -/
def defaultReimportClassObject
    (E : FormalExternalClassicalComparisonObject) :
    LCELReimportClassObject E.baseTheoryContent E.reimportContent where
  ReimportWitness := E.reimportContent.Admission × E.baseTheoryContent.Sentence
  admission := Prod.fst
  importedSentence := Prod.snd
  designated := ⟨E.reimportContent.witness, E.reimportContent.importedSentence⟩
  designated_sentence_eq_imported := rfl
  designated_certifies := by
    simpa using E.reimportContent.witness_certifies_imported
  designated_true := by
    simpa using E.reimportContent.imported_true

/-- The default typed reimport-class object is propositionally equivalent to
`hasSemanticReimport` on the underlying reimport semantics. -/
theorem defaultReimportClassObject_realized_iff_hasSemanticReimport
    (E : FormalExternalClassicalComparisonObject) :
    (defaultReimportClassObject E).realized
      ↔ E.reimportContent.hasSemanticReimport := by
  constructor
  · intro h
    rcases h with ⟨⟨a, s⟩, hCert, hTrue⟩
    exact ⟨a, s, hCert, hTrue⟩
  · intro h
    rcases h with ⟨a, s, hCert, hTrue⟩
    exact ⟨⟨a, s⟩, hCert, hTrue⟩

end OperatorKO7.LCELTypedSigmaGamma
