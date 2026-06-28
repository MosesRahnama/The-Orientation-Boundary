import OperatorKO7.Meta.ClassicalAscentProfile
import OperatorKO7.Meta.LCELTypedSigmaGamma
import OperatorKO7.Meta.ProjectionAsConservativeExtension
import OperatorKO7.Meta.StructuralIdentityComparison

/-!
# LCEL Schema

Layer-Crossing-Under-External-License schema as a single Lean carrier.

This file realizes the operational-inexpressibility manuscript's Definition 5.7 (`def:lcel-schema`) as a
packaged six-slot structure at the Lean level. It is intentionally a
**definition-and-packaging** layer: it does not rescue the paper's broader
blanket mechanization claim for the LCEL block. The substrate propositions
(`prop:lcel-reversibility`, `prop:lcel-boundary-factorization`) and the
schema-level structural-identity theorem (`thm:lcel-structural-identity`)
are developed in the companion files
`OperatorKO7/Meta/LCELReversibility.lean` and
`OperatorKO7/Meta/LCELStructuralIdentity.lean`.

The paper's six LCEL clauses are:

1. base system `T`,
2. boundary `Π ⊆ Ω_T`,
3. external license `Σ`,
4. licensed extension `T⁺ = T + Σ`,
5. reimport class `Γ' ⊆ Γ_n`,
6. annotation functor `Imp : Der(T⁺) → Annot(T)`.

The four structural clauses of Definition 5.7 are:

- internal non-derivability of boundary,
- license coverage of boundary,
- reimport conservativity,
- annotation respects projection.

The light profile `LCELSlotProfile` carries propositional readings of the
six clauses. `FormalLCELInstance` carries a typed version compatible with
the existing `FormalExternalClassicalComparisonObject`, adjoining the two
slots (explicit license `Σ`, explicit reimport class `Γ'`) that the
comparison object folds into `strongerFramework` and `reimport`.

Adapters from the Gödel-side and benchmark-side comparison objects are
supplied, witnessing the two instantiations named in the operational-inexpressibility manuscript's
`thm:structural-identity` proof.
-/

namespace OperatorKO7.LCELSchema

open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.LCELTypedSigmaGamma
open OperatorKO7.ProjectionAsConservativeExtension
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema
open OperatorKO7.StructuralIdentityComparison

/-! ## Light propositional profile -/

/-- the operational-inexpressibility manuscript Definition 5.7 read as a six-clause propositional profile. -/
structure LCELSlotProfile where
  hasBaseSystem : Prop
  hasBoundary : Prop
  hasExternalLicense : Prop
  hasLicensedExtension : Prop
  hasReimportClass : Prop
  hasAnnotationFunctor : Prop

/-- the operational-inexpressibility manuscript's LCEL realization: all six clauses hold. -/
def RealizesLCELSchema (P : LCELSlotProfile) : Prop :=
  P.hasBaseSystem
    ∧ P.hasBoundary
    ∧ P.hasExternalLicense
    ∧ P.hasLicensedExtension
    ∧ P.hasReimportClass
    ∧ P.hasAnnotationFunctor

/-- Named LCEL clause, used by the structural-identity quasi-functor. -/
inductive LCELClause
  | baseSystem
  | boundary
  | externalLicense
  | licensedExtension
  | reimportClass
  | annotationFunctor
  deriving DecidableEq, Repr

/-- Stagewise view of an `LCELSlotProfile`. -/
def ClauseHolds (P : LCELSlotProfile) : LCELClause → Prop
  | .baseSystem => P.hasBaseSystem
  | .boundary => P.hasBoundary
  | .externalLicense => P.hasExternalLicense
  | .licensedExtension => P.hasLicensedExtension
  | .reimportClass => P.hasReimportClass
  | .annotationFunctor => P.hasAnnotationFunctor

/-- Six-clause parallelism between two LCEL slot profiles. -/
def StagewiseLCELEquivalent (P Q : LCELSlotProfile) : Prop :=
  ∀ c, ClauseHolds P c ↔ ClauseHolds Q c

theorem StagewiseLCELEquivalent.symm
    {P Q : LCELSlotProfile}
    (h : StagewiseLCELEquivalent P Q) :
    StagewiseLCELEquivalent Q P := by
  intro c
  exact (h c).symm

theorem StagewiseLCELEquivalent.trans
    {P Q R : LCELSlotProfile}
    (hPQ : StagewiseLCELEquivalent P Q)
    (hQR : StagewiseLCELEquivalent Q R) :
    StagewiseLCELEquivalent P R := by
  intro c
  exact (hPQ c).trans (hQR c)

@[simp] theorem realizesLCEL_iff_stagewise (P : LCELSlotProfile) :
    RealizesLCELSchema P
      ↔ (ClauseHolds P .baseSystem
          ∧ ClauseHolds P .boundary
          ∧ ClauseHolds P .externalLicense
          ∧ ClauseHolds P .licensedExtension
          ∧ ClauseHolds P .reimportClass
          ∧ ClauseHolds P .annotationFunctor) := by
  constructor
  · intro h
    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · intro h
    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Stagewise parallelism preserves realization. -/
theorem StagewiseLCELEquivalent.preserves_realization
    {P Q : LCELSlotProfile}
    (h : StagewiseLCELEquivalent P Q)
    (hP : RealizesLCELSchema P) :
    RealizesLCELSchema Q := by
  rcases hP with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h .baseSystem).1 h1
  · exact (h .boundary).1 h2
  · exact (h .externalLicense).1 h3
  · exact (h .licensedExtension).1 h4
  · exact (h .reimportClass).1 h5
  · exact (h .annotationFunctor).1 h6

/-! ## Richer typed LCEL boundary and annotation objects -/

/-- Typed boundary object for the operational-inexpressibility manuscript's LCEL boundary slot `Π`.

This records a witness family into the base-theory sentence space together with
the two semantic side conditions that the paper treats as load-bearing:
internal non-derivability and truth in the reference model. -/
structure LCELBoundaryObject (B : FormalBaseTheorySemantics) where
  BoundaryWitness : Type
  boundarySentence : BoundaryWitness → B.Sentence
  designated : BoundaryWitness
  designated_not_provable : ¬ B.proves (boundarySentence designated)
  designated_true : B.trueInReferenceModel (boundarySentence designated)

namespace LCELBoundaryObject

/-- Propositional realization of a typed boundary object. -/
def realized {B : FormalBaseTheorySemantics} (Pi : LCELBoundaryObject B) : Prop :=
  ∃ w, ¬ B.proves (Pi.boundarySentence w)
    ∧ B.trueInReferenceModel (Pi.boundarySentence w)

/-- The designated boundary witness realizes the boundary slot. -/
theorem designated_realizes {B : FormalBaseTheorySemantics}
    (Pi : LCELBoundaryObject B) :
    Pi.realized := by
  exact ⟨Pi.designated, Pi.designated_not_provable, Pi.designated_true⟩

end LCELBoundaryObject

/-- Typed annotation functor for the operational-inexpressibility manuscript's LCEL slot
`Imp : Der(T⁺) → Annot(T)`.

This remains artifact-facing: it records a typed annotation carrier, a decoder
back into the sentence space, and theorem-backed laws showing that the
designated derivation yields a certified annotation whose decoded sentence is
true in the reference model. -/
structure LCELAnnotationFunctor
    (B : FormalBaseTheorySemantics) (R : FormalReimportSemantics B) where
  Annotation : Type
  annotate : R.Admission → Annotation
  decode : Annotation → B.Sentence
  witness_decodes_to_imported :
    decode (annotate R.witness) = R.importedSentence
  witness_certifies_decoded :
    R.certifies R.witness (decode (annotate R.witness))
  witness_decoded_true :
    B.trueInReferenceModel (decode (annotate R.witness))

namespace LCELAnnotationFunctor

/-- Propositional realization of a typed annotation functor. -/
def realized
    {B : FormalBaseTheorySemantics} {R : FormalReimportSemantics B}
    (Imp : LCELAnnotationFunctor B R) : Prop :=
  ∃ a, R.certifies a (Imp.decode (Imp.annotate a))
    ∧ B.trueInReferenceModel (Imp.decode (Imp.annotate a))

/-- The designated derivation witness realizes the annotation slot. -/
theorem witness_realizes
    {B : FormalBaseTheorySemantics} {R : FormalReimportSemantics B}
    (Imp : LCELAnnotationFunctor B R) :
    Imp.realized := by
  exact ⟨R.witness, Imp.witness_certifies_decoded, Imp.witness_decoded_true⟩

end LCELAnnotationFunctor

/-! ## Typed LCEL instance -/

/-- Typed LCEL instance.

This bundles an existing `FormalExternalClassicalComparisonObject`
with richer typed LCEL boundary/annotation objects and with the two extra
slot fields that the operational-inexpressibility manuscript Definition 5.7 treats separately: an explicit
external-license object `Σ` and an explicit reimport-class object `Γ'`.

The structure does not fake proofs of the substrate propositions; it
supplies the data the paper's LCEL definition names while retaining the
older proposition-level witness surface for compatibility with the current
LCEL theorem stack. The reversibility asymmetry and boundary factorization are derived in
`LCELReversibility.lean` conditional on additional witnesses that the
paper glosses as standard facts. -/
structure FormalLCELInstance where
  /-- Underlying four-slot comparison object from
  `ClassicalAscentProfile`. Wraps base theory, obstruction, stronger
  framework, and reimport. -/
  comparison : FormalExternalClassicalComparisonObject
  /-- Rich typed boundary object for the LCEL boundary slot `Π`. -/
  boundaryObject : LCELBoundaryObject comparison.baseTheoryContent
  /-- Explicit link from the richer boundary object back to the comparison
  profile's self-obstruction clause. -/
  boundaryMatchesProfile :
    boundaryObject.realized ↔ comparison.profile.shape.hasSelfObstruction
  /-- Rich typed external-license object for the LCEL slot `Σ`. -/
  externalLicenseObject :
    LCELExternalLicenseObject
      comparison.baseTheoryContent
      comparison.reflectionContent
  /-- Compatibility-facing proposition-level external-license slot retained
  for the existing theorem surface. -/
  externalLicenseWitness : Prop
  externalLicenseHolds : externalLicenseWitness
  /-- Explicit link from the typed `Σ` object back to the retained
  proposition-level witness slot. -/
  externalLicenseMatchesWitness :
    externalLicenseObject.realized ↔ externalLicenseWitness
  /-- Rich typed reimport-class object for the LCEL slot `Γ'`. -/
  reimportClassObject :
    LCELReimportClassObject
      comparison.baseTheoryContent
      comparison.reimportContent
  /-- Compatibility-facing proposition-level reimport-class slot retained
  for the existing theorem surface. -/
  reimportClassWitness : Prop
  reimportClassHolds : reimportClassWitness
  /-- Explicit link from the typed `Γ'` object back to the retained
  proposition-level witness slot. -/
  reimportClassMatchesWitness :
    reimportClassObject.realized ↔ reimportClassWitness
  /-- Rich typed annotation functor for the LCEL slot
  `Imp : Der(T⁺) → Annot(T)`. -/
  annotationFunctor :
    LCELAnnotationFunctor comparison.baseTheoryContent comparison.reimportContent
  /-- Explicit link from the richer annotation functor back to the comparison
  profile's licensed-reimport clause. -/
  annotationMatchesProfile :
    annotationFunctor.realized ↔ comparison.profile.shape.licensedReimport

namespace FormalLCELInstance

/-- The propositional slot profile extracted from a typed instance. -/
def toSlotProfile (L : FormalLCELInstance) : LCELSlotProfile where
  hasBaseSystem := L.comparison.baseSemantics.hasBaseSystem
  hasBoundary := L.boundaryObject.realized
  hasExternalLicense := L.externalLicenseWitness
  hasLicensedExtension := L.comparison.frameworkSemantics.frameworkAvailable
  hasReimportClass := L.reimportClassWitness
  hasAnnotationFunctor := L.annotationFunctor.realized

/-- The typed `Σ` object realizes its retained proposition-level slot. -/
theorem externalLicenseObject_realized (L : FormalLCELInstance) :
    L.externalLicenseObject.realized :=
  (L.externalLicenseMatchesWitness).2 L.externalLicenseHolds

/-- The typed `Γ'` object realizes its retained proposition-level slot. -/
theorem reimportClassObject_realized (L : FormalLCELInstance) :
    L.reimportClassObject.realized :=
  (L.reimportClassMatchesWitness).2 L.reimportClassHolds

/-- A typed LCEL instance realizes the schema when the underlying
comparison object realizes the six-step shape and both extra slots are
inhabited. -/
theorem realizesLCELSchema (L : FormalLCELInstance)
    (hBase : L.comparison.baseSemantics.hasBaseSystem)
    (hFramework : L.comparison.frameworkSemantics.frameworkAvailable) :
    RealizesLCELSchema L.toSlotProfile := by
  refine ⟨hBase, ?_, L.externalLicenseHolds, hFramework,
    L.reimportClassHolds, ?_⟩
  · exact L.boundaryObject.designated_realizes
  · exact L.annotationFunctor.witness_realizes

/-- Direct realization using the comparison object's `supported` theorem.

`FormalExternalClassicalComparisonObject.supported` provides a
three-clause conjunction: the profile realizes the six-step shape, the
family is reflection, and the shape is stagewise-equivalent to the
DP-side profile. Together with `profileShape`, the six-step witness
transports to the four semantic slot-witnesses. -/
theorem realizesLCELSchema_of_supported (L : FormalLCELInstance)
    (hSupp : RealizesSixStepShape L.comparison.profile.shape
      ∧ L.comparison.profile.family = AscentFamily.reflection
      ∧ StagewiseEquivalent L.comparison.profile.shape
          dpAsClassicalAscentProfile.shape) :
    RealizesLCELSchema L.toSlotProfile := by
  rcases hSupp with ⟨hShape, _hFamily, _hStage⟩
  rcases hShape with ⟨hBase, _hSelfObs, _hBlocked, hFramework, _hResolved,
    _hLicensed⟩
  -- Transport from the profile shape to the semantic base/framework slots via
  -- `profileShape`, which records the shape as the six-tuple of slot-witness
  -- predicates.
  have hBase' : L.comparison.baseSemantics.hasBaseSystem := by
    have hEq : L.comparison.profile.shape.hasBaseSystem
        = L.comparison.baseSemantics.hasBaseSystem := by
      rw [L.comparison.profileShape]
    exact hEq ▸ hBase
  have hFramework' : L.comparison.frameworkSemantics.frameworkAvailable := by
    have hEq : L.comparison.profile.shape.hasStrongerFramework
        = L.comparison.frameworkSemantics.frameworkAvailable := by
      rw [L.comparison.profileShape]
    exact hEq ▸ hFramework
  exact L.realizesLCELSchema hBase' hFramework'

end FormalLCELInstance

/-! ## Canonical instances -/

/-- Rich Gödel-side boundary object for the LCEL boundary slot. -/
def godel1931LCELBoundaryObject :
    LCELBoundaryObject godel1931FormalExternalClassicalComparisonObject.baseTheoryContent where
  BoundaryWitness :=
    godel1931FormalExternalClassicalComparisonObject.obstructionContent.Witness
  boundarySentence :=
    godel1931FormalExternalClassicalComparisonObject.obstructionContent.blockedBy
  designated := godel1931FormalExternalClassicalComparisonObject.obstructionContent.witness
  designated_not_provable := by
    simpa using
      godel1931FormalExternalClassicalComparisonObject.obstructionContent.blocked_not_provable
  designated_true := by
    simpa using
      godel1931FormalExternalClassicalComparisonObject.obstructionContent.blocked_true

/-- Rich Gödel-side annotation functor for the LCEL annotation slot. -/
def godel1931LCELAnnotationFunctor :
    LCELAnnotationFunctor
      godel1931FormalExternalClassicalComparisonObject.baseTheoryContent
      godel1931FormalExternalClassicalComparisonObject.reimportContent where
  Annotation := godel1931FormalExternalClassicalComparisonObject.baseTheoryContent.Sentence
  annotate := fun _ =>
    godel1931FormalExternalClassicalComparisonObject.reimportContent.importedSentence
  decode := id
  witness_decodes_to_imported := rfl
  witness_certifies_decoded := by
    simpa using
      godel1931FormalExternalClassicalComparisonObject.reimportContent.witness_certifies_imported
  witness_decoded_true := by
    simpa using
      godel1931FormalExternalClassicalComparisonObject.reimportContent.imported_true

/-- Rich Gödel-side typed external-license object for the LCEL slot `Σ`. -/
def godel1931LCELExternalLicenseObject :
    LCELExternalLicenseObject
      godel1931FormalExternalClassicalComparisonObject.baseTheoryContent
      godel1931FormalExternalClassicalComparisonObject.reflectionContent :=
  defaultExternalLicenseObject godel1931FormalExternalClassicalComparisonObject

/-- Rich Gödel-side typed reimport-class object for the LCEL slot `Γ'`. -/
def godel1931LCELReimportClassObject :
    LCELReimportClassObject
      godel1931FormalExternalClassicalComparisonObject.baseTheoryContent
      godel1931FormalExternalClassicalComparisonObject.reimportContent :=
  defaultReimportClassObject godel1931FormalExternalClassicalComparisonObject

/-- Rich benchmark-side boundary object for the LCEL boundary slot. -/
def benchmarkTransportLCELBoundaryObject :
    LCELBoundaryObject benchmarkTransportFormalExternalClassicalComparisonObject.baseTheoryContent where
  BoundaryWitness :=
    benchmarkTransportFormalExternalClassicalComparisonObject.obstructionContent.Witness
  boundarySentence :=
    benchmarkTransportFormalExternalClassicalComparisonObject.obstructionContent.blockedBy
  designated :=
    benchmarkTransportFormalExternalClassicalComparisonObject.obstructionContent.witness
  designated_not_provable := by
    simpa using
      benchmarkTransportFormalExternalClassicalComparisonObject.obstructionContent.blocked_not_provable
  designated_true := by
    simpa using
      benchmarkTransportFormalExternalClassicalComparisonObject.obstructionContent.blocked_true

/-- Rich benchmark-side annotation functor for the LCEL annotation slot.
After the reimport-content admission-carrier upgrade, the admission
space and the annotation space both coincide with the typed sentence
space, so `annotate` is the identity on sentences rather than a
constant landing on the designated imported sentence. -/
def benchmarkTransportLCELAnnotationFunctor :
    LCELAnnotationFunctor
      benchmarkTransportFormalExternalClassicalComparisonObject.baseTheoryContent
      benchmarkTransportFormalExternalClassicalComparisonObject.reimportContent where
  Annotation :=
    benchmarkTransportFormalExternalClassicalComparisonObject.baseTheoryContent.Sentence
  annotate := id
  decode := id
  witness_decodes_to_imported := rfl
  witness_certifies_decoded := rfl
  witness_decoded_true := by
    simpa using
      benchmarkTransportFormalExternalClassicalComparisonObject.reimportContent.imported_true

/-- Rich benchmark-side typed external-license object for the LCEL slot `Σ`.
-/
def benchmarkTransportLCELExternalLicenseObject :
    LCELExternalLicenseObject
      benchmarkTransportFormalExternalClassicalComparisonObject.baseTheoryContent
      benchmarkTransportFormalExternalClassicalComparisonObject.reflectionContent :=
  defaultExternalLicenseObject benchmarkTransportFormalExternalClassicalComparisonObject

/-- Rich benchmark-side typed reimport-class object for the LCEL slot `Γ'`. -/
def benchmarkTransportLCELReimportClassObject :
    LCELReimportClassObject
      benchmarkTransportFormalExternalClassicalComparisonObject.baseTheoryContent
      benchmarkTransportFormalExternalClassicalComparisonObject.reimportContent :=
  defaultReimportClassObject benchmarkTransportFormalExternalClassicalComparisonObject

/-- Gödel-side canonical LCEL instance. Wraps
`godel1931FormalExternalClassicalComparisonObject` with the two extra
slots. The explicit `Σ` / `Γ'` carriers are now present as typed semantic
objects, while the older proposition-level witness fields are retained as
compatibility projections. -/
def godel1931LCELInstance : FormalLCELInstance where
  comparison := godel1931FormalExternalClassicalComparisonObject
  boundaryObject := godel1931LCELBoundaryObject
  boundaryMatchesProfile := by
    constructor
    · intro _
      have hObs :
          godel1931FormalExternalClassicalComparisonObject.obstructionSemantics.hasSelfObstruction := by
        exact
          godel1931FormalExternalClassicalComparisonObject.obstructionSemantics.realizesSelfObstruction
      have hEq :
          godel1931FormalExternalClassicalComparisonObject.profile.shape.hasSelfObstruction =
            godel1931FormalExternalClassicalComparisonObject.obstructionSemantics.hasSelfObstruction := by
        rw [godel1931FormalExternalClassicalComparisonObject.profileShape]
      exact hEq.symm ▸ hObs
    · intro _
      exact godel1931LCELBoundaryObject.designated_realizes
  externalLicenseObject := godel1931LCELExternalLicenseObject
  externalLicenseWitness :=
    godel1931FormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
  externalLicenseHolds := by
    rcases godel1931FormalExternalClassicalComparison_semanticSupported with
      ⟨_, _, _, hReflect, _, _, _⟩
    exact hReflect
  externalLicenseMatchesWitness := by
    simpa [godel1931LCELExternalLicenseObject] using
      defaultExternalLicenseObject_realized_iff_hasReflectionOperator
        godel1931FormalExternalClassicalComparisonObject
  reimportClassObject := godel1931LCELReimportClassObject
  reimportClassWitness :=
    godel1931FormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport
  reimportClassHolds := by
    rcases godel1931FormalExternalClassicalComparison_semanticSupported with
      ⟨_, _, _, _, _, _, hReimport⟩
    exact hReimport
  reimportClassMatchesWitness := by
    simpa [godel1931LCELReimportClassObject] using
      defaultReimportClassObject_realized_iff_hasSemanticReimport
        godel1931FormalExternalClassicalComparisonObject
  annotationFunctor := godel1931LCELAnnotationFunctor
  annotationMatchesProfile := by
    constructor
    · intro _
      have hAnn :
          godel1931FormalExternalClassicalComparisonObject.reimportSemantics.licensedReimport := by
        exact
          godel1931FormalExternalClassicalComparisonObject.reimportSemantics.realizesLicensedReimport
      have hEq :
          godel1931FormalExternalClassicalComparisonObject.profile.shape.licensedReimport =
            godel1931FormalExternalClassicalComparisonObject.reimportSemantics.licensedReimport := by
        rw [godel1931FormalExternalClassicalComparisonObject.profileShape]
      exact hEq.symm ▸ hAnn
    · intro _
      exact godel1931LCELAnnotationFunctor.witness_realizes

/-- Benchmark / DP-side canonical LCEL instance. Wraps the benchmark
transport comparison object with the two extra slots. The explicit
`Σ` / `Γ'` carriers are now present as typed semantic objects, while the
older proposition-level witness fields are retained as compatibility
projections. -/
def benchmarkTransportLCELInstance : FormalLCELInstance where
  comparison := benchmarkTransportFormalExternalClassicalComparisonObject
  boundaryObject := benchmarkTransportLCELBoundaryObject
  boundaryMatchesProfile := by
    constructor
    · intro _
      have hObs :
          benchmarkTransportFormalExternalClassicalComparisonObject.obstructionSemantics.hasSelfObstruction := by
        exact
          benchmarkTransportFormalExternalClassicalComparisonObject.obstructionSemantics.realizesSelfObstruction
      have hEq :
          benchmarkTransportFormalExternalClassicalComparisonObject.profile.shape.hasSelfObstruction =
            benchmarkTransportFormalExternalClassicalComparisonObject.obstructionSemantics.hasSelfObstruction := by
        rw [benchmarkTransportFormalExternalClassicalComparisonObject.profileShape]
      exact hEq.symm ▸ hObs
    · intro _
      exact benchmarkTransportLCELBoundaryObject.designated_realizes
  externalLicenseObject := benchmarkTransportLCELExternalLicenseObject
  externalLicenseWitness :=
    benchmarkTransportFormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
  externalLicenseHolds := by
    rcases benchmarkTransportFormalExternalClassicalComparison_semanticSupported with
      ⟨_, _, _, hReflect, _, _, _⟩
    exact hReflect
  externalLicenseMatchesWitness := by
    simpa [benchmarkTransportLCELExternalLicenseObject] using
      defaultExternalLicenseObject_realized_iff_hasReflectionOperator
        benchmarkTransportFormalExternalClassicalComparisonObject
  reimportClassObject := benchmarkTransportLCELReimportClassObject
  reimportClassWitness :=
    benchmarkTransportFormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport
  reimportClassHolds := by
    rcases benchmarkTransportFormalExternalClassicalComparison_semanticSupported with
      ⟨_, _, _, _, _, _, hReimport⟩
    exact hReimport
  reimportClassMatchesWitness := by
    simpa [benchmarkTransportLCELReimportClassObject] using
      defaultReimportClassObject_realized_iff_hasSemanticReimport
        benchmarkTransportFormalExternalClassicalComparisonObject
  annotationFunctor := benchmarkTransportLCELAnnotationFunctor
  annotationMatchesProfile := by
    constructor
    · intro _
      have hAnn :
          benchmarkTransportFormalExternalClassicalComparisonObject.reimportSemantics.licensedReimport := by
        exact
          benchmarkTransportFormalExternalClassicalComparisonObject.reimportSemantics.realizesLicensedReimport
      have hEq :
          benchmarkTransportFormalExternalClassicalComparisonObject.profile.shape.licensedReimport =
            benchmarkTransportFormalExternalClassicalComparisonObject.reimportSemantics.licensedReimport := by
        rw [benchmarkTransportFormalExternalClassicalComparisonObject.profileShape]
      exact hEq.symm ▸ hAnn
    · intro _
      exact benchmarkTransportLCELAnnotationFunctor.witness_realizes

/-- The Gödel-side LCEL instance realizes the operational-inexpressibility manuscript's LCEL schema. -/
theorem godel1931LCELInstance_realizesSchema :
    RealizesLCELSchema godel1931LCELInstance.toSlotProfile := by
  exact
    godel1931LCELInstance.realizesLCELSchema_of_supported
      godel1931FormalExternalClassicalComparison_supported

/-- The benchmark-side LCEL instance realizes the operational-inexpressibility manuscript's LCEL schema. -/
theorem benchmarkTransportLCELInstance_realizesSchema :
    RealizesLCELSchema benchmarkTransportLCELInstance.toSlotProfile := by
  exact
    benchmarkTransportLCELInstance.realizesLCELSchema_of_supported
      benchmarkTransportFormalExternalClassicalComparison_supported

/-- Both canonical LCEL instances realize the schema. -/
theorem canonical_lcel_instances_realize_schema :
    RealizesLCELSchema godel1931LCELInstance.toSlotProfile
      ∧ RealizesLCELSchema benchmarkTransportLCELInstance.toSlotProfile :=
  ⟨godel1931LCELInstance_realizesSchema,
    benchmarkTransportLCELInstance_realizesSchema⟩

end OperatorKO7.LCELSchema
