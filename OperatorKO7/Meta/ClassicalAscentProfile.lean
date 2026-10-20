import OperatorKO7.Meta.ReflectionSchema

/-!
# Classical Ascent Profile

Structural comparison wrapper above `ReflectionSchema`.

The generic records below are interfaces whose propositions and witnesses are
supplied by an inhabitant. The Gödel-named instance at the end is a synthetic
finite model with stipulated predicates. Its proved content is stage-shape
compatibility with the DP profile. Formal PA syntax, arithmetization,
incompleteness, model-theoretic truth, and reflection principles require
separate structures and proofs.
-/

namespace OperatorKO7.ClassicalAscentProfile

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema

private theorem iff_of_true {P Q : Prop} (hP : P) (hQ : Q) : P ↔ Q := by
  constructor
  · intro _
    exact hQ
  · intro _
    exact hP

/-- Six-stage shape, family tag, and optional metadata. -/
structure AscentProfile where
  shape : SixStepStructuralProfile
  family : AscentFamily
  complexity? : Option FormulaClass := none
  targetTheory? : Option FormalTheory := none

/-- Ascent profile paired with six unconstrained presentation labels. -/
structure ConcreteComparisonProfile where
  profile : AscentProfile
  baseSystemLabel : String
  obstructionLabel : String
  blockedLabel : String
  strongerFrameworkLabel : String
  resolutionLabel : String
  licensedReimportLabel : String

/-- Base-system classification tag. -/
inductive HistoricalBaseKind
  | peanoArithmetic
  | benchmarkContractKO7
  deriving DecidableEq, Repr

/-- Obstruction classification tag. -/
inductive HistoricalObstructionKind
  | godelSentence
  | noDirectWholeWitness
  deriving DecidableEq, Repr

/-- Stronger-framework classification tag. -/
inductive HistoricalFrameworkKind
  | externalReflection
  | transformedCallTransport
  deriving DecidableEq, Repr

/-- Resolution classification tag. -/
inductive HistoricalResolutionKind
  | strongerTheoryTruth
  | transformedCallWitness
  deriving DecidableEq, Repr

/-- Reimport classification tag. -/
inductive HistoricalReimportKind
  | licensedTruthAdmission
  | contractLicensedWitness
  deriving DecidableEq, Repr

/-- Five classification tags stored independently of semantic coherence data. -/
structure HistoricalComparisonAnnotation where
  baseKind : HistoricalBaseKind
  obstructionKind : HistoricalObstructionKind
  frameworkKind : HistoricalFrameworkKind
  resolutionKind : HistoricalResolutionKind
  reimportKind : HistoricalReimportKind

/-- Label, optional register value, and a supplied base-system proposition. -/
structure HistoricalBaseTheoryProfile where
  label : String
  registerApprox? : Option FormalTheory := none
  hasBaseSystem : Prop

/-- Label with supplied self-obstruction and base-blocking propositions. -/
structure HistoricalObstructionWitness where
  label : String
  hasSelfObstruction : Prop
  blockedInBase : Prop

/-- Label with supplied framework-availability and resolution propositions. -/
structure HistoricalFrameworkOperator where
  label : String
  frameworkAvailable : Prop
  resolvesInFramework : Prop

/-- Label with a supplied licensed-reimport proposition. -/
structure HistoricalReimportMap where
  label : String
  licensedReimport : Prop

/-- Abstract sentence carrier and proof predicate with one supplied witness.
Deductive-calculus and soundness laws are additional interface requirements. -/
structure FormalHistoricalBaseTheory where
  label : String
  registerApprox? : Option FormalTheory := none
  Sentence : Type
  provesBaseSystem : Sentence → Prop
  witness : Sentence
  witness_provesBaseSystem : provesBaseSystem witness

/-- Abstract obstruction carrier with supplied predicates and one witness
satisfying both. -/
structure FormalHistoricalObstruction where
  label : String
  Witness : Type
  isSelfObstruction : Witness → Prop
  blocksBase : Witness → Prop
  witness : Witness
  witness_isSelfObstruction : isSelfObstruction witness
  witness_blocksBase : blocksBase witness

/-- Abstract framework carrier with one availability witness and one supplied
resolution witness. -/
structure FormalHistoricalFramework where
  label : String
  Framework : Type
  resolves : Framework → Prop
  availableWitness : Framework
  resolver : Framework
  resolver_resolves : resolves resolver

/-- Abstract admission carrier with one supplied certification witness. -/
structure FormalHistoricalReimport where
  label : String
  Admission : Type
  certified : Admission → Prop
  witness : Admission
  witness_certified : certified witness

/-- Abstract sentence carrier with arbitrary proof and truth predicates plus
one sentence satisfying the proof predicate. Model and proof-calculus laws are
left as additional data. -/
structure FormalBaseTheorySemantics where
  Sentence : Type
  proves : Sentence → Prop
  trueInReferenceModel : Sentence → Prop
  baseSentence : Sentence
  baseSentence_proves : proves baseSentence

/-- Abstract blocked-sentence interface. All proof, truth, extension,
reflection, and admission relations are supplied by the inhabitant; the
structure leaves metatheoretic soundness and conservativity as additional laws. -/
structure FormalReflectionOperatorSemantics
    (B : FormalBaseTheorySemantics) where
  Framework : Type
  extendsBase : Framework → Prop
  reflects : Framework → B.Sentence → Prop
  licensedAdmission : B.Sentence → Prop
  blockedSentence : B.Sentence
  blocked_not_provable : ¬ B.proves blockedSentence
  blocked_true : B.trueInReferenceModel blockedSentence
  strongerFramework : Framework
  stronger_extendsBase : extendsBase strongerFramework
  stronger_reflects_blocked : reflects strongerFramework blockedSentence
  blocked_licensedAdmission : licensedAdmission blockedSentence

/-- Abstract obstruction interface with a designated witness and sentence.
Its self-reference, obstruction, unprovability, and truth facts are fields. -/
structure FormalObstructionSemantics
    (B : FormalBaseTheorySemantics) where
  Witness : Type
  obstructs : Witness → B.Sentence → Prop
  selfReferential : Witness → Prop
  blockedBy : Witness → B.Sentence
  witness : Witness
  witness_selfReferential : selfReferential witness
  witness_obstructs_blocked : obstructs witness (blockedBy witness)
  blocked_not_provable : ¬ B.proves (blockedBy witness)
  blocked_true : B.trueInReferenceModel (blockedBy witness)

/-- Abstract reimport interface with one supplied certification and truth
witness. -/
structure FormalReimportSemantics
    (B : FormalBaseTheorySemantics) where
  Admission : Type
  certifies : Admission → B.Sentence → Prop
  importedSentence : B.Sentence
  witness : Admission
  witness_certifies_imported : certifies witness importedSentence
  imported_true : B.trueInReferenceModel importedSentence

/-- Existence of a sentence satisfying the supplied base-system predicate. -/
def FormalHistoricalBaseTheory.hasBaseSystem
    (B : FormalHistoricalBaseTheory) : Prop :=
  ∃ s, B.provesBaseSystem s

/-- Package the designated witness into the existential proposition. -/
theorem FormalHistoricalBaseTheory.realizesBaseSystem
    (B : FormalHistoricalBaseTheory) :
    B.hasBaseSystem := by
  exact ⟨B.witness, B.witness_provesBaseSystem⟩

/-- Existence of a witness satisfying the supplied self-obstruction predicate. -/
def FormalHistoricalObstruction.hasSelfObstruction
    (O : FormalHistoricalObstruction) : Prop :=
  ∃ w, O.isSelfObstruction w

/-- Existence of a witness satisfying the supplied base-blocking predicate. -/
def FormalHistoricalObstruction.blockedInBase
    (O : FormalHistoricalObstruction) : Prop :=
  ∃ w, O.blocksBase w

/-- Package the designated self-obstruction witness. -/
theorem FormalHistoricalObstruction.realizesSelfObstruction
    (O : FormalHistoricalObstruction) :
    O.hasSelfObstruction := by
  exact ⟨O.witness, O.witness_isSelfObstruction⟩

/-- Package the designated base-blocking witness. -/
theorem FormalHistoricalObstruction.realizesBlockedInBase
    (O : FormalHistoricalObstruction) :
    O.blockedInBase := by
  exact ⟨O.witness, O.witness_blocksBase⟩

/-- Nonemptiness of the supplied framework carrier. -/
def FormalHistoricalFramework.frameworkAvailable
    (F : FormalHistoricalFramework) : Prop :=
  Nonempty F.Framework

/-- Existence of an element satisfying the supplied resolution predicate. -/
def FormalHistoricalFramework.resolvesInFramework
    (F : FormalHistoricalFramework) : Prop :=
  ∃ x, F.resolves x

/-- Package the designated framework element as a nonemptiness witness. -/
theorem FormalHistoricalFramework.realizesAvailability
    (F : FormalHistoricalFramework) :
    F.frameworkAvailable := by
  exact ⟨F.availableWitness⟩

/-- Package the designated resolver into the existential proposition. -/
theorem FormalHistoricalFramework.realizesResolution
    (F : FormalHistoricalFramework) :
    F.resolvesInFramework := by
  exact ⟨F.resolver, F.resolver_resolves⟩

/-- Existence of an admission satisfying the supplied certification predicate. -/
def FormalHistoricalReimport.licensedReimport
    (R : FormalHistoricalReimport) : Prop :=
  ∃ a, R.certified a

/-- Package the designated certification witness. -/
theorem FormalHistoricalReimport.realizesLicensedReimport
    (R : FormalHistoricalReimport) :
    R.licensedReimport := by
  exact ⟨R.witness, R.witness_certified⟩

/-- Existence of a sentence satisfying the supplied proof predicate. -/
def FormalBaseTheorySemantics.hasInternalProofLayer
    (B : FormalBaseTheorySemantics) : Prop :=
  ∃ s, B.proves s

/-- Package the designated proved sentence. -/
theorem FormalBaseTheorySemantics.realizesInternalProofLayer
    (B : FormalBaseTheorySemantics) :
    B.hasInternalProofLayer := by
  exact ⟨B.baseSentence, B.baseSentence_proves⟩

/-- Existence of a sentence satisfying the supplied truth predicate together
with failure of the supplied proof predicate. -/
def FormalReflectionOperatorSemantics.hasBlockedSemanticSentence
    {B : FormalBaseTheorySemantics}
  (_R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ s, ¬ B.proves s ∧ B.trueInReferenceModel s

/-- Existence of a framework element satisfying the supplied extension
predicate. -/
def FormalReflectionOperatorSemantics.hasReflectionOperator
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ F, R.extendsBase F

/-- Existence of a framework element that reflects the designated blocked
sentence according to the supplied relation. -/
def FormalReflectionOperatorSemantics.resolvesBlockedSemantically
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ F, R.reflects F R.blockedSentence

/-- Existence of a sentence satisfying the supplied admission predicate. -/
def FormalReflectionOperatorSemantics.hasLicensedAdmission
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ s, R.licensedAdmission s

/-- Package the designated blocked sentence and its two supplied facts. -/
theorem FormalReflectionOperatorSemantics.realizesBlockedSemanticSentence
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.hasBlockedSemanticSentence := by
  exact ⟨R.blockedSentence, R.blocked_not_provable, R.blocked_true⟩

/-- Package the designated extending framework. -/
theorem FormalReflectionOperatorSemantics.realizesReflectionOperator
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.hasReflectionOperator := by
  exact ⟨R.strongerFramework, R.stronger_extendsBase⟩

/-- Package the supplied reflection fact for the designated blocked sentence. -/
theorem FormalReflectionOperatorSemantics.realizesSemanticResolution
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.resolvesBlockedSemantically := by
  exact ⟨R.strongerFramework, R.stronger_reflects_blocked⟩

/-- Package the supplied admission fact for the designated blocked sentence. -/
theorem FormalReflectionOperatorSemantics.realizesLicensedAdmission
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.hasLicensedAdmission := by
  exact ⟨R.blockedSentence, R.blocked_licensedAdmission⟩

/-- Existence of a witness and sentence satisfying the four supplied
obstruction-side predicates. -/
def FormalObstructionSemantics.hasSemanticObstruction
    {B : FormalBaseTheorySemantics}
    (O : FormalObstructionSemantics B) : Prop :=
  ∃ w s, O.selfReferential w ∧ O.obstructs w s ∧ ¬ B.proves s ∧ B.trueInReferenceModel s

/-- Package the designated obstruction witness and sentence. -/
theorem FormalObstructionSemantics.realizesSemanticObstruction
    {B : FormalBaseTheorySemantics}
    (O : FormalObstructionSemantics B) :
    O.hasSemanticObstruction := by
  exact ⟨O.witness, O.blockedBy O.witness, O.witness_selfReferential,
    O.witness_obstructs_blocked, O.blocked_not_provable, O.blocked_true⟩

/-- Existence of an admission and sentence satisfying certification and truth. -/
def FormalReimportSemantics.hasSemanticReimport
    {B : FormalBaseTheorySemantics}
    (R : FormalReimportSemantics B) : Prop :=
  ∃ a s, R.certifies a s ∧ B.trueInReferenceModel s

/-- Package the designated admission and imported sentence. -/
theorem FormalReimportSemantics.realizesSemanticReimport
    {B : FormalBaseTheorySemantics}
    (R : FormalReimportSemantics B) :
    R.hasSemanticReimport := by
  exact ⟨R.witness, R.importedSentence, R.witness_certifies_imported, R.imported_true⟩

/-- Equalities and relation fields connecting the three abstract interfaces. -/
structure FormalSemanticCoherence
    {B : FormalBaseTheorySemantics}
    (O : FormalObstructionSemantics B)
    (R : FormalReflectionOperatorSemantics B)
    (I : FormalReimportSemantics B) where
  obstruction_blocked_eq_reflection_blocked :
    O.blockedBy O.witness = R.blockedSentence
  reflection_blocked_eq_reimported :
    R.blockedSentence = I.importedSentence
  reflection_covers_obstruction :
    R.reflects R.strongerFramework (O.blockedBy O.witness)
  reimport_certifies_reflection_blocked :
    I.certifies I.witness R.blockedSentence

/-- The reflection relation required by the coherence record. -/
def FormalSemanticCoherence.obstructionTransfersToReflection
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (_C : FormalSemanticCoherence O R I) : Prop :=
  R.reflects R.strongerFramework (O.blockedBy O.witness)

/-- The certification relation required by the coherence record. -/
def FormalSemanticCoherence.reflectionTransfersToReimport
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (_C : FormalSemanticCoherence O R I) : Prop :=
  I.certifies I.witness R.blockedSentence

/-- Project the coherence record's reflection field. -/
theorem FormalSemanticCoherence.realizesObstructionToReflection
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (C : FormalSemanticCoherence O R I) :
    C.obstructionTransfersToReflection := by
  exact C.reflection_covers_obstruction

/-- Project the coherence record's certification field. -/
theorem FormalSemanticCoherence.realizesReflectionToReimport
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (C : FormalSemanticCoherence O R I) :
    C.reflectionTransfersToReimport := by
  exact C.reimport_certifies_reflection_blocked

/-- Bundle four proposition-bearing records with an ascent profile and supplied
stagewise-compatibility proof. The component propositions remain abstract. -/
structure ExternalClassicalComparisonObject where
  baseTheory : HistoricalBaseTheoryProfile
  obstruction : HistoricalObstructionWitness
  strongerFramework : HistoricalFrameworkOperator
  reimport : HistoricalReimportMap
  family : AscentFamily
  profile : AscentProfile
  profileShape :
    profile.shape = {
      hasBaseSystem := baseTheory.hasBaseSystem
      hasSelfObstruction := obstruction.hasSelfObstruction
      blockedInBase := obstruction.blockedInBase
      hasStrongerFramework := strongerFramework.frameworkAvailable
      resolvedInFramework := strongerFramework.resolvesInFramework
      licensedReimport := reimport.licensedReimport
    }
  profileFamily : profile.family = family
  compatible :
    StagewiseEquivalent profile.shape dpSixStepStructuralProfile
      ∧ profile.family = AscentFamily.reflection

/-- Bundle the abstract witness interfaces, their coherence record, and a
supplied stagewise-compatibility proof. The type does not identify these
interfaces with a historical formal system; such an identification requires an
adapter. -/
structure FormalExternalClassicalComparisonObject where
  baseSemantics : FormalHistoricalBaseTheory
  obstructionSemantics : FormalHistoricalObstruction
  frameworkSemantics : FormalHistoricalFramework
  reimportSemantics : FormalHistoricalReimport
  baseTheoryContent : FormalBaseTheorySemantics
  obstructionContent : FormalObstructionSemantics baseTheoryContent
  reflectionContent : FormalReflectionOperatorSemantics baseTheoryContent
  reimportContent : FormalReimportSemantics baseTheoryContent
  semanticCoherence :
    FormalSemanticCoherence obstructionContent reflectionContent reimportContent
  family : AscentFamily
  profile : AscentProfile
  profileShape :
    profile.shape = {
      hasBaseSystem := baseSemantics.hasBaseSystem
      hasSelfObstruction := obstructionSemantics.hasSelfObstruction
      blockedInBase := obstructionSemantics.blockedInBase
      hasStrongerFramework := frameworkSemantics.frameworkAvailable
      resolvedInFramework := frameworkSemantics.resolvesInFramework
      licensedReimport := reimportSemantics.licensedReimport
    }
  profileFamily : profile.family = family
  compatible :
    StagewiseEquivalent profile.shape dpSixStepStructuralProfile
      ∧ profile.family = AscentFamily.reflection

/-- Forget witness carriers and retain their existential propositions, labels,
and profile data. -/
def FormalExternalClassicalComparisonObject.toExternalClassicalComparisonObject
    (E : FormalExternalClassicalComparisonObject) :
    ExternalClassicalComparisonObject where
  baseTheory := {
    label := E.baseSemantics.label
    registerApprox? := E.baseSemantics.registerApprox?
    hasBaseSystem := E.baseSemantics.hasBaseSystem
  }
  obstruction := {
    label := E.obstructionSemantics.label
    hasSelfObstruction := E.obstructionSemantics.hasSelfObstruction
    blockedInBase := E.obstructionSemantics.blockedInBase
  }
  strongerFramework := {
    label := E.frameworkSemantics.label
    frameworkAvailable := E.frameworkSemantics.frameworkAvailable
    resolvesInFramework := E.frameworkSemantics.resolvesInFramework
  }
  reimport := {
    label := E.reimportSemantics.label
    licensedReimport := E.reimportSemantics.licensedReimport
  }
  family := E.family
  profile := E.profile
  profileShape := by
    simpa [
      FormalHistoricalBaseTheory.hasBaseSystem,
      FormalHistoricalObstruction.hasSelfObstruction,
      FormalHistoricalObstruction.blockedInBase,
      FormalHistoricalFramework.frameworkAvailable,
      FormalHistoricalFramework.resolvesInFramework,
      FormalHistoricalReimport.licensedReimport
    ] using E.profileShape
  profileFamily := E.profileFamily
  compatible := E.compatible

/-- Repackage the DP-side structural record with its family and optional
metadata fields. -/
def dpAsClassicalAscentProfile : AscentProfile where
  shape := dpSixStepStructuralProfile
  family := AscentFamily.reflection
  complexity? := some artsGieslLicenseProfile.complexity
  targetTheory? := some artsGieslReverseMathCalibration.target

/-- Stagewise logical equivalence to the DP shape plus equality of family tags. -/
def CompatibleWithDp (C : AscentProfile) : Prop :=
  StagewiseEquivalent C.shape dpSixStepStructuralProfile
    ∧ C.family = AscentFamily.reflection

@[simp] theorem dpAsClassicalAscentProfile_family :
    dpAsClassicalAscentProfile.family = AscentFamily.reflection := rfl

@[simp] theorem dpAsClassicalAscentProfile_targetTheory :
    dpAsClassicalAscentProfile.targetTheory? = some FormalTheory.RCA0_WO_omega3 := by
  simp [dpAsClassicalAscentProfile, arts_giesl_reverse_math_target]

theorem dpAsClassicalAscentProfile_compatible : CompatibleWithDp dpAsClassicalAscentProfile := by
  constructor
  · intro s
    rfl
  · rfl

/-- Six-stage all-`True` synthetic profile labelled as a Gödel comparison.
Its fields are stipulated finite predicates rather than an encoded historical
theorem. -/
def godel1931PaperAscentProfile : AscentProfile where
  shape := {
    hasBaseSystem := True
    hasSelfObstruction := True
    blockedInBase := True
    hasStrongerFramework := True
    resolvedInFramework := True
    licensedReimport := True
  }
  family := AscentFamily.reflection

/-- Presentation labels attached to the synthetic all-`True` profile. -/
def godel1931PaperComparison : ConcreteComparisonProfile where
  profile := godel1931PaperAscentProfile
  baseSystemLabel := "PA"
  obstructionLabel := "self-referential Gödel sentence"
  blockedLabel := "base-language incompleteness"
  strongerFrameworkLabel := "external reflection / stronger metatheory"
  resolutionLabel := "truth proved at the stronger level"
  licensedReimportLabel := "externally licensed truth admission"

/-- Classification tags attached to the synthetic Gödel-labelled profile. -/
def godel1931HistoricalAnnotation : HistoricalComparisonAnnotation where
  baseKind := HistoricalBaseKind.peanoArithmetic
  obstructionKind := HistoricalObstructionKind.godelSentence
  frameworkKind := HistoricalFrameworkKind.externalReflection
  resolutionKind := HistoricalResolutionKind.strongerTheoryTruth
  reimportKind := HistoricalReimportKind.licensedTruthAdmission

theorem godel1931PaperAscentProfile_realizesSixStep :
    RealizesSixStepShape godel1931PaperAscentProfile.shape := by
  simp [godel1931PaperAscentProfile, RealizesSixStepShape]

/-- The synthetic all-`True` profile is stagewise equivalent to the DP profile,
whose six fields are proved true by `structural_identity`. -/
theorem godel1931PaperAscentProfile_compatible :
    CompatibleWithDp godel1931PaperAscentProfile := by
  rcases structural_identity with
    ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
  constructor
  · intro s
    cases s with
    | baseSystem =>
        exact iff_of_true trivial hBase
    | selfObstruction =>
        exact iff_of_true trivial hSelf
    | blockedInBase =>
        exact iff_of_true trivial hBlocked
    | strongerFramework =>
        exact iff_of_true trivial hStronger
    | resolvedInFramework =>
        exact iff_of_true trivial hResolved
    | licensedReimport =>
        exact iff_of_true trivial hLicensed
  · rfl

/-- Stagewise equivalence transports the DP profile's six supplied facts. -/
theorem compatibleWithDp_realizesSixStep
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    RealizesSixStepShape C.shape := by
  exact hC.1.symm.preserves_realization structural_identity

/-- Project stagewise equivalence at `blockedInBase`. -/
theorem compatibleWithDp_blockedInBase_iff
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    C.shape.blockedInBase ↔ dpSixStepStructuralProfile.blockedInBase :=
  hC.1 StructuralStage.blockedInBase

/-- Project stagewise equivalence at `resolvedInFramework`. -/
theorem compatibleWithDp_resolvedInFramework_iff
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    C.shape.resolvedInFramework ↔ dpSixStepStructuralProfile.resolvedInFramework :=
  hC.1 StructuralStage.resolvedInFramework

/-- Repackage the compatibility field as realization, family equality, and
stagewise equivalence. -/
theorem ExternalClassicalComparisonObject.supported
    (E : ExternalClassicalComparisonObject) :
    RealizesSixStepShape E.profile.shape
      ∧ E.profile.family = AscentFamily.reflection
      ∧ StagewiseEquivalent E.profile.shape dpAsClassicalAscentProfile.shape := by
  refine ⟨compatibleWithDp_realizesSixStep E.profile E.compatible, ?_, ?_⟩
  · exact E.compatible.2
  · simpa [dpAsClassicalAscentProfile] using E.compatible.1

/-- Apply the same profile result after forgetting witness carriers. -/
theorem FormalExternalClassicalComparisonObject.supported
    (E : FormalExternalClassicalComparisonObject) :
    RealizesSixStepShape E.profile.shape
      ∧ E.profile.family = AscentFamily.reflection
      ∧ StagewiseEquivalent E.profile.shape dpAsClassicalAscentProfile.shape := by
  exact E.toExternalClassicalComparisonObject.supported

/-- Collect existential consequences of the object's supplied predicate and
witness fields. Application to an external historical system requires a
separate adapter establishing those predicates. -/
theorem FormalExternalClassicalComparisonObject.semanticSupported
    (E : FormalExternalClassicalComparisonObject) :
    E.baseTheoryContent.hasInternalProofLayer
      ∧ E.obstructionContent.hasSemanticObstruction
      ∧ E.reflectionContent.hasBlockedSemanticSentence
      ∧ E.reflectionContent.hasReflectionOperator
      ∧ E.reflectionContent.resolvesBlockedSemantically
      ∧ E.reflectionContent.hasLicensedAdmission
      ∧ E.reimportContent.hasSemanticReimport := by
  exact ⟨E.baseTheoryContent.realizesInternalProofLayer,
    E.obstructionContent.realizesSemanticObstruction,
    E.reflectionContent.realizesBlockedSemanticSentence,
    E.reflectionContent.realizesReflectionOperator,
    E.reflectionContent.realizesSemanticResolution,
    E.reflectionContent.realizesLicensedAdmission,
    E.reimportContent.realizesSemanticReimport⟩

/-- Project the two relation fields from the supplied coherence record. -/
theorem FormalExternalClassicalComparisonObject.semanticTransferSupported
    (E : FormalExternalClassicalComparisonObject) :
    E.semanticCoherence.obstructionTransfersToReflection
      ∧ E.semanticCoherence.reflectionTransfersToReimport := by
  exact ⟨E.semanticCoherence.realizesObstructionToReflection,
    E.semanticCoherence.realizesReflectionToReimport⟩

/-- Gödel-labelled base profile whose proposition is stipulated as `True`. -/
def godel1931BaseTheoryProfile : HistoricalBaseTheoryProfile where
  label := "PA"
  hasBaseSystem := True

/-- Gödel-labelled obstruction profile whose two propositions are stipulated
as `True`. -/
def godel1931ObstructionWitness : HistoricalObstructionWitness where
  label := "self-referential Gödel sentence"
  hasSelfObstruction := True
  blockedInBase := True

/-- Gödel-labelled framework profile whose propositions are stipulated as
`True`. -/
def godel1931StrongerFrameworkOperator : HistoricalFrameworkOperator where
  label := "external reflection / stronger metatheory"
  frameworkAvailable := True
  resolvesInFramework := True

/-- Gödel-labelled reimport profile whose proposition is stipulated as `True`. -/
def godel1931ReimportMap : HistoricalReimportMap where
  label := "externally licensed truth admission"
  licensedReimport := True

/-- Unit-carrier witness model with a constantly true proof predicate, scoped to
the synthetic finite comparison. -/
def godel1931FormalBaseTheory : FormalHistoricalBaseTheory where
  label := "PA"
  Sentence := Unit
  provesBaseSystem _ := True
  witness := ()
  witness_provesBaseSystem := trivial

/-- Two constructor tags used by the synthetic Gödel-labelled model. -/
inductive GodelSentenceSemantic
  | paBaseSentence
  | godelBlockedSentence
  deriving DecidableEq, Repr

/-- One constructor tag used by the synthetic framework model. -/
inductive GodelFrameworkSemantic
  | externalReflection
  deriving DecidableEq, Repr

/-- Synthetic two-sentence model: one proof predicate is true, the other false,
and the reference-truth predicate is true for both by definition. -/
def godel1931BaseTheoryContent : FormalBaseTheorySemantics where
  Sentence := GodelSentenceSemantic
  proves
    | .paBaseSentence => True
    | .godelBlockedSentence => False
  trueInReferenceModel _ := True
  baseSentence := .paBaseSentence
  baseSentence_proves := trivial

/-- Synthetic reflection interface whose relations select the blocked-sentence
tag by definition. A PA reflection theorem would require a separate adapter. -/
def godel1931ReflectionContent :
    FormalReflectionOperatorSemantics godel1931BaseTheoryContent where
  Framework := GodelFrameworkSemantic
  extendsBase _ := True
  reflects _ s := s = .godelBlockedSentence
  licensedAdmission s := s = .godelBlockedSentence
  blockedSentence := .godelBlockedSentence
  blocked_not_provable := by
    simp [godel1931BaseTheoryContent]
  blocked_true := by
    simp [godel1931BaseTheoryContent]
  strongerFramework := .externalReflection
  stronger_extendsBase := trivial
  stronger_reflects_blocked := rfl
  blocked_licensedAdmission := rfl

/-- Unit-carrier obstruction model with both predicates stipulated as `True`. -/
def godel1931FormalObstruction : FormalHistoricalObstruction where
  label := "self-referential Gödel sentence"
  Witness := Unit
  isSelfObstruction _ := True
  blocksBase _ := True
  witness := ()
  witness_isSelfObstruction := trivial
  witness_blocksBase := trivial

/-- Synthetic obstruction interface selecting the blocked-sentence tag. Its
self-reference predicate is stipulated by definition. -/
def godel1931ObstructionContent :
    FormalObstructionSemantics godel1931BaseTheoryContent where
  Witness := Unit
  obstructs _ s := s = .godelBlockedSentence
  selfReferential _ := True
  blockedBy _ := .godelBlockedSentence
  witness := ()
  witness_selfReferential := trivial
  witness_obstructs_blocked := rfl
  blocked_not_provable := by
    exact godel1931ReflectionContent.blocked_not_provable
  blocked_true := by
    exact godel1931ReflectionContent.blocked_true

/-- Unit-carrier framework model with resolution stipulated as `True`. -/
def godel1931FormalFramework : FormalHistoricalFramework where
  label := "external reflection / stronger metatheory"
  Framework := Unit
  resolves _ := True
  availableWitness := ()
  resolver := ()
  resolver_resolves := trivial

/-- Unit-carrier admission model with certification stipulated as `True`. -/
def godel1931FormalReimport : FormalHistoricalReimport where
  label := "externally licensed truth admission"
  Admission := Unit
  certified _ := True
  witness := ()
  witness_certified := trivial

/-- Synthetic reimport interface whose certification predicate selects the
blocked-sentence tag. -/
def godel1931ReimportContent :
    FormalReimportSemantics godel1931BaseTheoryContent where
  Admission := Unit
  certifies _ s := s = .godelBlockedSentence
  importedSentence := .godelBlockedSentence
  witness := ()
  witness_certifies_imported := rfl
  imported_true := by
    exact godel1931ReflectionContent.blocked_true

/-- Definitional coherence among the three synthetic interfaces. -/
def godel1931SemanticCoherence :
    FormalSemanticCoherence
      godel1931ObstructionContent
      godel1931ReflectionContent
      godel1931ReimportContent where
  obstruction_blocked_eq_reflection_blocked := rfl
  reflection_blocked_eq_reimported := rfl
  reflection_covers_obstruction := by
    exact godel1931ReflectionContent.stronger_reflects_blocked
  reimport_certifies_reflection_blocked := by
    exact godel1931ReimportContent.witness_certifies_imported

/-- Aggregate the synthetic Gödel-labelled interfaces and their stagewise
compatibility proof. -/
def godel1931FormalExternalClassicalComparisonObject :
    FormalExternalClassicalComparisonObject where
  baseSemantics := godel1931FormalBaseTheory
  obstructionSemantics := godel1931FormalObstruction
  frameworkSemantics := godel1931FormalFramework
  reimportSemantics := godel1931FormalReimport
  baseTheoryContent := godel1931BaseTheoryContent
  obstructionContent := godel1931ObstructionContent
  reflectionContent := godel1931ReflectionContent
  reimportContent := godel1931ReimportContent
  semanticCoherence := godel1931SemanticCoherence
  family := AscentFamily.reflection
  profile := {
    shape := {
      hasBaseSystem := godel1931FormalBaseTheory.hasBaseSystem
      hasSelfObstruction := godel1931FormalObstruction.hasSelfObstruction
      blockedInBase := godel1931FormalObstruction.blockedInBase
      hasStrongerFramework := godel1931FormalFramework.frameworkAvailable
      resolvedInFramework := godel1931FormalFramework.resolvesInFramework
      licensedReimport := godel1931FormalReimport.licensedReimport
    }
    family := AscentFamily.reflection
  }
  profileShape := rfl
  profileFamily := rfl
  compatible := by
    rcases structural_identity with
      ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
    constructor
    · intro s
      cases s with
      | baseSystem =>
          exact iff_of_true godel1931FormalBaseTheory.realizesBaseSystem hBase
      | selfObstruction =>
          exact iff_of_true godel1931FormalObstruction.realizesSelfObstruction hSelf
      | blockedInBase =>
          exact iff_of_true godel1931FormalObstruction.realizesBlockedInBase hBlocked
      | strongerFramework =>
          exact iff_of_true godel1931FormalFramework.realizesAvailability hStronger
      | resolvedInFramework =>
          exact iff_of_true godel1931FormalFramework.realizesResolution hResolved
      | licensedReimport =>
          exact iff_of_true godel1931FormalReimport.realizesLicensedReimport hLicensed
    · rfl

/-- Project profile realization and compatibility from the synthetic object. -/
theorem godel1931FormalExternalClassicalComparison_supported :
    RealizesSixStepShape godel1931FormalExternalClassicalComparisonObject.profile.shape
      ∧ godel1931FormalExternalClassicalComparisonObject.profile.family =
          AscentFamily.reflection
      ∧ StagewiseEquivalent
          godel1931FormalExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931FormalExternalClassicalComparisonObject.supported

/-- Collect existential facts that follow from the synthetic object's
definition. The conclusion remains within the stipulated finite model. -/
theorem godel1931FormalExternalClassicalComparison_semanticSupported :
    godel1931FormalExternalClassicalComparisonObject.baseTheoryContent.hasInternalProofLayer
      ∧ godel1931FormalExternalClassicalComparisonObject.obstructionContent.hasSemanticObstruction
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.hasBlockedSemanticSentence
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.resolvesBlockedSemantically
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.hasLicensedAdmission
      ∧ godel1931FormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport := by
  exact godel1931FormalExternalClassicalComparisonObject.semanticSupported

/-- Project the synthetic coherence record's two relation fields. -/
theorem godel1931FormalExternalClassicalComparison_transferSupported :
    godel1931FormalExternalClassicalComparisonObject.semanticCoherence.obstructionTransfersToReflection
      ∧ godel1931FormalExternalClassicalComparisonObject.semanticCoherence.reflectionTransfersToReimport := by
  exact godel1931FormalExternalClassicalComparisonObject.semanticTransferSupported

/-- Forget the synthetic object's witness carriers and retain its profile-level
fields. -/
def godel1931ExternalClassicalComparisonObject :
    ExternalClassicalComparisonObject :=
  godel1931FormalExternalClassicalComparisonObject.toExternalClassicalComparisonObject

end OperatorKO7.ClassicalAscentProfile
