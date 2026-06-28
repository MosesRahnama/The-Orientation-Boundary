import OperatorKO7.Meta.ReflectionSchema

/-!
# Classical Ascent Profile

Paper-facing comparison wrapper above `ReflectionSchema`.

This file packages the already mechanized DP-side profile as a classical-style
ascent profile and defines the exact compatibility condition any future
classical-side profile must satisfy before it can legitimately be compared to
that DP profile.
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

/-- Comparison-ready ascent profile. -/
structure AscentProfile where
  shape : SixStepStructuralProfile
  family : AscentFamily
  complexity? : Option FormulaClass := none
  targetTheory? : Option FormalTheory := none

/-- Concrete paper-facing comparison profile with named stage labels. This is a
disciplined artifact object, not a formalization of the surrounding historical
arithmetic. -/
structure ConcreteComparisonProfile where
  profile : AscentProfile
  baseSystemLabel : String
  obstructionLabel : String
  blockedLabel : String
  strongerFrameworkLabel : String
  resolutionLabel : String
  licensedReimportLabel : String

/-- Coarse historical base-system tag for paper-facing comparison objects. -/
inductive HistoricalBaseKind
  | peanoArithmetic
  | benchmarkContractKO7
  deriving DecidableEq, Repr

/-- Coarse historical obstruction tag. -/
inductive HistoricalObstructionKind
  | godelSentence
  | noDirectWholeWitness
  deriving DecidableEq, Repr

/-- Coarse historical stronger-framework tag. -/
inductive HistoricalFrameworkKind
  | externalReflection
  | transformedCallTransport
  deriving DecidableEq, Repr

/-- Coarse historical resolution tag. -/
inductive HistoricalResolutionKind
  | strongerTheoryTruth
  | transformedCallWitness
  deriving DecidableEq, Repr

/-- Coarse historical reimport tag. -/
inductive HistoricalReimportKind
  | licensedTruthAdmission
  | contractLicensedWitness
  deriving DecidableEq, Repr

/-- Typed historical annotation sitting above a concrete paper-facing
comparison profile. This stays deliberately coarse and artifact honest. -/
structure HistoricalComparisonAnnotation where
  baseKind : HistoricalBaseKind
  obstructionKind : HistoricalObstructionKind
  frameworkKind : HistoricalFrameworkKind
  resolutionKind : HistoricalResolutionKind
  reimportKind : HistoricalReimportKind

/-- Base-theory profile for the richer external classical comparison layer. -/
structure HistoricalBaseTheoryProfile where
  label : String
  registerApprox? : Option FormalTheory := none
  hasBaseSystem : Prop

/-- Explicit obstruction witness family for the richer external comparison
layer. -/
structure HistoricalObstructionWitness where
  label : String
  hasSelfObstruction : Prop
  blockedInBase : Prop

/-- Explicit stronger-framework operator for the richer external comparison
layer. -/
structure HistoricalFrameworkOperator where
  label : String
  frameworkAvailable : Prop
  resolvesInFramework : Prop

/-- Explicit reimport / licensed-admission map for the richer external
comparison layer. -/
structure HistoricalReimportMap where
  label : String
  licensedReimport : Prop

/-- Formal base-theory semantics for the external classical comparison layer. -/
structure FormalHistoricalBaseTheory where
  label : String
  registerApprox? : Option FormalTheory := none
  Sentence : Type
  provesBaseSystem : Sentence → Prop
  witness : Sentence
  witness_provesBaseSystem : provesBaseSystem witness

/-- Formal obstruction semantics for the external classical comparison layer. -/
structure FormalHistoricalObstruction where
  label : String
  Witness : Type
  isSelfObstruction : Witness → Prop
  blocksBase : Witness → Prop
  witness : Witness
  witness_isSelfObstruction : isSelfObstruction witness
  witness_blocksBase : blocksBase witness

/-- Formal stronger-framework semantics for the external classical comparison
layer. -/
structure FormalHistoricalFramework where
  label : String
  Framework : Type
  resolves : Framework → Prop
  availableWitness : Framework
  resolver : Framework
  resolver_resolves : resolves resolver

/-- Formal reimport / licensed-admission semantics for the external classical
comparison layer. -/
structure FormalHistoricalReimport where
  label : String
  Admission : Type
  certified : Admission → Prop
  witness : Admission
  witness_certified : certified witness

/-- Deeper semantic content for the base theory itself: a sentence type,
an internal proof predicate, and a reference-model truth predicate. -/
structure FormalBaseTheorySemantics where
  Sentence : Type
  proves : Sentence → Prop
  trueInReferenceModel : Sentence → Prop
  baseSentence : Sentence
  baseSentence_proves : proves baseSentence

/-- Semantic content for the stronger framework / reflection operator.

This records an actual blocked sentence at the base layer together with:

- a stronger framework extending the base layer,
- a semantic reflection/transport operation validating that blocked sentence,
- and a licensed-admission predicate for reimporting that sentence.
-/
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

/-- Deeper semantic content for the obstruction layer itself: a witness family,
an obstruction relation into the base-theory sentence space, and a designated
blocked sentence carried by the obstruction witness. -/
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

/-- Deeper semantic content for the reimport / licensed-admission layer:
an admission carrier together with a certification relation on sentences in the
base-theory semantic space. -/
structure FormalReimportSemantics
    (B : FormalBaseTheorySemantics) where
  Admission : Type
  certifies : Admission → B.Sentence → Prop
  importedSentence : B.Sentence
  witness : Admission
  witness_certifies_imported : certifies witness importedSentence
  imported_true : B.trueInReferenceModel importedSentence

/-- Derived base-system proposition from the formal base-theory semantics. -/
def FormalHistoricalBaseTheory.hasBaseSystem
    (B : FormalHistoricalBaseTheory) : Prop :=
  ∃ s, B.provesBaseSystem s

/-- The designated base-theory witness realizes the derived base-system
proposition. -/
theorem FormalHistoricalBaseTheory.realizesBaseSystem
    (B : FormalHistoricalBaseTheory) :
    B.hasBaseSystem := by
  exact ⟨B.witness, B.witness_provesBaseSystem⟩

/-- Derived self-obstruction proposition from the formal obstruction
semantics. -/
def FormalHistoricalObstruction.hasSelfObstruction
    (O : FormalHistoricalObstruction) : Prop :=
  ∃ w, O.isSelfObstruction w

/-- Derived base-blocking proposition from the formal obstruction semantics. -/
def FormalHistoricalObstruction.blockedInBase
    (O : FormalHistoricalObstruction) : Prop :=
  ∃ w, O.blocksBase w

/-- The designated obstruction witness realizes self-obstruction. -/
theorem FormalHistoricalObstruction.realizesSelfObstruction
    (O : FormalHistoricalObstruction) :
    O.hasSelfObstruction := by
  exact ⟨O.witness, O.witness_isSelfObstruction⟩

/-- The designated obstruction witness realizes the base-blocking property. -/
theorem FormalHistoricalObstruction.realizesBlockedInBase
    (O : FormalHistoricalObstruction) :
    O.blockedInBase := by
  exact ⟨O.witness, O.witness_blocksBase⟩

/-- Derived framework-availability proposition from the formal stronger-framework
semantics. -/
def FormalHistoricalFramework.frameworkAvailable
    (F : FormalHistoricalFramework) : Prop :=
  Nonempty F.Framework

/-- Derived stronger-framework resolution proposition from the formal
stronger-framework semantics. -/
def FormalHistoricalFramework.resolvesInFramework
    (F : FormalHistoricalFramework) : Prop :=
  ∃ x, F.resolves x

/-- The designated framework witness realizes availability. -/
theorem FormalHistoricalFramework.realizesAvailability
    (F : FormalHistoricalFramework) :
    F.frameworkAvailable := by
  exact ⟨F.availableWitness⟩

/-- The designated resolver realizes the stronger-framework resolution
proposition. -/
theorem FormalHistoricalFramework.realizesResolution
    (F : FormalHistoricalFramework) :
    F.resolvesInFramework := by
  exact ⟨F.resolver, F.resolver_resolves⟩

/-- Derived licensed-reimport proposition from the formal reimport semantics. -/
def FormalHistoricalReimport.licensedReimport
    (R : FormalHistoricalReimport) : Prop :=
  ∃ a, R.certified a

/-- The designated reimport witness realizes the licensed-reimport
proposition. -/
theorem FormalHistoricalReimport.realizesLicensedReimport
    (R : FormalHistoricalReimport) :
    R.licensedReimport := by
  exact ⟨R.witness, R.witness_certified⟩

/-- Derived internal-proof-layer proposition from the deeper base-theory
semantics. -/
def FormalBaseTheorySemantics.hasInternalProofLayer
    (B : FormalBaseTheorySemantics) : Prop :=
  ∃ s, B.proves s

/-- The designated base sentence realizes the internal proof layer. -/
theorem FormalBaseTheorySemantics.realizesInternalProofLayer
    (B : FormalBaseTheorySemantics) :
    B.hasInternalProofLayer := by
  exact ⟨B.baseSentence, B.baseSentence_proves⟩

/-- Derived semantic obstruction proposition: some sentence is true in the
reference model but unprovable in the base layer. -/
def FormalReflectionOperatorSemantics.hasBlockedSemanticSentence
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ s, ¬ B.proves s ∧ B.trueInReferenceModel s

/-- Derived semantic stronger-framework proposition. -/
def FormalReflectionOperatorSemantics.hasReflectionOperator
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ F, R.extendsBase F

/-- Derived semantic resolution proposition. -/
def FormalReflectionOperatorSemantics.resolvesBlockedSemantically
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ F s, R.reflects F s

/-- Derived semantic licensed-admission proposition. -/
def FormalReflectionOperatorSemantics.hasLicensedAdmission
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) : Prop :=
  ∃ s, R.licensedAdmission s

/-- The designated blocked sentence realizes semantic obstruction. -/
theorem FormalReflectionOperatorSemantics.realizesBlockedSemanticSentence
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.hasBlockedSemanticSentence := by
  exact ⟨R.blockedSentence, R.blocked_not_provable, R.blocked_true⟩

/-- The designated stronger framework realizes semantic availability. -/
theorem FormalReflectionOperatorSemantics.realizesReflectionOperator
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.hasReflectionOperator := by
  exact ⟨R.strongerFramework, R.stronger_extendsBase⟩

/-- The designated stronger framework resolves the blocked sentence
semantically. -/
theorem FormalReflectionOperatorSemantics.realizesSemanticResolution
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.resolvesBlockedSemantically := by
  exact ⟨R.strongerFramework, R.blockedSentence, R.stronger_reflects_blocked⟩

/-- The designated blocked sentence is licensed for reimport. -/
theorem FormalReflectionOperatorSemantics.realizesLicensedAdmission
    {B : FormalBaseTheorySemantics}
    (R : FormalReflectionOperatorSemantics B) :
    R.hasLicensedAdmission := by
  exact ⟨R.blockedSentence, R.blocked_licensedAdmission⟩

/-- Derived semantic obstruction proposition from the deeper obstruction
semantics. -/
def FormalObstructionSemantics.hasSemanticObstruction
    {B : FormalBaseTheorySemantics}
    (O : FormalObstructionSemantics B) : Prop :=
  ∃ w s, O.selfReferential w ∧ O.obstructs w s ∧ ¬ B.proves s ∧ B.trueInReferenceModel s

/-- The designated obstruction witness realizes semantic obstruction. -/
theorem FormalObstructionSemantics.realizesSemanticObstruction
    {B : FormalBaseTheorySemantics}
    (O : FormalObstructionSemantics B) :
    O.hasSemanticObstruction := by
  exact ⟨O.witness, O.blockedBy O.witness, O.witness_selfReferential,
    O.witness_obstructs_blocked, O.blocked_not_provable, O.blocked_true⟩

/-- Derived semantic licensed-reimport proposition from the deeper reimport
semantics. -/
def FormalReimportSemantics.hasSemanticReimport
    {B : FormalBaseTheorySemantics}
    (R : FormalReimportSemantics B) : Prop :=
  ∃ a s, R.certifies a s ∧ B.trueInReferenceModel s

/-- The designated admission witness realizes semantic reimport. -/
theorem FormalReimportSemantics.realizesSemanticReimport
    {B : FormalBaseTheorySemantics}
    (R : FormalReimportSemantics B) :
    R.hasSemanticReimport := by
  exact ⟨R.witness, R.importedSentence, R.witness_certifies_imported, R.imported_true⟩

/-- Coherence data tying the deeper obstruction, reflection, and reimport
semantics into one staged transfer story. -/
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

/-- Derived semantic obstruction-to-reflection transfer proposition. -/
def FormalSemanticCoherence.obstructionTransfersToReflection
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (C : FormalSemanticCoherence O R I) : Prop :=
  R.reflects R.strongerFramework (O.blockedBy O.witness)

/-- Derived semantic reflection-to-reimport transfer proposition. -/
def FormalSemanticCoherence.reflectionTransfersToReimport
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (C : FormalSemanticCoherence O R I) : Prop :=
  I.certifies I.witness R.blockedSentence

/-- The coherence object realizes the obstruction-to-reflection transfer. -/
theorem FormalSemanticCoherence.realizesObstructionToReflection
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (C : FormalSemanticCoherence O R I) :
    C.obstructionTransfersToReflection := by
  exact C.reflection_covers_obstruction

/-- The coherence object realizes the reflection-to-reimport transfer. -/
theorem FormalSemanticCoherence.realizesReflectionToReimport
    {B : FormalBaseTheorySemantics}
    {O : FormalObstructionSemantics B}
    {R : FormalReflectionOperatorSemantics B}
    {I : FormalReimportSemantics B}
    (C : FormalSemanticCoherence O R I) :
    C.reflectionTransfersToReimport := by
  exact C.reimport_certifies_reflection_blocked

/-- Richer external classical comparison object.

This goes beyond labels and annotations: it packages the base-theory profile,
obstruction witness, stronger-framework operator, and reimport map together
with a concrete ascent profile and a theorem that the resulting profile is
compatible with the mechanized DP-side profile. -/
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

/-- Stronger external classical comparison object with typed witness semantics
for the base theory, obstruction, stronger framework, and reimport step. -/
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

/-- Forget typed witness semantics and recover the lighter external comparison
object. -/
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

/-- The mechanized DP confession viewed as a comparison-ready ascent profile. -/
def dpAsClassicalAscentProfile : AscentProfile where
  shape := dpSixStepStructuralProfile
  family := AscentFamily.reflection
  complexity? := some artsGieslLicenseProfile.complexity
  targetTheory? := some artsGieslReverseMathCalibration.target

/-- Compatibility condition for a future classical-side comparison profile. -/
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

/-- Named paper-facing right-hand profile for the Gödel-side comparison. The
shape is intentionally concrete and fully realized inside the artifact, while
the surrounding historical interpretation remains outside the Lean claim. -/
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

/-- Named stage labels for the paper-facing Gödel-side comparison object. -/
def godel1931PaperComparison : ConcreteComparisonProfile where
  profile := godel1931PaperAscentProfile
  baseSystemLabel := "PA"
  obstructionLabel := "self-referential Gödel sentence"
  blockedLabel := "base-language incompleteness"
  strongerFrameworkLabel := "external reflection / stronger metatheory"
  resolutionLabel := "truth proved at the stronger level"
  licensedReimportLabel := "externally licensed truth admission"

/-- Typed historical annotation for the paper-facing Gödel-side comparison. -/
def godel1931HistoricalAnnotation : HistoricalComparisonAnnotation where
  baseKind := HistoricalBaseKind.peanoArithmetic
  obstructionKind := HistoricalObstructionKind.godelSentence
  frameworkKind := HistoricalFrameworkKind.externalReflection
  resolutionKind := HistoricalResolutionKind.strongerTheoryTruth
  reimportKind := HistoricalReimportKind.licensedTruthAdmission

theorem godel1931PaperAscentProfile_realizesSixStep :
    RealizesSixStepShape godel1931PaperAscentProfile.shape := by
  simp [godel1931PaperAscentProfile, RealizesSixStepShape]

/-- Concrete theorem-backed classical-side comparison instantiation for the
paper-facing Gödel profile. -/
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

/-- Any comparison-ready profile that matches the DP stagewise shape and keeps
reflection-family status inherits the six-step realization. -/
theorem compatibleWithDp_realizesSixStep
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    RealizesSixStepShape C.shape := by
  exact hC.1.symm.preserves_realization structural_identity

/-- A compatible profile remains blocked in the base layer exactly when the DP
profile is blocked in the base layer. -/
theorem compatibleWithDp_blockedInBase_iff
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    C.shape.blockedInBase ↔ dpSixStepStructuralProfile.blockedInBase :=
  hC.1 StructuralStage.blockedInBase

/-- A compatible profile resolves only at the stronger framework stage exactly
when the DP profile does. -/
theorem compatibleWithDp_resolvedInFramework_iff
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    C.shape.resolvedInFramework ↔ dpSixStepStructuralProfile.resolvedInFramework :=
  hC.1 StructuralStage.resolvedInFramework

/-- Any richer external classical comparison object is theorem-backed at the
profile level. -/
theorem ExternalClassicalComparisonObject.supported
    (E : ExternalClassicalComparisonObject) :
    RealizesSixStepShape E.profile.shape
      ∧ E.profile.family = AscentFamily.reflection
      ∧ StagewiseEquivalent E.profile.shape dpAsClassicalAscentProfile.shape := by
  refine ⟨compatibleWithDp_realizesSixStep E.profile E.compatible, ?_, ?_⟩
  · exact E.compatible.2
  · simpa [dpAsClassicalAscentProfile] using E.compatible.1

/-- Any formal external classical comparison object is theorem-backed at the
profile level. -/
theorem FormalExternalClassicalComparisonObject.supported
    (E : FormalExternalClassicalComparisonObject) :
    RealizesSixStepShape E.profile.shape
      ∧ E.profile.family = AscentFamily.reflection
      ∧ StagewiseEquivalent E.profile.shape dpAsClassicalAscentProfile.shape := by
  exact E.toExternalClassicalComparisonObject.supported

/-- Any formal external comparison object now also carries theorem-backed
semantic content for the base theory and the reflection operator themselves. -/
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

/-- Any formal external comparison object also carries theorem-backed staged
transfer from obstruction to reflection and from reflection to reimport. -/
theorem FormalExternalClassicalComparisonObject.semanticTransferSupported
    (E : FormalExternalClassicalComparisonObject) :
    E.semanticCoherence.obstructionTransfersToReflection
      ∧ E.semanticCoherence.reflectionTransfersToReimport := by
  exact ⟨E.semanticCoherence.realizesObstructionToReflection,
    E.semanticCoherence.realizesReflectionToReimport⟩

/-- Richer base-theory profile for the paper-facing Gödel-side comparison. -/
def godel1931BaseTheoryProfile : HistoricalBaseTheoryProfile where
  label := "PA"
  hasBaseSystem := True

/-- Richer obstruction witness for the paper-facing Gödel-side comparison. -/
def godel1931ObstructionWitness : HistoricalObstructionWitness where
  label := "self-referential Gödel sentence"
  hasSelfObstruction := True
  blockedInBase := True

/-- Richer stronger-framework operator for the paper-facing Gödel-side
comparison. -/
def godel1931StrongerFrameworkOperator : HistoricalFrameworkOperator where
  label := "external reflection / stronger metatheory"
  frameworkAvailable := True
  resolvesInFramework := True

/-- Richer reimport map for the paper-facing Gödel-side comparison. -/
def godel1931ReimportMap : HistoricalReimportMap where
  label := "externally licensed truth admission"
  licensedReimport := True

/-- Typed base-theory semantics for the Gödel-side external comparison. -/
def godel1931FormalBaseTheory : FormalHistoricalBaseTheory where
  label := "PA"
  Sentence := Unit
  provesBaseSystem _ := True
  witness := ()
  witness_provesBaseSystem := trivial

/-- Semantic sentence layer for the paper-facing Gödel-side comparison. -/
inductive GodelSentenceSemantic
  | paBaseSentence
  | godelBlockedSentence
  deriving DecidableEq, Repr

/-- Semantic stronger-framework tag for the paper-facing Gödel-side
comparison. -/
inductive GodelFrameworkSemantic
  | externalReflection
  deriving DecidableEq, Repr

/-- Deeper base-theory semantics for the paper-facing Gödel-side comparison. -/
def godel1931BaseTheoryContent : FormalBaseTheorySemantics where
  Sentence := GodelSentenceSemantic
  proves
    | .paBaseSentence => True
    | .godelBlockedSentence => False
  trueInReferenceModel _ := True
  baseSentence := .paBaseSentence
  baseSentence_proves := trivial

/-- Deeper reflection-operator semantics for the paper-facing Gödel-side
comparison. -/
def godel1931ReflectionContent :
    FormalReflectionOperatorSemantics godel1931BaseTheoryContent where
  Framework := GodelFrameworkSemantic
  extendsBase _ := True
  reflects _ s := s = .godelBlockedSentence
  licensedAdmission s := s = .godelBlockedSentence
  blockedSentence := .godelBlockedSentence
  blocked_not_provable := by
    simp [godel1931BaseTheoryContent, FormalBaseTheorySemantics.proves]
  blocked_true := by
    simp [godel1931BaseTheoryContent, FormalBaseTheorySemantics.trueInReferenceModel]
  strongerFramework := .externalReflection
  stronger_extendsBase := trivial
  stronger_reflects_blocked := rfl
  blocked_licensedAdmission := rfl

/-- Typed obstruction semantics for the Gödel-side external comparison. -/
def godel1931FormalObstruction : FormalHistoricalObstruction where
  label := "self-referential Gödel sentence"
  Witness := Unit
  isSelfObstruction _ := True
  blocksBase _ := True
  witness := ()
  witness_isSelfObstruction := trivial
  witness_blocksBase := trivial

/-- Deeper obstruction semantics for the Gödel-side external comparison. -/
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
    simpa [godel1931BaseTheoryContent] using
      godel1931ReflectionContent.blocked_not_provable
  blocked_true := by
    simpa [godel1931BaseTheoryContent] using
      godel1931ReflectionContent.blocked_true

/-- Typed stronger-framework semantics for the Gödel-side external comparison. -/
def godel1931FormalFramework : FormalHistoricalFramework where
  label := "external reflection / stronger metatheory"
  Framework := Unit
  resolves _ := True
  availableWitness := ()
  resolver := ()
  resolver_resolves := trivial

/-- Typed reimport semantics for the Gödel-side external comparison. -/
def godel1931FormalReimport : FormalHistoricalReimport where
  label := "externally licensed truth admission"
  Admission := Unit
  certified _ := True
  witness := ()
  witness_certified := trivial

/-- Deeper semantic reimport layer for the Gödel-side external comparison. -/
def godel1931ReimportContent :
    FormalReimportSemantics godel1931BaseTheoryContent where
  Admission := Unit
  certifies _ s := s = .godelBlockedSentence
  importedSentence := .godelBlockedSentence
  witness := ()
  witness_certifies_imported := rfl
  imported_true := by
    simpa [godel1931BaseTheoryContent] using
      godel1931ReflectionContent.blocked_true

/-- Semantic coherence for the staged Gödel-side transfer:
obstruction -> reflection -> licensed reimport. -/
def godel1931SemanticCoherence :
    FormalSemanticCoherence
      godel1931ObstructionContent
      godel1931ReflectionContent
      godel1931ReimportContent where
  obstruction_blocked_eq_reflection_blocked := rfl
  reflection_blocked_eq_reimported := rfl
  reflection_covers_obstruction := by
    simpa using godel1931ReflectionContent.stronger_reflects_blocked
  reimport_certifies_reflection_blocked := by
    simpa using godel1931ReimportContent.witness_certifies_imported

/-- Stronger formal external classical comparison object for the paper-facing
Gödel-side comparison. -/
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

/-- The stronger formal Gödel-side external comparison object is theorem-backed
at the profile level. -/
theorem godel1931FormalExternalClassicalComparison_supported :
    RealizesSixStepShape godel1931FormalExternalClassicalComparisonObject.profile.shape
      ∧ godel1931FormalExternalClassicalComparisonObject.profile.family =
          AscentFamily.reflection
      ∧ StagewiseEquivalent
          godel1931FormalExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931FormalExternalClassicalComparisonObject.supported

/-- The stronger Gödel-side formal comparison object also has theorem-backed
base-theory and reflection semantics. -/
theorem godel1931FormalExternalClassicalComparison_semanticSupported :
    godel1931FormalExternalClassicalComparisonObject.baseTheoryContent.hasInternalProofLayer
      ∧ godel1931FormalExternalClassicalComparisonObject.obstructionContent.hasSemanticObstruction
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.hasBlockedSemanticSentence
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.resolvesBlockedSemantically
      ∧ godel1931FormalExternalClassicalComparisonObject.reflectionContent.hasLicensedAdmission
      ∧ godel1931FormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport := by
  exact godel1931FormalExternalClassicalComparisonObject.semanticSupported

/-- The stronger Gödel-side formal comparison object also has theorem-backed
obstruction-to-reflection and reflection-to-reimport transfer. -/
theorem godel1931FormalExternalClassicalComparison_transferSupported :
    godel1931FormalExternalClassicalComparisonObject.semanticCoherence.obstructionTransfersToReflection
      ∧ godel1931FormalExternalClassicalComparisonObject.semanticCoherence.reflectionTransfersToReimport := by
  exact godel1931FormalExternalClassicalComparisonObject.semanticTransferSupported

/-- Richer external classical comparison object for the paper-facing
Gödel-side comparison. -/
def godel1931ExternalClassicalComparisonObject :
    ExternalClassicalComparisonObject :=
  godel1931FormalExternalClassicalComparisonObject.toExternalClassicalComparisonObject

end OperatorKO7.ClassicalAscentProfile
