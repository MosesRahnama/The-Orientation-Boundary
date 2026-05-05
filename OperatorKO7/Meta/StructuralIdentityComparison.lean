import OperatorKO7.Meta.ClassicalAscentProfile
import OperatorKO7.Meta.ProjectionAsConservativeExtension

/-!
# Structural Identity Comparison

Comparison theorems for ascent profiles that are stagewise equivalent to the
mechanized DP-side six-step profile.

This does not introduce a new historical theorem. It formalizes the exact shape
of the stronger comparison claim so that any future classical-side profile can
be connectorged into a machine-checked comparison object.
-/

namespace OperatorKO7.StructuralIdentityComparison

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.ProjectionAsConservativeExtension

/-- Comparison object between two ascent profiles. -/
structure ComparisonWitness
    (left right : AscentProfile) where
  sameFamily : left.family = right.family
  sameShape : StagewiseEquivalent left.shape right.shape

/-- Packaged concrete comparison object: a named right-hand profile together
with its explicit comparison witness against the mechanized DP profile. -/
structure HistoricalComparisonObject where
  concrete : ConcreteComparisonProfile
  comparison : ComparisonWitness concrete.profile dpAsClassicalAscentProfile

/-- Stronger packaged comparison object carrying a typed historical annotation
above the concrete comparison profile and its theorem-backed witness. -/
structure AnnotatedHistoricalComparisonObject where
  annotation : HistoricalComparisonAnnotation
  historical : HistoricalComparisonObject

/-- Concrete theorem-bearing historical comparison object.

This is stronger than the earlier annotation-only wrapper: it packages the
named comparison profile together with

- an explicit stagewise realization witness, and
- the theorem-backed comparison witness against the mechanized DP profile.

This is the repository's concrete right-hand historical object, as opposed to a
purely abstract comparison schema. -/
structure GroundedHistoricalComparisonObject where
  annotation : HistoricalComparisonAnnotation
  concrete : ConcreteComparisonProfile
  realization : StagewiseRealization concrete.profile.shape
  comparison : ComparisonWitness concrete.profile dpAsClassicalAscentProfile

/-- Convert a richer external classical comparison object into the grounded
historical comparison interface. -/
def ExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    (annotation : HistoricalComparisonAnnotation)
    (baseLabel obstructionLabel frameworkLabel resolutionLabel reimportLabel : String)
    (E : ExternalClassicalComparisonObject) :
    GroundedHistoricalComparisonObject where
  annotation := annotation
  concrete := {
    profile := E.profile
    baseSystemLabel := baseLabel
    obstructionLabel := obstructionLabel
    blockedLabel := obstructionLabel
    strongerFrameworkLabel := frameworkLabel
    resolutionLabel := resolutionLabel
    licensedReimportLabel := reimportLabel
  }
  realization := by
    rcases (realizesSixStepShape_iff_stagewise E.profile.shape).1
      (compatibleWithDp_realizesSixStep E.profile E.compatible) with ⟨hR⟩
    exact hR
  comparison := {
    sameFamily := by simpa [dpAsClassicalAscentProfile] using E.compatible.2
    sameShape := by simpa [dpAsClassicalAscentProfile] using E.compatible.1
  }

/-- Convert a stronger formal external classical comparison object into the
grounded historical comparison interface by forgetting only the typed semantic
carriers. -/
def FormalExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    (annotation : HistoricalComparisonAnnotation)
    (resolutionLabel : String)
    (E : FormalExternalClassicalComparisonObject) :
    GroundedHistoricalComparisonObject :=
  ExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    annotation
    E.baseSemantics.label
    E.obstructionSemantics.label
    E.frameworkSemantics.label
    resolutionLabel
    E.reimportSemantics.label
    E.toExternalClassicalComparisonObject

/-- The grounded comparison object recovered from a formal external comparison
object is theorem-backed uniformly. -/
theorem FormalExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject_supported
    (annotation : HistoricalComparisonAnnotation)
    (resolutionLabel : String)
    (E : FormalExternalClassicalComparisonObject) :
    let G := FormalExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
      annotation resolutionLabel E
    RealizesSixStepShape G.concrete.profile.shape
      ∧ G.concrete.profile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent G.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  let G := FormalExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    annotation resolutionLabel E
  refine ⟨?_, G.comparison.sameFamily, G.comparison.sameShape⟩
  exact (realizesSixStepShape_iff_stagewise G.concrete.profile.shape).2 ⟨G.realization⟩

/-- Structural-identity comparison preserves six-step realization from left to
right. -/
theorem ComparisonWitness.right_realizes
    {left right : AscentProfile}
    (C : ComparisonWitness left right)
    (hLeft : RealizesSixStepShape left.shape) :
    RealizesSixStepShape right.shape :=
  C.sameShape.preserves_realization hLeft

/-- And symmetrically from right to left. -/
theorem ComparisonWitness.left_realizes
    {left right : AscentProfile}
    (C : ComparisonWitness left right)
    (hRight : RealizesSixStepShape right.shape) :
    RealizesSixStepShape left.shape := by
  apply C.sameShape.symm.preserves_realization
  exact hRight

/-- Any comparison-ready reflection profile compatible with the DP profile has
an explicit structural-identity comparison against the mechanized DP ascent
profile. -/
def comparisonAgainstDp
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    ComparisonWitness C dpAsClassicalAscentProfile where
  sameFamily := by simpa [dpAsClassicalAscentProfile] using hC.2
  sameShape := by simpa [dpAsClassicalAscentProfile] using hC.1

/-- Main reusable comparison theorem: any future classical reflection profile
that matches the DP stagewise shape is structurally identical to the mechanized
DP profile at the level of the six-step comparison schema. -/
theorem compatible_profile_has_dp_structural_identity
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    RealizesSixStepShape C.shape
      ∧ C.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent C.shape dpAsClassicalAscentProfile.shape := by
  refine ⟨compatibleWithDp_realizesSixStep C hC, ?_, ?_⟩
  · simpa [dpAsClassicalAscentProfile] using hC.2
  · simpa [dpAsClassicalAscentProfile] using hC.1

/-- The mechanized DP profile is structurally identical to itself in the new
comparison sense. -/
def dpStructuralIdentitySelfComparison :
    ComparisonWitness dpAsClassicalAscentProfile dpAsClassicalAscentProfile where
  sameFamily := rfl
  sameShape := by intro s; rfl

/-- Concrete comparison witness instantiating the right-hand profile with the
named paper-facing Gödel-side object. -/
def godel1931PaperComparisonAgainstDp :
    ComparisonWitness godel1931PaperAscentProfile dpAsClassicalAscentProfile :=
  comparisonAgainstDp godel1931PaperAscentProfile
    godel1931PaperAscentProfile_compatible

/-- Concrete theorem-backed structural identity for the named paper-facing
Gödel-side comparison object. -/
theorem godel1931Paper_has_dp_structural_identity :
    RealizesSixStepShape godel1931PaperAscentProfile.shape
      ∧ godel1931PaperAscentProfile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent godel1931PaperAscentProfile.shape
          dpAsClassicalAscentProfile.shape := by
  exact compatible_profile_has_dp_structural_identity
    godel1931PaperAscentProfile godel1931PaperAscentProfile_compatible

/-- Concrete comparison witness instantiating the right-hand profile with the
benchmark conservative-extension transport object. -/
def benchmarkTransportComparisonAgainstDp :
    ComparisonWitness benchmarkTransportAscentProfile dpAsClassicalAscentProfile :=
  comparisonAgainstDp benchmarkTransportAscentProfile
    benchmarkTransportAscentProfile_compatible

/-- Concrete theorem-backed structural identity for the benchmark transport
comparison profile. This is the direct link from the conservative-extension
layer to the six-step comparison layer. -/
theorem benchmarkTransport_has_dp_structural_identity :
    RealizesSixStepShape benchmarkTransportAscentProfile.shape
      ∧ benchmarkTransportAscentProfile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent benchmarkTransportAscentProfile.shape
          dpAsClassicalAscentProfile.shape := by
  exact compatible_profile_has_dp_structural_identity
    benchmarkTransportAscentProfile benchmarkTransportAscentProfile_compatible

/-- Any packaged concrete comparison object inherits a theorem-backed
structural-identity statement against the mechanized DP profile. -/
theorem HistoricalComparisonObject.supported
    (H : HistoricalComparisonObject) :
    RealizesSixStepShape H.concrete.profile.shape
      ∧ H.concrete.profile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent H.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  refine ⟨H.comparison.left_realizes structural_identity, ?_, ?_⟩
  · exact H.comparison.sameFamily
  · exact H.comparison.sameShape

/-- Any grounded historical comparison object is theorem-backed both as a
six-step realization and as a structural comparison against the mechanized DP
profile. -/
theorem GroundedHistoricalComparisonObject.supported
    (H : GroundedHistoricalComparisonObject) :
    RealizesSixStepShape H.concrete.profile.shape
      ∧ H.concrete.profile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent H.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  refine ⟨?_, H.comparison.sameFamily, H.comparison.sameShape⟩
  exact (realizesSixStepShape_iff_stagewise H.concrete.profile.shape).2 ⟨H.realization⟩

/-- Forget the explicit theorem witness and recover the lighter historical
comparison object. -/
def GroundedHistoricalComparisonObject.toHistoricalComparisonObject
    (H : GroundedHistoricalComparisonObject) :
    HistoricalComparisonObject where
  concrete := H.concrete
  comparison := H.comparison

/-- Forget the explicit theorem witness and recover the lighter annotated
historical comparison object. -/
def GroundedHistoricalComparisonObject.toAnnotatedHistoricalComparisonObject
    (H : GroundedHistoricalComparisonObject) :
    AnnotatedHistoricalComparisonObject where
  annotation := H.annotation
  historical := H.toHistoricalComparisonObject

/-- Packaged paper-facing Gödel-side comparison object. -/
def godel1931HistoricalComparisonObject : HistoricalComparisonObject where
  concrete := godel1931PaperComparison
  comparison := godel1931PaperComparisonAgainstDp

/-- Packaged benchmark-transport comparison object. -/
def benchmarkTransportHistoricalComparisonObject : HistoricalComparisonObject where
  concrete := benchmarkTransportComparison
  comparison := benchmarkTransportComparisonAgainstDp

/-- Theorem-bearing Gödel-side historical comparison object. -/
def godel1931GroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject where
  annotation := godel1931HistoricalAnnotation
  concrete := godel1931PaperComparison
  realization := by
    rcases
      (realizesSixStepShape_iff_stagewise godel1931PaperAscentProfile.shape).1
        godel1931PaperAscentProfile_realizesSixStep with
      ⟨hR⟩
    exact hR
  comparison := godel1931PaperComparisonAgainstDp

/-- The richer external Gödel-side comparison object induces the grounded
historical comparison interface. -/
def godel1931ExternalGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject :=
  ExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    godel1931HistoricalAnnotation
    godel1931BaseTheoryProfile.label
    godel1931ObstructionWitness.label
    godel1931StrongerFrameworkOperator.label
    "truth proved at the stronger level"
    godel1931ReimportMap.label
    godel1931ExternalClassicalComparisonObject

/-- The stronger formal Gödel-side external comparison object also recovers the
grounded historical comparison interface. -/
def godel1931FormalGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject :=
  FormalExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    godel1931HistoricalAnnotation
    "truth proved at the stronger level"
    godel1931FormalExternalClassicalComparisonObject

/-- Richer base-theory profile for the benchmark transport comparison. -/
def benchmarkTransportBaseTheoryProfile : HistoricalBaseTheoryProfile where
  label := "benchmark contract over KO7"
  registerApprox? := some FormalTheory.RCA0_WO_omega3
  hasBaseSystem := True

/-- Richer obstruction witness for the benchmark transport comparison. -/
def benchmarkTransportObstructionWitness : HistoricalObstructionWitness where
  label := "no direct whole-term witness"
  hasSelfObstruction := True
  blockedInBase := ¬ OperatorKO7.WitnessOrder.HasWitness
    OperatorKO7.WitnessOrder.ko7Tower
    OperatorKO7.WitnessOrder.WLevel.directWhole

/-- Richer stronger-framework operator for the benchmark transport comparison. -/
def benchmarkTransportFrameworkOperator : HistoricalFrameworkOperator where
  label := "conservative importedWhole → transformedCall transport"
  frameworkAvailable := Nonempty
    (ConservativeExtension
      (OperatorKO7.WitnessOrder.contractTower
        OperatorKO7.WitnessOrder.ko7Tower
        OperatorKO7.WitnessOrder.benchmarkContract)
      importedWholeLanguage transformedCallLanguage)
  resolvesInFramework :=
    OperatorKO7.WitnessOrder.kappaLe
      (OperatorKO7.WitnessOrder.contractTower
        OperatorKO7.WitnessOrder.ko7Tower
        OperatorKO7.WitnessOrder.benchmarkContract)
      OperatorKO7.WitnessOrder.WLevel.transformedCall

/-- Richer reimport map for the benchmark transport comparison. -/
def benchmarkTransportReimportMap : HistoricalReimportMap where
  label := "transported transformed-call admission"
  licensedReimport :=
    OperatorKO7.WitnessOrder.kappaLe
      (OperatorKO7.WitnessOrder.contractTower
        OperatorKO7.WitnessOrder.ko7Tower
        OperatorKO7.WitnessOrder.benchmarkContract)
      OperatorKO7.WitnessOrder.WLevel.transformedCall

/-- Typed base-theory semantics for the benchmark transport comparison. -/
def benchmarkTransportFormalBaseTheory : FormalHistoricalBaseTheory where
  label := "benchmark contract over KO7"
  registerApprox? := some FormalTheory.RCA0_WO_omega3
  Sentence := Unit
  provesBaseSystem _ := True
  witness := ()
  witness_provesBaseSystem := trivial

/-- Semantic sentence layer for the benchmark transport comparison. -/
inductive BenchmarkTransportSentenceSemantic
  | benchmarkBaseSentence
  | transformedWitnessSentence
  deriving DecidableEq, Repr

/-- Semantic stronger-framework tag for the benchmark transport comparison. -/
inductive BenchmarkTransportFrameworkSemantic
  | transformedCallTransport
  deriving DecidableEq, Repr

/-- Deeper base-theory semantics for the benchmark transport comparison. -/
def benchmarkTransportBaseTheoryContent : FormalBaseTheorySemantics where
  Sentence := BenchmarkTransportSentenceSemantic
  proves
    | .benchmarkBaseSentence => True
    | .transformedWitnessSentence => False
  trueInReferenceModel _ := True
  baseSentence := .benchmarkBaseSentence
  baseSentence_proves := trivial

/-- Deeper reflection/transport semantics for the benchmark transport
comparison. -/
def benchmarkTransportReflectionContent :
    FormalReflectionOperatorSemantics benchmarkTransportBaseTheoryContent where
  Framework := BenchmarkTransportFrameworkSemantic
  extendsBase _ := True
  reflects _ s := s = .transformedWitnessSentence
  licensedAdmission s := s = .transformedWitnessSentence
  blockedSentence := .transformedWitnessSentence
  blocked_not_provable := by
    simp [benchmarkTransportBaseTheoryContent, FormalBaseTheorySemantics.proves]
  blocked_true := by
    simp [benchmarkTransportBaseTheoryContent, FormalBaseTheorySemantics.trueInReferenceModel]
  strongerFramework := .transformedCallTransport
  stronger_extendsBase := trivial
  stronger_reflects_blocked := rfl
  blocked_licensedAdmission := rfl

/-- Typed obstruction semantics for the benchmark transport comparison.
The witness carrier is the full benchmark-side semantic sentence space
`BenchmarkTransportSentenceSemantic`, so that the downstream boundary
witness space is non-singleton and the direct benchmark↔DP boundary
correspondence can be genuinely non-constant. Only the designated
witness (`.transformedWitnessSentence`) carries the theorem load;
non-designated witnesses are structurally present without faking extra
mathematics. -/
def benchmarkTransportFormalObstruction : FormalHistoricalObstruction where
  label := "no direct whole-term witness"
  Witness := BenchmarkTransportSentenceSemantic
  isSelfObstruction _ := True
  blocksBase _ := ¬ OperatorKO7.WitnessOrder.HasWitness
    OperatorKO7.WitnessOrder.ko7Tower
    OperatorKO7.WitnessOrder.WLevel.directWhole
  witness := .transformedWitnessSentence
  witness_isSelfObstruction := trivial
  witness_blocksBase := OperatorKO7.WitnessOrder.ko7_no_directWhole_witness

/-- Deeper obstruction semantics for the benchmark transport comparison,
with witness carrier upgraded to the typed sentence space. The
obstruction relation is the identification witness-equals-blocked-sentence
on the typed sentence space, and the `blockedBy` projection is the
identity map on sentences. -/
def benchmarkTransportObstructionContent :
    FormalObstructionSemantics benchmarkTransportBaseTheoryContent where
  Witness := BenchmarkTransportSentenceSemantic
  obstructs w s := s = w
  selfReferential _ := True
  blockedBy := id
  witness := .transformedWitnessSentence
  witness_selfReferential := trivial
  witness_obstructs_blocked := rfl
  blocked_not_provable := by
    intro h
    simp [benchmarkTransportBaseTheoryContent,
      FormalBaseTheorySemantics.proves] at h
  blocked_true := by
    simp [benchmarkTransportBaseTheoryContent,
      FormalBaseTheorySemantics.trueInReferenceModel]

/-- Typed stronger-framework semantics for the benchmark transport comparison. -/
def benchmarkTransportFormalFramework : FormalHistoricalFramework where
  label := "conservative importedWhole → transformedCall transport"
  Framework :=
    { _u : Unit //
      ConservativeExtension
        (OperatorKO7.WitnessOrder.contractTower
          OperatorKO7.WitnessOrder.ko7Tower
          OperatorKO7.WitnessOrder.benchmarkContract)
        importedWholeLanguage transformedCallLanguage }
  resolves _ :=
    OperatorKO7.WitnessOrder.kappaLe
      (OperatorKO7.WitnessOrder.contractTower
        OperatorKO7.WitnessOrder.ko7Tower
        OperatorKO7.WitnessOrder.benchmarkContract)
      OperatorKO7.WitnessOrder.WLevel.transformedCall
  availableWitness := ⟨(), benchmarkContractProjectionExtension⟩
  resolver := ⟨(), benchmarkContractProjectionExtension⟩
  resolver_resolves := OperatorKO7.WitnessOrder.ko7_kappaContract_le_transformedCall

/-- Typed reimport semantics for the benchmark transport comparison.
The admission carrier is the full benchmark-side semantic sentence
space, matching the obstruction content, so that the annotation
functor's `annotate` map can be the identity on sentences (rather than
a constant landing on the imported sentence). -/
def benchmarkTransportFormalReimport : FormalHistoricalReimport where
  label := "transported transformed-call admission"
  Admission := BenchmarkTransportSentenceSemantic
  certified _ :=
    OperatorKO7.WitnessOrder.kappaLe
      (OperatorKO7.WitnessOrder.contractTower
      OperatorKO7.WitnessOrder.ko7Tower
      OperatorKO7.WitnessOrder.benchmarkContract)
    OperatorKO7.WitnessOrder.WLevel.transformedCall
  witness := .transformedWitnessSentence
  witness_certified := OperatorKO7.WitnessOrder.ko7_kappaContract_le_transformedCall

/-- Deeper semantic reimport layer for the benchmark transport
comparison, with admission carrier upgraded to the typed sentence
space. The certification relation is `a = s` on sentences. -/
def benchmarkTransportReimportContent :
    FormalReimportSemantics benchmarkTransportBaseTheoryContent where
  Admission := BenchmarkTransportSentenceSemantic
  certifies a s := a = s
  importedSentence := .transformedWitnessSentence
  witness := .transformedWitnessSentence
  witness_certifies_imported := rfl
  imported_true := by
    simp [benchmarkTransportBaseTheoryContent,
      FormalBaseTheorySemantics.trueInReferenceModel]

/-- Semantic coherence for the staged benchmark-side transfer:
obstruction -> transformed-call reflection -> transported reimport.
The coherence equalities are `rfl` on the typed sentence space because
the obstruction's designated witness, reflection's blocked sentence,
and reimport's imported sentence all equal `.transformedWitnessSentence`
after the witness-carrier upgrade. -/
def benchmarkTransportSemanticCoherence :
    FormalSemanticCoherence
      benchmarkTransportObstructionContent
      benchmarkTransportReflectionContent
      benchmarkTransportReimportContent where
  obstruction_blocked_eq_reflection_blocked := rfl
  reflection_blocked_eq_reimported := rfl
  reflection_covers_obstruction := rfl
  reimport_certifies_reflection_blocked := rfl

/-- Stronger formal external classical comparison object for the benchmark
transport layer. -/
def benchmarkTransportFormalExternalClassicalComparisonObject :
    FormalExternalClassicalComparisonObject where
  baseSemantics := benchmarkTransportFormalBaseTheory
  obstructionSemantics := benchmarkTransportFormalObstruction
  frameworkSemantics := benchmarkTransportFormalFramework
  reimportSemantics := benchmarkTransportFormalReimport
  baseTheoryContent := benchmarkTransportBaseTheoryContent
  obstructionContent := benchmarkTransportObstructionContent
  reflectionContent := benchmarkTransportReflectionContent
  reimportContent := benchmarkTransportReimportContent
  semanticCoherence := benchmarkTransportSemanticCoherence
  family := AscentFamily.reflection
  profile := {
    shape := {
      hasBaseSystem := benchmarkTransportFormalBaseTheory.hasBaseSystem
      hasSelfObstruction := benchmarkTransportFormalObstruction.hasSelfObstruction
      blockedInBase := benchmarkTransportFormalObstruction.blockedInBase
      hasStrongerFramework := benchmarkTransportFormalFramework.frameworkAvailable
      resolvedInFramework := benchmarkTransportFormalFramework.resolvesInFramework
      licensedReimport := benchmarkTransportFormalReimport.licensedReimport
    }
    family := AscentFamily.reflection
  }
  profileShape := rfl
  profileFamily := rfl
  compatible := by
    rcases OperatorKO7.ProofTheoreticRegister.structural_identity with
      ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
    refine ⟨?_, rfl⟩
    intro s
    cases s with
    | baseSystem =>
        exact ⟨fun _ => hBase,
          fun _ => benchmarkTransportFormalBaseTheory.realizesBaseSystem⟩
    | selfObstruction =>
        exact ⟨fun _ => hSelf,
          fun _ => benchmarkTransportFormalObstruction.realizesSelfObstruction⟩
    | blockedInBase =>
        exact ⟨fun _ => hBlocked,
          fun _ => benchmarkTransportFormalObstruction.realizesBlockedInBase⟩
    | strongerFramework =>
        exact ⟨fun _ => hStronger,
          fun _ => benchmarkTransportFormalFramework.realizesAvailability⟩
    | resolvedInFramework =>
        exact ⟨fun _ => hResolved,
          fun _ => benchmarkTransportFormalFramework.realizesResolution⟩
    | licensedReimport =>
        exact ⟨fun _ => hLicensed,
          fun _ => benchmarkTransportFormalReimport.realizesLicensedReimport⟩

/-- The stronger formal benchmark-side external comparison object is
theorem-backed at the profile level. -/
theorem benchmarkTransportFormalExternalClassicalComparison_supported :
    RealizesSixStepShape benchmarkTransportFormalExternalClassicalComparisonObject.profile.shape
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.profile.family =
          AscentFamily.reflection
      ∧ StagewiseEquivalent
          benchmarkTransportFormalExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportFormalExternalClassicalComparisonObject.supported

/-- The stronger benchmark-side formal comparison object also has theorem-backed
base-theory and reflection semantics. -/
theorem benchmarkTransportFormalExternalClassicalComparison_semanticSupported :
    benchmarkTransportFormalExternalClassicalComparisonObject.baseTheoryContent.hasInternalProofLayer
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.obstructionContent.hasSemanticObstruction
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.reflectionContent.hasBlockedSemanticSentence
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.reflectionContent.resolvesBlockedSemantically
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.reflectionContent.hasLicensedAdmission
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport := by
  exact benchmarkTransportFormalExternalClassicalComparisonObject.semanticSupported

/-- The stronger benchmark-side formal comparison object also has theorem-backed
obstruction-to-reflection and reflection-to-reimport transfer. -/
theorem benchmarkTransportFormalExternalClassicalComparison_transferSupported :
    benchmarkTransportFormalExternalClassicalComparisonObject.semanticCoherence.obstructionTransfersToReflection
      ∧ benchmarkTransportFormalExternalClassicalComparisonObject.semanticCoherence.reflectionTransfersToReimport := by
  exact benchmarkTransportFormalExternalClassicalComparisonObject.semanticTransferSupported

/-- Richer external classical comparison object for the benchmark transport
layer. -/
def benchmarkTransportExternalClassicalComparisonObject :
    ExternalClassicalComparisonObject :=
  benchmarkTransportFormalExternalClassicalComparisonObject.toExternalClassicalComparisonObject

/-- Theorem-bearing benchmark-transport historical comparison object. -/
def benchmarkTransportGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject where
  annotation := benchmarkTransportHistoricalAnnotation
  concrete := benchmarkTransportComparison
  realization := by
    rcases
      (realizesSixStepShape_iff_stagewise benchmarkTransportAscentProfile.shape).1
        benchmarkTransportAscentProfile_realizesSixStep with
      ⟨hR⟩
    exact hR
  comparison := benchmarkTransportComparisonAgainstDp

/-- The richer external benchmark-transport comparison object induces the
grounded historical comparison interface. -/
def benchmarkTransportExternalGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject :=
  ExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    benchmarkTransportHistoricalAnnotation
    benchmarkTransportBaseTheoryProfile.label
    benchmarkTransportObstructionWitness.label
    benchmarkTransportFrameworkOperator.label
    "first admissible witness at transformed-call"
    benchmarkTransportReimportMap.label
    benchmarkTransportExternalClassicalComparisonObject

/-- The stronger formal benchmark-side external comparison object also recovers
the grounded historical comparison interface. -/
def benchmarkTransportFormalGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject :=
  FormalExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    benchmarkTransportHistoricalAnnotation
    "first admissible witness at transformed-call"
    benchmarkTransportFormalExternalClassicalComparisonObject

/-- Typed Gödel-side historical comparison object. -/
def godel1931AnnotatedHistoricalComparisonObject :
    AnnotatedHistoricalComparisonObject where
  annotation := godel1931HistoricalAnnotation
  historical := godel1931HistoricalComparisonObject

/-- Typed benchmark-transport historical comparison object. -/
def benchmarkTransportAnnotatedHistoricalComparisonObject :
    AnnotatedHistoricalComparisonObject where
  annotation := benchmarkTransportHistoricalAnnotation
  historical := benchmarkTransportHistoricalComparisonObject

/-- Supported form of the paper-facing Gödel-side comparison object. -/
theorem godel1931HistoricalComparison_supported :
    RealizesSixStepShape godel1931HistoricalComparisonObject.concrete.profile.shape
      ∧ godel1931HistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931HistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931HistoricalComparisonObject.supported

/-- Supported form of the benchmark-transport comparison object. -/
theorem benchmarkTransportHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportHistoricalComparisonObject.concrete.profile.shape
      ∧ benchmarkTransportHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportHistoricalComparisonObject.supported

/-- Supported form of the theorem-bearing Gödel-side historical comparison
object. -/
theorem godel1931GroundedHistoricalComparison_supported :
    RealizesSixStepShape
        godel1931GroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ godel1931GroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931GroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931GroundedHistoricalComparisonObject.supported

/-- Supported form of the richer external Gödel-side comparison object. -/
theorem godel1931ExternalClassicalComparison_supported :
    RealizesSixStepShape godel1931ExternalClassicalComparisonObject.profile.shape
      ∧ godel1931ExternalClassicalComparisonObject.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent godel1931ExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931ExternalClassicalComparisonObject.supported

/-- The richer external Gödel-side object recovers the grounded interface. -/
theorem godel1931ExternalGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        godel1931ExternalGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ godel1931ExternalGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931ExternalGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931ExternalGroundedHistoricalComparisonObject.supported

/-- The stronger formal Gödel-side external object recovers the grounded
interface theoremically. -/
theorem godel1931FormalGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        godel1931FormalGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ godel1931FormalGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931FormalGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931FormalGroundedHistoricalComparisonObject.supported

/-- Supported form of the theorem-bearing benchmark-transport historical
comparison object. -/
theorem benchmarkTransportGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ benchmarkTransportGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportGroundedHistoricalComparisonObject.supported

/-- Supported form of the richer external benchmark-transport comparison
object. -/
theorem benchmarkTransportExternalClassicalComparison_supported :
    RealizesSixStepShape benchmarkTransportExternalClassicalComparisonObject.profile.shape
      ∧ benchmarkTransportExternalClassicalComparisonObject.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportExternalClassicalComparisonObject.supported

/-- The richer external benchmark-transport object recovers the grounded
interface. -/
theorem benchmarkTransportExternalGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportExternalGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ benchmarkTransportExternalGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportExternalGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportExternalGroundedHistoricalComparisonObject.supported

/-- The stronger formal benchmark-side external object recovers the grounded
interface theoremically. -/
theorem benchmarkTransportFormalGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportFormalGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ benchmarkTransportFormalGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportFormalGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportFormalGroundedHistoricalComparisonObject.supported

/-- Typed Gödel-side historical comparison object remains theorem-backed. -/
theorem godel1931AnnotatedHistoricalComparison_supported :
    RealizesSixStepShape
        godel1931AnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
      ∧ godel1931AnnotatedHistoricalComparisonObject.historical.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931AnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931AnnotatedHistoricalComparisonObject.historical.supported

/-- Typed benchmark-transport historical comparison object remains
theorem-backed. -/
theorem benchmarkTransportAnnotatedHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportAnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
      ∧ benchmarkTransportAnnotatedHistoricalComparisonObject.historical.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportAnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportAnnotatedHistoricalComparisonObject.historical.supported

end OperatorKO7.StructuralIdentityComparison
