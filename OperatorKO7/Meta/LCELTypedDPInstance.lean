import OperatorKO7.Meta.LCELAnnotatedReimport
import OperatorKO7.Meta.LCELFactorization
import OperatorKO7.Meta.WitnessOrder

set_option autoImplicit false

/-!
# Typed LCEL instance for the KO7 dependency-pair route

This module contains actual sentence and derivation objects.  The base layer has
a transformed-call certificate but no direct derivation of source termination.
The extension layer combines that certificate with a proof-valued transport
license.  Reimport preserves both pieces in the licensed constructor and cannot
erase to a plain base derivation.

The active concrete transport consumes the pair certificate by using the
actual DP countdown embedding to supply well-founded induction for the
polynomial source-step rank.  This is a fixed-KO7 composite proof, not the
generic Arts-Giesl dependency-pair processor theorem: source transport still
uses the independently checked theorem that the KO7 polynomial interpretation
strictly decreases on every root step.  The old constant-map inhabitant remains
only as an explicitly named compatibility fixture.
-/

namespace OperatorKO7.Meta.LCELDPInstance

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Meta.LCELTypedDerivations
open OperatorKO7.Meta.LCELAnnotatedReimport
open OperatorKO7.Meta.LCELFactorization

/-- The two typed propositions used by the concrete DP layer crossing. -/
inductive DPSentence where
| sourceTermination
| transformedCallTermination
deriving DecidableEq, Repr

/-- Proof object for well-foundedness of the concrete extracted pair problem. -/
structure TransformedCallCertificate : Type where
  pairWellFounded : WellFounded DPPairRev

/-- Proof-valued license for this one named KO7 pair relation and this one
named KO7 source relation.  This type is not a generic dependency-pair
processor soundness interface. -/
structure KO7FixedSystemLicense : Type where
  lift : WellFounded DPPairRev ->
    WellFounded (fun a b : Trace => Step b a)

/-- Extension proof of source termination retains both the transformed
certificate and the license used to transport it. -/
structure LicensedSourceTermination : Type where
  certificate : TransformedCallCertificate
  license : KO7FixedSystemLicense

/-- Base derivations: no source-termination object, but a real pair certificate. -/
def dpBaseDerivation : DPSentence -> Type
| .sourceTermination => Empty
| .transformedCallTermination => TransformedCallCertificate

/-- Extension derivations add the proof-carrying licensed source result. -/
def dpExtensionDerivation : DPSentence -> Type
| .sourceTermination => LicensedSourceTermination
| .transformedCallTermination => TransformedCallCertificate

def dpBaseTheory : TypedTheory where
  Sentence := DPSentence
  Derivation := dpBaseDerivation

def dpExtensionTheory : TypedTheory where
  Sentence := DPSentence
  Derivation := dpExtensionDerivation

/-- The base-to-extension embedding maps actual derivation objects and does not
manufacture a source derivation from the empty base type. -/
def dpTheoryExtension : TheoryExtension dpBaseTheory dpExtensionTheory where
  onSentence := id
  sentence_injective := by
    intro left right h
    exact h
  onDerivation := by
    intro phi d
    cases phi with
    | sourceTermination => exact Empty.elim d
    | transformedCallTermination => exact d
  derivation_injective := by
    intro phi left right h
    cases phi with
    | sourceTermination => exact Empty.elim left
    | transformedCallTermination => exact h

/-- The concrete sentence map is genuinely injective. -/
theorem dpTheoryExtension_sentence_injective :
    Function.Injective dpTheoryExtension.onSentence :=
  dpTheoryExtension.sentence_injective

/-- The concrete derivation map is genuinely injective in every sentence
fiber. -/
theorem dpTheoryExtension_derivation_injective
    {phi : dpBaseTheory.Sentence}
    {left right : dpBaseTheory.Derivation phi}
    (h : dpTheoryExtension.onDerivation left =
      dpTheoryExtension.onDerivation right) :
    left = right :=
  dpTheoryExtension.derivation_injective h

/-- Actual certificate for the manually extracted KO7 dependency-pair relation. -/
def ko7TransformedCallCertificate : TransformedCallCertificate where
  pairWellFounded := ko7_has_transformedCall_witness

/-- Legacy fixed-system constant-map fixture supplied by the independently
proved KO7 source well-foundedness theorem.  Its input is intentionally unused.
It remains for compatibility and is not used by the active licensed reimport. -/
def ko7ConstantLicenseFixture : KO7FixedSystemLicense where
  lift := fun _ => ko7_has_importedWhole_witness_poly

/-- Fixed-system source transport in which the supplied DP certificate provides
the well-founded natural countdown used by the polynomial source ranking.

Relation: actual `DPPairRev` certificate to the actual full KO7 root `Step`.
Property: strong normalization / well-founded reverse relation.
Does not prove: generic dependency-pair processor soundness. -/
theorem ko7SourceWellFounded_of_pairCertificate
    (hPair : WellFounded DPPairRev) :
    WellFounded (fun a b : Trace => Step b a) := by
  have hNat : WellFounded (fun m n : Nat => m < n) :=
    natLt_wellFounded_of_DPPairRev hPair
  have hPolynomialRank : WellFounded
      (fun a b : Trace =>
        OperatorKO7.PolyInterpretation.W a <
          OperatorKO7.PolyInterpretation.W b) :=
    InvImage.wf (f := OperatorKO7.PolyInterpretation.W) hNat
  exact Subrelation.wf
    (fun hStep => OperatorKO7.PolyInterpretation.W_orients_step hStep)
    hPolynomialRank

/-- Active proof-valued fixed-system license.  Unlike the compatibility
fixture, its proof term routes the supplied pair certificate through
`natLt_wellFounded_of_DPPairRev` before constructing source accessibility. -/
def ko7DPCertificateConsumingLicense : KO7FixedSystemLicense where
  lift := ko7SourceWellFounded_of_pairCertificate

/-- Licensed extension derivation of the concrete source-termination sentence;
the retained license is the certificate-consuming fixed-system construction. -/
def ko7LicensedSourceTermination : LicensedSourceTermination where
  certificate := ko7TransformedCallCertificate
  license := ko7DPCertificateConsumingLicense

/-- Compatibility receipt for the legacy constant fixture. -/
theorem ko7ConstantLicenseFixture_yields_sourceWellFounded :
    WellFounded (fun a b : Trace => Step b a) :=
  ko7ConstantLicenseFixture.lift
    ko7TransformedCallCertificate.pairWellFounded

/-- The active licensed derivation applies its retained license to its retained
pair certificate and yields source well-foundedness. -/
theorem ko7DPCertificateConsumingLicense_yields_sourceWellFounded :
    WellFounded (fun a b : Trace => Step b a) :=
  ko7LicensedSourceTermination.license.lift
    ko7LicensedSourceTermination.certificate.pairWellFounded

/-- Source termination is a boundary sentence of the typed base layer. -/
theorem sourceTermination_is_boundary :
    BoundarySentence dpBaseTheory DPSentence.sourceTermination := by
  intro h
  obtain ⟨d⟩ := h
  exact Empty.elim d

/-! ## Exact bridge to the concrete factorization observables -/

/-- Observation proxy from the typed DP sentence language to the concrete
two-observable language.  It maps the base certificate sentence to the
counter observation and the source sentence to the wrapper-sensitive
observation.  The theorems below state exactly what this proxy preserves and
where semantic transport fails. -/
def dpSentenceObservationProxy :
    DPSentence → KO7DPFactorizationSentence
  | .sourceTermination => .wrapperMultiplicityEven
  | .transformedCallTermination => .counterPositive

/-- Inverse of the two-sentence observation proxy. -/
def observationProxyToDPSentence :
    KO7DPFactorizationSentence → DPSentence
  | .counterPositive => .transformedCallTermination
  | .wrapperMultiplicityEven => .sourceTermination

@[simp] theorem observationProxyToDPSentence_leftInverse
    (sentence : DPSentence) :
    observationProxyToDPSentence (dpSentenceObservationProxy sentence) =
      sentence := by
  cases sentence <;> rfl

@[simp] theorem dpSentenceObservationProxy_rightInverse
    (sentence : KO7DPFactorizationSentence) :
    dpSentenceObservationProxy (observationProxyToDPSentence sentence) =
      sentence := by
  cases sentence <;> rfl

/-- The proxy is an exact equivalence of the two enumerated sentence
alphabets.  This is an alphabet equivalence, not yet a semantic equivalence. -/
def dpSentenceObservationEquiv :
    DPSentence ≃ KO7DPFactorizationSentence where
  toFun := dpSentenceObservationProxy
  invFun := observationProxyToDPSentence
  left_inv := observationProxyToDPSentence_leftInverse
  right_inv := dpSentenceObservationProxy_rightInverse

/-- The actual typed base-derivation judgment agrees exactly with the concrete
factorization model's base judgment through the observation proxy. -/
theorem dpBaseDerivable_iff_observationProxyProvesBase
    (sentence : DPSentence) :
    Nonempty (dpBaseTheory.Derivation sentence) ↔
      ko7DPFactorizationBoundaryModel.provesBase
        (dpSentenceObservationProxy sentence) := by
  cases sentence with
  | sourceTermination =>
      constructor
      · rintro ⟨derivation⟩
        exact Empty.elim derivation
      · intro h
        cases h
  | transformedCallTermination =>
      constructor
      · intro _
        rfl
      · intro _
        exact ⟨ko7TransformedCallCertificate⟩

/-- Actual global semantics for the two typed DP sentences.  Truth of source
termination and transformed-call termination is a proposition about the fixed
KO7 relations, so it does not vary with the comparison trace.  The coordinates
remain the actual `dpRank` and wrapper multiplicity in order to expose the
semantic mismatch with the observation proxy. -/
def ko7TypedDPSemanticBoundaryModel :
    FactorizationBoundaryModel DPSentence Trace Nat Nat where
  reference := ko7DPFactorizationReference
  piRev := dpRank
  piIrr := ko7WrapperMultiplicity
  trueIn := fun _ sentence =>
    match sentence with
    | .sourceTermination => WellFounded (fun a b : Trace => Step b a)
    | .transformedCallTermination => WellFounded DPPairRev
  provesBase := fun sentence => Nonempty (dpBaseTheory.Derivation sentence)

/-- Both fixed-system semantic sentences are true at every comparison trace.
The source case is obtained through the active certificate-consuming license. -/
theorem ko7TypedDPSemantic_true_everywhere
    (model : Trace) (sentence : DPSentence) :
    ko7TypedDPSemanticBoundaryModel.trueIn model sentence := by
  cases sentence with
  | sourceTermination =>
      exact ko7DPCertificateConsumingLicense_yields_sourceWellFounded
  | transformedCallTermination =>
      exact ko7TransformedCallCertificate.pairWellFounded

/-- At the chosen reference trace, the observation proxy and the actual global
semantics agree on both enumerated sentences. -/
theorem ko7TypedDPSemantic_reference_agrees_with_observationProxy
    (sentence : DPSentence) :
    ko7TypedDPSemanticBoundaryModel.trueIn
        ko7DPFactorizationReference sentence ↔
      ko7DPFactorizationBoundaryModel.trueIn
        ko7DPFactorizationReference
        (dpSentenceObservationProxy sentence) := by
  cases sentence with
  | sourceTermination =>
      constructor
      · intro _
        simp [ko7DPFactorizationBoundaryModel, ko7DPFactorizationReference,
          dpSentenceObservationProxy, ko7WrapperMultiplicity]
      · intro _
        exact ko7DPCertificateConsumingLicense_yields_sourceWellFounded
  | transformedCallTermination =>
      constructor
      · intro _
        simp [ko7DPFactorizationBoundaryModel, ko7DPFactorizationReference,
          dpSentenceObservationProxy, dpRank]
      · intro _
        exact ko7TransformedCallCertificate.pairWellFounded

/-- Global semantic transport through the observation proxy fails: source
termination remains true at the alternate trace, while its wrapper-parity
proxy is false there. -/
theorem ko7TypedDPSemantic_observationProxy_not_truthPreserving :
    ko7TypedDPSemanticBoundaryModel.trueIn
        ko7DPFactorizationAlternate DPSentence.sourceTermination ∧
      ¬ ko7DPFactorizationBoundaryModel.trueIn
        ko7DPFactorizationAlternate
        (dpSentenceObservationProxy DPSentence.sourceTermination) := by
  constructor
  · exact ko7DPCertificateConsumingLicense_yields_sourceWellFounded
  · simp [ko7DPFactorizationBoundaryModel, ko7DPFactorizationAlternate,
      dpSentenceObservationProxy, ko7WrapperMultiplicity]

/-- Truth of typed base-derived sentences factors through `dpRank`; in fact,
the fixed-system semantic propositions are independent of both trace
coordinates. -/
def ko7TypedDPBaseDerivationsFactorThroughRev :
    BaseDerivationsFactorThroughRev ko7TypedDPSemanticBoundaryModel where
  factorizedTruth := fun sentence _ =>
    match sentence with
    | .sourceTermination => WellFounded (fun a b : Trace => Step b a)
    | .transformedCallTermination => WellFounded DPPairRev
  factorization := by
    intro sentence _ model
    cases sentence <;> rfl

/-- With actual fixed-system semantics, source termination is genuinely
reference-true and genuinely absent from the typed base derivation layer. -/
theorem ko7TypedDP_sourceTermination_boundaryAdmissible :
    BoundaryAdmissible ko7TypedDPSemanticBoundaryModel
      DPSentence.sourceTermination :=
  ⟨ko7DPCertificateConsumingLicense_yields_sourceWellFounded,
    sourceTermination_is_boundary⟩

/-- No actual fixed-system semantic sentence is sensitive to the wrapper
coordinate, because both relation-level propositions are true independently
of the comparison trace. -/
theorem ko7TypedDPSemantic_not_piIrrSensitive
    (sentence : DPSentence) :
    ¬ PiIrrSensitiveAtReference ko7TypedDPSemanticBoundaryModel sentence := by
  rintro ⟨_, alternate, _, _, hFalse⟩
  exact hFalse (ko7TypedDPSemantic_true_everywhere alternate sentence)

/-- Consequently the abstract equality package from the proxy model cannot be
transported to actual typed DP semantics: its required completeness field is
refuted by the source-termination boundary witness. -/
theorem ko7TypedDPSemantic_no_extensionalFactorization :
    ¬ Nonempty (ExtensionalFactorization ko7TypedDPSemanticBoundaryModel) := by
  rintro ⟨hExtensional⟩
  exact ko7TypedDPSemantic_not_piIrrSensitive
    DPSentence.sourceTermination
    (hExtensional.boundary_complete DPSentence.sourceTermination
      ko7TypedDP_sourceTermination_boundaryAdmissible)

/-- Set equality between actual typed boundary sentences and wrapper-sensitive
sentences is therefore false. -/
theorem ko7TypedDP_boundaryAdmissible_set_ne_piIrrSensitive_set :
    {sentence : DPSentence |
        BoundaryAdmissible ko7TypedDPSemanticBoundaryModel sentence} ≠
      {sentence : DPSentence |
        PiIrrSensitiveAtReference ko7TypedDPSemanticBoundaryModel sentence} := by
  intro hSets
  have hAtSource := Set.ext_iff.mp hSets DPSentence.sourceTermination
  exact ko7TypedDPSemantic_not_piIrrSensitive
    DPSentence.sourceTermination
    (hAtSource.mp ko7TypedDP_sourceTermination_boundaryAdmissible)

/-- Concrete annotated reimport carrying the actual pair certificate and the
proof-valued fixed-system license. -/
def ko7AnnotatedSourceTermination :
    AnnotatedDerivation dpBaseTheory dpExtensionTheory dpTheoryExtension
      KO7FixedSystemLicense DPSentence.sourceTermination :=
  reimportAnnotated ko7DPCertificateConsumingLicense
    ko7LicensedSourceTermination

/-- The concrete licensed DP reimport cannot erase to an unannotated base proof. -/
theorem ko7AnnotatedSourceTermination_not_plain :
    eraseToBase? ko7AnnotatedSourceTermination = none :=
  boundary_annotation_erases_to_none sourceTermination_is_boundary
    ko7AnnotatedSourceTermination

/-- Sentence-indexed annotated derivations in the concrete DP instance. -/
abbrev DPAnnotatedState :=
  Sigma (fun phi : DPSentence =>
    AnnotatedDerivation dpBaseTheory dpExtensionTheory dpTheoryExtension
      KO7FixedSystemLicense phi)

/-- The transformed-call certificate reimported through the same explicit
certificate-consuming fixed-system license. -/
def ko7AnnotatedTransformedCall :
    AnnotatedDerivation dpBaseTheory dpExtensionTheory dpTheoryExtension
      KO7FixedSystemLicense DPSentence.transformedCallTermination :=
  reimportAnnotated ko7DPCertificateConsumingLicense
    ko7TransformedCallCertificate

/-- The actual licensed source-termination state. -/
def ko7LicensedSourceAnnotatedState : DPAnnotatedState :=
  ⟨DPSentence.sourceTermination, ko7AnnotatedSourceTermination⟩

/-- The actual licensed transformed-call state. -/
def ko7LicensedTransformedCallAnnotatedState : DPAnnotatedState :=
  ⟨DPSentence.transformedCallTermination, ko7AnnotatedTransformedCall⟩

/-- Coarse annotation observer: it retains only whether a derivation is base
or licensed and deliberately forgets the conclusion and licensed payload. -/
def dpAnnotationClass (state : DPAnnotatedState) : Bool :=
  match state.2 with
  | .base _ => false
  | .licensed _ _ => true

/-- The conclusion sentence retained by an annotated state. -/
def dpAnnotatedConclusion (state : DPAnnotatedState) : DPSentence :=
  state.1

/-- The two concrete licensed states collide under the coarse annotation
observer. -/
theorem ko7_licensedAnnotatedStates_same_class :
    dpAnnotationClass ko7LicensedSourceAnnotatedState =
      dpAnnotationClass ko7LicensedTransformedCallAnnotatedState :=
  rfl

/-- The same two licensed states have different typed conclusions. -/
theorem ko7_licensedAnnotatedStates_distinct_conclusion :
    dpAnnotatedConclusion ko7LicensedSourceAnnotatedState ≠
      dpAnnotatedConclusion ko7LicensedTransformedCallAnnotatedState := by
  intro h
  cases h

/-- Paper-facing typed DP instance of extensional boundary factorization: the
coarse annotation class does not determine the typed conclusion.  This is the
exact `FactorsThrough` failure witnessed by the two actual licensed reimports;
it makes no general dependency-pair soundness claim. -/
theorem ko7_typedDP_annotationClass_boundary :
    Boundary dpAnnotationClass dpAnnotatedConclusion := by
  intro hFactors
  exact ko7_licensedAnnotatedStates_distinct_conclusion
    (hFactors ko7_licensedAnnotatedStates_same_class)

/-- Compatibility reach name for the typed DP result.  Its conclusion is the
extensional factorization boundary itself, not a stored conjunction of desired
facts. -/
theorem ko7_typed_lcel_dp_package :
    Boundary dpAnnotationClass dpAnnotatedConclusion :=
  ko7_typedDP_annotationClass_boundary

section AuditChecks

#check @DPSentence
#check @TransformedCallCertificate
#check @KO7FixedSystemLicense
#check @LicensedSourceTermination
#check @dpTheoryExtension
#check @dpTheoryExtension_sentence_injective
#check @dpTheoryExtension_derivation_injective
#check @ko7TransformedCallCertificate
#check @ko7ConstantLicenseFixture
#check @ko7SourceWellFounded_of_pairCertificate
#check @ko7DPCertificateConsumingLicense
#check @ko7ConstantLicenseFixture_yields_sourceWellFounded
#check @ko7DPCertificateConsumingLicense_yields_sourceWellFounded
#check @sourceTermination_is_boundary
#check @dpSentenceObservationProxy
#check @dpSentenceObservationEquiv
#check @dpBaseDerivable_iff_observationProxyProvesBase
#check @ko7TypedDPSemanticBoundaryModel
#check @ko7TypedDPSemantic_true_everywhere
#check @ko7TypedDPSemantic_reference_agrees_with_observationProxy
#check @ko7TypedDPSemantic_observationProxy_not_truthPreserving
#check @ko7TypedDPBaseDerivationsFactorThroughRev
#check @ko7TypedDP_sourceTermination_boundaryAdmissible
#check @ko7TypedDPSemantic_not_piIrrSensitive
#check @ko7TypedDPSemantic_no_extensionalFactorization
#check @ko7TypedDP_boundaryAdmissible_set_ne_piIrrSensitive_set
#check @ko7AnnotatedSourceTermination
#check @ko7AnnotatedSourceTermination_not_plain
#check @ko7_typedDP_annotationClass_boundary
#check @ko7_typed_lcel_dp_package

#print axioms ko7ConstantLicenseFixture_yields_sourceWellFounded
#print axioms ko7SourceWellFounded_of_pairCertificate
#print axioms ko7DPCertificateConsumingLicense_yields_sourceWellFounded
#print axioms sourceTermination_is_boundary
#print axioms dpBaseDerivable_iff_observationProxyProvesBase
#print axioms ko7TypedDPSemantic_true_everywhere
#print axioms ko7TypedDPSemantic_reference_agrees_with_observationProxy
#print axioms ko7TypedDPSemantic_observationProxy_not_truthPreserving
#print axioms ko7TypedDPBaseDerivationsFactorThroughRev
#print axioms ko7TypedDP_sourceTermination_boundaryAdmissible
#print axioms ko7TypedDPSemantic_not_piIrrSensitive
#print axioms ko7TypedDPSemantic_no_extensionalFactorization
#print axioms ko7TypedDP_boundaryAdmissible_set_ne_piIrrSensitive_set
#print axioms ko7AnnotatedSourceTermination_not_plain
#print axioms ko7_typedDP_annotationClass_boundary
#print axioms ko7_typed_lcel_dp_package

end AuditChecks

end OperatorKO7.Meta.LCELDPInstance
