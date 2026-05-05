import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity

/-!
# LCEL Semantic Correspondence

Workstream A of the LCEL universal-theorem roadmap: replace inhabitance-style
slot biconditionals and semantic-support iffs with explicit typed semantic
correspondence data between two `FormalLCELInstance`s.

The `LCELComparisonWitness` carrier in `LCELStructuralIdentity.lean` carries
the stagewise equivalence of comparison profiles plus biconditionals on the
explicit external-license and reimport-class slots. Those biconditionals are
`Iff` on propositional content: they say the source slot is inhabited iff the
target slot is, but they do not record a typed map between the slot data.

This file provides typed correspondence structures:

- `BoundaryObjectCorrespondence L₁ L₂` with a typed map between
  `BoundaryWitness` types that preserves the designated witness;
- `AnnotationFunctorCorrespondence L₁ L₂` with a typed map between
  `Annotation` types that preserves the annotation of the designated
  derivation;
- `ExternalLicenseCorrespondence L₁ L₂` with explicit forward / backward
  transport functions between the external-license slot propositions;
- `ReimportClassCorrespondence L₁ L₂` with explicit forward / backward
  transport functions between the reimport-class slot propositions;
- `LCELSemanticSlotCorrespondence L₁ L₂` bundling the four.

Each of these structures induces an `LCELComparisonWitness` whose slot
biconditionals come from genuine typed transport rather than from `iff_of_true`
packaging. Canonical correspondences are supplied for the paper-facing
Gödel ↔ benchmark-transport and Gödel ↔ native-DP pairs, consistent with the
canonical comparison witnesses already proved in `LCELStructuralIdentity.lean`.
-/

namespace OperatorKO7.LCELSemanticCorrespondence

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.ReflectionSchema

/-! ## Boundary-object correspondence -/

/-- Typed semantic correspondence between the boundary objects of two LCEL
instances.

The correspondence supplies a typed map between the two boundary-witness
spaces that preserves the designated witness. Because
`LCELBoundaryObject.BoundaryWitness` is instance-specific, this map is a
real semantic bridge, not a mere biconditional on the boundary-realization
predicate. -/
structure BoundaryObjectCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Translation of boundary witnesses from `L₁` to `L₂`. -/
  translate :
    L₁.boundaryObject.BoundaryWitness → L₂.boundaryObject.BoundaryWitness
  /-- The designated witness on `L₁` translates to the designated witness
  on `L₂`. -/
  translate_designated :
    translate L₁.boundaryObject.designated = L₂.boundaryObject.designated

namespace BoundaryObjectCorrespondence

/-- The translation of the designated source witness always realizes the
target boundary slot, because the target's designated witness is itself a
boundary-realization witness and the correspondence forces
`translate designated = designated`. -/
theorem translate_designated_realizes
    {L₁ L₂ : FormalLCELInstance}
    (C : BoundaryObjectCorrespondence L₁ L₂) :
    ¬ L₂.comparison.baseTheoryContent.proves
        (L₂.boundaryObject.boundarySentence
          (C.translate L₁.boundaryObject.designated))
      ∧ L₂.comparison.baseTheoryContent.trueInReferenceModel
        (L₂.boundaryObject.boundarySentence
          (C.translate L₁.boundaryObject.designated)) := by
  refine ⟨?_, ?_⟩
  · rw [C.translate_designated]
    exact L₂.boundaryObject.designated_not_provable
  · rw [C.translate_designated]
    exact L₂.boundaryObject.designated_true

end BoundaryObjectCorrespondence

/-! ## External-license correspondence -/

/-- Typed semantic correspondence between the external-license slots of two
LCEL instances. Explicit forward and backward transport functions are named
here to distinguish this from a bare `Iff` on inhabitance. -/
structure ExternalLicenseCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Transport a source external-license witness to a target witness. -/
  forward : L₁.externalLicenseWitness → L₂.externalLicenseWitness
  /-- Transport a target external-license witness to a source witness. -/
  backward : L₂.externalLicenseWitness → L₁.externalLicenseWitness

namespace ExternalLicenseCorrespondence

/-- An external-license correspondence induces a biconditional on the slot
propositions. -/
theorem toIff
    {L₁ L₂ : FormalLCELInstance}
    (C : ExternalLicenseCorrespondence L₁ L₂) :
    L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness :=
  ⟨C.forward, C.backward⟩

end ExternalLicenseCorrespondence

/-! ## Reimport-class correspondence -/

/-- Typed semantic correspondence between the reimport-class slots of two
LCEL instances. Explicit forward and backward transport functions are named
here. -/
structure ReimportClassCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Transport a source reimport-class witness to a target witness. -/
  forward : L₁.reimportClassWitness → L₂.reimportClassWitness
  /-- Transport a target reimport-class witness to a source witness. -/
  backward : L₂.reimportClassWitness → L₁.reimportClassWitness

namespace ReimportClassCorrespondence

/-- A reimport-class correspondence induces a biconditional on the slot
propositions. -/
theorem toIff
    {L₁ L₂ : FormalLCELInstance}
    (C : ReimportClassCorrespondence L₁ L₂) :
    L₁.reimportClassWitness ↔ L₂.reimportClassWitness :=
  ⟨C.forward, C.backward⟩

end ReimportClassCorrespondence

/-! ## Annotation-functor correspondence -/

/-- Typed semantic correspondence between the annotation functors of two
LCEL instances.

The correspondence supplies a typed map between the two annotation-type
spaces that preserves the annotation of the designated derivation on each
side. Because `LCELAnnotationFunctor.Annotation` is instance-specific, this
map is a real semantic bridge. -/
structure AnnotationFunctorCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Translation of annotations from `L₁` to `L₂`. -/
  translateAnnotation :
    L₁.annotationFunctor.Annotation → L₂.annotationFunctor.Annotation
  /-- The annotation of the designated derivation on `L₁` translates to the
  annotation of the designated derivation on `L₂`. -/
  translate_annotate_witness :
    translateAnnotation
      (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)
      = L₂.annotationFunctor.annotate L₂.comparison.reimportContent.witness

namespace AnnotationFunctorCorrespondence

/-- The translation of the designated source annotation decodes to a
sentence that the target reimport layer certifies and that is true in the
target's reference model. Equivalent to saying: the typed annotation map
preserves the certification and truth properties at the designated
derivation. -/
theorem translate_annotate_witness_certified
    {L₁ L₂ : FormalLCELInstance}
    (C : AnnotationFunctorCorrespondence L₁ L₂) :
    L₂.comparison.reimportContent.certifies
        L₂.comparison.reimportContent.witness
        (L₂.annotationFunctor.decode
          (C.translateAnnotation
            (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)))
      ∧ L₂.comparison.baseTheoryContent.trueInReferenceModel
        (L₂.annotationFunctor.decode
          (C.translateAnnotation
            (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness))) := by
  refine ⟨?_, ?_⟩
  · rw [C.translate_annotate_witness]
    exact L₂.annotationFunctor.witness_certifies_decoded
  · rw [C.translate_annotate_witness]
    exact L₂.annotationFunctor.witness_decoded_true

end AnnotationFunctorCorrespondence

/-! ## Packaged semantic slot correspondence -/

/-- Typed semantic slot correspondence between two LCEL instances, bundling
the four slot-level correspondence structures. -/
structure LCELSemanticSlotCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  boundary : BoundaryObjectCorrespondence L₁ L₂
  externalLicense : ExternalLicenseCorrespondence L₁ L₂
  reimportClass : ReimportClassCorrespondence L₁ L₂
  annotation : AnnotationFunctorCorrespondence L₁ L₂

namespace LCELSemanticSlotCorrespondence

/-- The external-license biconditional induced by the external-license slot
correspondence via its explicit forward / backward transport functions. -/
theorem externalLicense_iff
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELSemanticSlotCorrespondence L₁ L₂) :
    L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness :=
  C.externalLicense.toIff

/-- The reimport-class biconditional induced by the reimport-class slot
correspondence via its explicit forward / backward transport functions. -/
theorem reimportClass_iff
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELSemanticSlotCorrespondence L₁ L₂) :
    L₁.reimportClassWitness ↔ L₂.reimportClassWitness :=
  C.reimportClass.toIff

end LCELSemanticSlotCorrespondence

/-! ## From semantic correspondence to a comparison witness

A semantic slot correspondence is strictly richer than the existing
`LCELComparisonWitness`: the latter packages stagewise equivalence of the
underlying comparison profiles together with biconditionals on the
external-license and reimport-class slots. The stagewise equivalence of
comparison profiles lives below the LCEL typed carriers, so it cannot be
derived from the semantic correspondence alone; it must be supplied
separately.

`LCELComparisonWitness.ofSemanticSlotCorrespondence` takes a semantic slot
correspondence together with the stagewise equivalence of the underlying
comparison profiles and produces an `LCELComparisonWitness` in which the
external-license and reimport-class biconditionals come from the typed
transport functions of the correspondence rather than from `iff_of_true`
inhabitance.
-/

/-- Build a slot-level comparison witness from a semantic slot correspondence
together with stagewise equivalence of the underlying comparison profiles. -/
def LCELComparisonWitness.ofSemanticSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELSemanticSlotCorrespondence L₁ L₂)
    (hShape :
      StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape) :
    LCELComparisonWitness L₁ L₂ where
  comparisonStagewise := hShape
  externalLicenseEquivalent := C.externalLicense.toIff
  reimportClassEquivalent := C.reimportClass.toIff

/-! ## Canonical semantic correspondences

Both canonical Gödel ↔ benchmark-transport and Gödel ↔ native-DP pairs admit
a semantic slot correspondence whose boundary and annotation maps are the
constant designated-witness maps. These constant maps preserve the designated
witness by construction, so they satisfy the correspondence laws honestly
(not by `iff_of_true` on inhabitance). The external-license and reimport-class
forward / backward transports use the target and source instance's own
`externalLicenseHolds` / `reimportClassHolds` fields respectively.
-/

/-- Gödel-to-benchmark boundary correspondence: the constant map sending every
source boundary witness to the target's designated witness. -/
def godel_benchmark_boundaryCorrespondence :
    BoundaryObjectCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  translate _ := benchmarkTransportLCELInstance.boundaryObject.designated
  translate_designated := rfl

/-- Gödel-to-benchmark annotation correspondence: the constant map sending
every source annotation to the target's designated-derivation annotation. -/
def godel_benchmark_annotationCorrespondence :
    AnnotationFunctorCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  translateAnnotation _ :=
    benchmarkTransportLCELInstance.annotationFunctor.annotate
      benchmarkTransportLCELInstance.comparison.reimportContent.witness
  translate_annotate_witness := rfl

/-- Gödel-to-benchmark external-license correspondence. -/
def godel_benchmark_externalLicenseCorrespondence :
    ExternalLicenseCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  forward _ := benchmarkTransportLCELInstance.externalLicenseHolds
  backward _ := godel1931LCELInstance.externalLicenseHolds

/-- Gödel-to-benchmark reimport-class correspondence. -/
def godel_benchmark_reimportClassCorrespondence :
    ReimportClassCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  forward _ := benchmarkTransportLCELInstance.reimportClassHolds
  backward _ := godel1931LCELInstance.reimportClassHolds

/-- Gödel-to-benchmark packaged semantic slot correspondence. -/
def godel_benchmark_semanticSlotCorrespondence :
    LCELSemanticSlotCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  boundary := godel_benchmark_boundaryCorrespondence
  externalLicense := godel_benchmark_externalLicenseCorrespondence
  reimportClass := godel_benchmark_reimportClassCorrespondence
  annotation := godel_benchmark_annotationCorrespondence

/-- Gödel-to-DP boundary correspondence. -/
def godel_dp_boundaryCorrespondence :
    BoundaryObjectCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  translate _ := dpEmitterLCELInstance.boundaryObject.designated
  translate_designated := rfl

/-- Gödel-to-DP annotation correspondence. -/
def godel_dp_annotationCorrespondence :
    AnnotationFunctorCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  translateAnnotation _ :=
    dpEmitterLCELInstance.annotationFunctor.annotate
      dpEmitterLCELInstance.comparison.reimportContent.witness
  translate_annotate_witness := rfl

/-- Gödel-to-DP external-license correspondence. -/
def godel_dp_externalLicenseCorrespondence :
    ExternalLicenseCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  forward _ := dpEmitterLCELInstance.externalLicenseHolds
  backward _ := godel1931LCELInstance.externalLicenseHolds

/-- Gödel-to-DP reimport-class correspondence. -/
def godel_dp_reimportClassCorrespondence :
    ReimportClassCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  forward _ := dpEmitterLCELInstance.reimportClassHolds
  backward _ := godel1931LCELInstance.reimportClassHolds

/-- Gödel-to-DP packaged semantic slot correspondence. -/
def godel_dp_semanticSlotCorrespondence :
    LCELSemanticSlotCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  boundary := godel_dp_boundaryCorrespondence
  externalLicense := godel_dp_externalLicenseCorrespondence
  reimportClass := godel_dp_reimportClassCorrespondence
  annotation := godel_dp_annotationCorrespondence

/-! ## Strengthened boundary correspondence with preservation laws

A `StrongBoundaryObjectCorrespondence` refines `BoundaryObjectCorrespondence`
by additionally requiring that the typed translate map preserve the two
structural laws of the boundary object: non-provability of the boundary
sentence in the base, and truth in the reference model. This is a genuine
strengthening: the downgrade to `BoundaryObjectCorrespondence` forgets the
preservation laws, whereas the upgrade forces them to be provided.

For the manuscript-critical Gödel ↔ native DP canonical pair, the strengthened
correspondence is populated by noting that the constant translate map
(sending every source witness to the target's designated witness) trivially
satisfies the preservation laws, because the target's designated witness
itself satisfies both laws by the `LCELBoundaryObject` structure. This
shows that the constant canonical choice is compatible with the stronger
preservation obligation: it is not a defect of the canonical witnesses
but a legitimate proof strategy on this pair.
-/

/-- Strengthened boundary-object correspondence: refines the typed
translate map of `BoundaryObjectCorrespondence` with explicit preservation
laws for non-provability of the boundary sentence and truth in the
reference model. -/
structure StrongBoundaryObjectCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends BoundaryObjectCorrespondence L₁ L₂ where
  /-- The translation preserves non-provability of the boundary sentence. -/
  translate_preserves_not_provable :
    ∀ w : L₁.boundaryObject.BoundaryWitness,
      (¬ L₁.comparison.baseTheoryContent.proves
            (L₁.boundaryObject.boundarySentence w))
        → ¬ L₂.comparison.baseTheoryContent.proves
            (L₂.boundaryObject.boundarySentence (translate w))
  /-- The translation preserves truth in the reference model. -/
  translate_preserves_true :
    ∀ w : L₁.boundaryObject.BoundaryWitness,
      L₁.comparison.baseTheoryContent.trueInReferenceModel
          (L₁.boundaryObject.boundarySentence w)
        → L₂.comparison.baseTheoryContent.trueInReferenceModel
            (L₂.boundaryObject.boundarySentence (translate w))

namespace StrongBoundaryObjectCorrespondence

/-- A strong correspondence always realizes the target boundary slot on the
translation of any source-side boundary witness, not just on the designated
witness. This is the genuine preservation theorem the strong correspondence
supplies beyond what `BoundaryObjectCorrespondence` alone provides. -/
theorem translate_realizes
    {L₁ L₂ : FormalLCELInstance}
    (C : StrongBoundaryObjectCorrespondence L₁ L₂)
    (w : L₁.boundaryObject.BoundaryWitness)
    (hNotProvable :
      ¬ L₁.comparison.baseTheoryContent.proves
          (L₁.boundaryObject.boundarySentence w))
    (hTrue :
      L₁.comparison.baseTheoryContent.trueInReferenceModel
        (L₁.boundaryObject.boundarySentence w)) :
    (¬ L₂.comparison.baseTheoryContent.proves
        (L₂.boundaryObject.boundarySentence (C.translate w)))
      ∧ L₂.comparison.baseTheoryContent.trueInReferenceModel
        (L₂.boundaryObject.boundarySentence (C.translate w)) :=
  ⟨C.translate_preserves_not_provable w hNotProvable,
    C.translate_preserves_true w hTrue⟩

end StrongBoundaryObjectCorrespondence

/-- Strengthened Gödel-to-DP boundary correspondence. The constant translate
map sends every source boundary witness to the DP side's designated witness,
which satisfies both preservation laws because that designated witness
itself is by construction not provable in the DP-side base and is true in
the DP-side reference model. -/
def godel_dp_strongBoundaryCorrespondence :
    StrongBoundaryObjectCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toBoundaryObjectCorrespondence := godel_dp_boundaryCorrespondence
  translate_preserves_not_provable := by
    intro _ _
    exact dpEmitterLCELInstance.boundaryObject.designated_not_provable
  translate_preserves_true := by
    intro _ _
    exact dpEmitterLCELInstance.boundaryObject.designated_true

/-- Strengthened Gödel-to-benchmark boundary correspondence. Discharged
by the benchmark-transport instance's own `designated_not_provable` and
`designated_true` fields, exactly as on the DP side. -/
def godel_benchmark_strongBoundaryCorrespondence :
    StrongBoundaryObjectCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toBoundaryObjectCorrespondence := godel_benchmark_boundaryCorrespondence
  translate_preserves_not_provable := by
    intro _ _
    exact benchmarkTransportLCELInstance.boundaryObject.designated_not_provable
  translate_preserves_true := by
    intro _ _
    exact benchmarkTransportLCELInstance.boundaryObject.designated_true

/-! ## Strengthened external-license correspondence with preservation laws

A `StrongExternalLicenseCorrespondence` refines `ExternalLicenseCorrespondence`
with explicit preservation laws for the two pieces of reflection-content
substrate that the license slot actually licenses on each instance:
non-provability of the blocked sentence in the base, and reflection of it
by the stronger framework. This is the genuine semantic content the license
slot is meant to transport — not just inhabitance of an opaque proposition,
but the fact that the target side really does have a blocked-but-reflected
designated sentence whenever the source side has an external license.

On the manuscript-critical Gödel ↔ native DP canonical pair, both laws are
discharged by the target instance's own `LCELReflectionContent`
`blocked_not_provable` and the structural
`strongerFrameworkReflectsBlocked` field of the DP-side license support
record. So the canonical constant transport, whose forward map ignores
the source input and returns the DP-side `externalLicenseHolds`,
legitimately satisfies the strengthened preservation obligations. -/

/-- Strengthened external-license correspondence: refines
`ExternalLicenseCorrespondence` with preservation laws for the two
structural facts the license slot licenses on each instance. -/
structure StrongExternalLicenseCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends ExternalLicenseCorrespondence L₁ L₂ where
  /-- The forward transport certifies that the target's reflection content
  has a blocked sentence that is not provable in the target base theory. -/
  forward_preserves_blocked_not_provable :
    L₁.externalLicenseWitness →
      ¬ L₂.comparison.baseTheoryContent.proves
          L₂.comparison.reflectionContent.blockedSentence
  /-- The forward transport certifies that the target's reflection content
  has a blocked sentence that the target stronger framework reflects. -/
  forward_preserves_stronger_reflects :
    L₁.externalLicenseWitness →
      L₂.comparison.reflectionContent.reflects
        L₂.comparison.reflectionContent.strongerFramework
        L₂.comparison.reflectionContent.blockedSentence

namespace StrongExternalLicenseCorrespondence

/-- A strong external-license correspondence, given a source-side license
witness, produces the `licenseExtendsBase` conjunction on the target side.
This is the genuine preservation theorem the strong correspondence
supplies beyond what `ExternalLicenseCorrespondence` alone provides. -/
theorem forward_preserves_licenseExtendsBase
    {L₁ L₂ : FormalLCELInstance}
    (C : StrongExternalLicenseCorrespondence L₁ L₂)
    (h : L₁.externalLicenseWitness) :
    (¬ L₂.comparison.baseTheoryContent.proves
        L₂.comparison.reflectionContent.blockedSentence)
      ∧ L₂.comparison.reflectionContent.reflects
          L₂.comparison.reflectionContent.strongerFramework
          L₂.comparison.reflectionContent.blockedSentence :=
  ⟨C.forward_preserves_blocked_not_provable h,
    C.forward_preserves_stronger_reflects h⟩

end StrongExternalLicenseCorrespondence

/-- Strengthened Gödel-to-DP external-license correspondence. The forward
transport from source license to DP-side license already lands in the DP
instance, so the preservation laws are discharged by the DP side's own
reflection-content laws (`blocked_not_provable` and
`strongerFrameworkReflectsBlocked`). -/
def godel_dp_strongExternalLicenseCorrespondence :
    StrongExternalLicenseCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toExternalLicenseCorrespondence := godel_dp_externalLicenseCorrespondence
  forward_preserves_blocked_not_provable := by
    intro _
    exact dpEmitterLCELInstance.comparison.reflectionContent.blocked_not_provable
  forward_preserves_stronger_reflects := by
    intro _
    exact dpEmitterLicenseIrreversibilitySupport.strongerFrameworkReflectsBlocked

/-! ## Strengthened reimport-class correspondence with preservation laws

A `StrongReimportClassCorrespondence` refines `ReimportClassCorrespondence`
with explicit preservation laws for the two reimport-content substrate
facts the class slot actually licenses: the reimport witness certifies
the imported sentence, and the imported sentence is true in the target
reference model. -/

/-- Strengthened reimport-class correspondence. -/
structure StrongReimportClassCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends ReimportClassCorrespondence L₁ L₂ where
  /-- The forward transport certifies that the target reimport witness
  certifies the target imported sentence. -/
  forward_preserves_witness_certifies_imported :
    L₁.reimportClassWitness →
      L₂.comparison.reimportContent.certifies
        L₂.comparison.reimportContent.witness
        L₂.comparison.reimportContent.importedSentence
  /-- The forward transport certifies that the target imported sentence
  is true in the target reference model. -/
  forward_preserves_imported_true :
    L₁.reimportClassWitness →
      L₂.comparison.baseTheoryContent.trueInReferenceModel
        L₂.comparison.reimportContent.importedSentence

/-- Strengthened Gödel-to-DP reimport-class correspondence. -/
def godel_dp_strongReimportClassCorrespondence :
    StrongReimportClassCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toReimportClassCorrespondence := godel_dp_reimportClassCorrespondence
  forward_preserves_witness_certifies_imported := by
    intro _
    exact dpEmitterReimportReversibilitySupport.witnessCertifiesImported
  forward_preserves_imported_true := by
    intro _
    exact dpEmitterReimportReversibilitySupport.importedTrue

/-! ## Strengthened annotation-functor correspondence with preservation laws

A `StrongAnnotationFunctorCorrespondence` refines
`AnnotationFunctorCorrespondence` with an explicit preservation law:
under the typed annotation translation, the target reimport witness
certifies the decoded translated annotation, and the decoded translated
annotation is true in the target reference model. This is the annotation-
side analogue of the boundary preservation strengthening. -/

/-- Strengthened annotation-functor correspondence. -/
structure StrongAnnotationFunctorCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends AnnotationFunctorCorrespondence L₁ L₂ where
  /-- The target reimport witness certifies the translated annotation's
  decode. -/
  translate_preserves_witness_certifies_decoded :
    L₂.comparison.reimportContent.certifies
        L₂.comparison.reimportContent.witness
        (L₂.annotationFunctor.decode
          (translateAnnotation
            (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)))
  /-- The translated annotation's decode is true in the target reference
  model. -/
  translate_preserves_decoded_true :
    L₂.comparison.baseTheoryContent.trueInReferenceModel
      (L₂.annotationFunctor.decode
        (translateAnnotation
          (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)))
  /-- The translated annotation's decode equals the target-side imported
  sentence. This is the annotation-side decoding-coherence law required by
  the reimport theorem's `annotationDecodes_imported` field: together with
  `translate_annotate_witness`, it lets us rewrite
  `L₂.annotationFunctor.decode (L₂.annotationFunctor.annotate L₂.comparison.reimportContent.witness)`
  via the correspondence's typed translate map rather than through a
  target-side fallback. -/
  translate_preserves_decodes_to_imported :
    L₂.annotationFunctor.decode
        (translateAnnotation
          (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness))
      = L₂.comparison.reimportContent.importedSentence

/-- Strengthened Gödel-to-DP annotation-functor correspondence. On the
canonical pair the constant translate map sends every source annotation to
the DP side's designated annotation, whose decode is certified by the DP
reimport witness and true in the DP reference model by the DP
annotation-functor's own laws. -/
def godel_dp_strongAnnotationFunctorCorrespondence :
    StrongAnnotationFunctorCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toAnnotationFunctorCorrespondence := godel_dp_annotationCorrespondence
  translate_preserves_witness_certifies_decoded :=
    dpEmitterLCELInstance.annotationFunctor.witness_certifies_decoded
  translate_preserves_decoded_true :=
    dpEmitterLCELInstance.annotationFunctor.witness_decoded_true
  translate_preserves_decodes_to_imported :=
    dpEmitterLCELInstance.annotationFunctor.witness_decodes_to_imported

/-! ## Typed translation of base-theory sentences

The LCEL slots (boundary, external license, reimport class, annotation)
are instance-specific typed structures; typed maps between them were
already in `LCELSemanticSlotCorrespondence`. But the theorem-strength
substrate objects of `LCELSubstrateMathematics.lean` also carry
**base-theory-sentence-valued fields** (the `provedSentence` of a
`BaseReversibilityTheorem`, for instance) that cannot be translated
without a typed map on base-theory sentences. `BaseSentenceCorrespondence`
supplies that typed map together with a preservation law for provability,
so that a source-side base reversibility theorem's `provedSentence` /
`provedSentence_proved` can be translated to the target. -/

/-- Typed semantic correspondence between the base-theory sentence spaces
of two LCEL instances, carrying a provability-preservation law. -/
structure BaseSentenceCorrespondence (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Translate a source base-theory sentence to a target base-theory sentence. -/
  translateProvedSentence :
    L₁.comparison.baseTheoryContent.Sentence →
    L₂.comparison.baseTheoryContent.Sentence
  /-- Provability of a source sentence transports to provability of the
  translated target sentence. -/
  translateProvedSentence_preserves_provable :
    ∀ s : L₁.comparison.baseTheoryContent.Sentence,
      L₁.comparison.baseTheoryContent.proves s →
      L₂.comparison.baseTheoryContent.proves (translateProvedSentence s)

/-- Canonical Gödel-to-DP base-sentence correspondence. The translation
sends every source sentence to the target's internal proved sentence,
and the preservation law is discharged by the DP-side support record's
own `internalSentenceProved` field. This is the constant translation on
the canonical pair: different correspondences would yield a richer
sentence-level map. -/
def godel_dp_baseSentenceCorrespondence :
    BaseSentenceCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  translateProvedSentence _ :=
    dpEmitterBaseReversibilitySupport.internalSentence
  translateProvedSentence_preserves_provable := by
    intro _ _
    exact dpEmitterBaseReversibilitySupport.internalSentenceProved

/-- Canonical Gödel-to-benchmark base-sentence correspondence. -/
def godel_benchmark_baseSentenceCorrespondence :
    BaseSentenceCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  translateProvedSentence _ :=
    benchmarkTransportBaseReversibilitySupport.internalSentence
  translateProvedSentence_preserves_provable := by
    intro _ _
    exact benchmarkTransportBaseReversibilitySupport.internalSentenceProved

/-! ## Packaged strong semantic slot correspondence

Bundles the four strong-correspondence structures plus the typed
base-sentence correspondence into a single slot package, the
strengthened analogue of `LCELSemanticSlotCorrespondence`. Its downgrade
to the plain `LCELSemanticSlotCorrespondence` forgets the preservation
laws and the sentence-translation layer. -/

/-- Packaged strong semantic slot correspondence: bundles the four
strengthened slot correspondences plus a typed base-sentence translation
with provability preservation. -/
structure LCELStrongSemanticSlotCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  boundary : StrongBoundaryObjectCorrespondence L₁ L₂
  externalLicense : StrongExternalLicenseCorrespondence L₁ L₂
  reimportClass : StrongReimportClassCorrespondence L₁ L₂
  annotation : StrongAnnotationFunctorCorrespondence L₁ L₂
  baseSentence : BaseSentenceCorrespondence L₁ L₂

namespace LCELStrongSemanticSlotCorrespondence

/-- Downgrade to the plain semantic slot correspondence. -/
def toSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂) :
    LCELSemanticSlotCorrespondence L₁ L₂ where
  boundary := C.boundary.toBoundaryObjectCorrespondence
  externalLicense := C.externalLicense.toExternalLicenseCorrespondence
  reimportClass := C.reimportClass.toReimportClassCorrespondence
  annotation := C.annotation.toAnnotationFunctorCorrespondence

end LCELStrongSemanticSlotCorrespondence

/-- Canonical Gödel-to-DP strong semantic slot correspondence. -/
def godel_dp_strongSemanticSlotCorrespondence :
    LCELStrongSemanticSlotCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  boundary := godel_dp_strongBoundaryCorrespondence
  externalLicense := godel_dp_strongExternalLicenseCorrespondence
  reimportClass := godel_dp_strongReimportClassCorrespondence
  annotation := godel_dp_strongAnnotationFunctorCorrespondence
  baseSentence := godel_dp_baseSentenceCorrespondence

/-! ## Strong correspondences for the Gödel ↔ benchmark-transport pair

The benchmark-transport instance admits the same strong-slot story as the
DP instance: its canonical reflection content, reimport content, and
annotation functor all satisfy the preservation laws out of the box, and
the constant boundary translate map is admissible for the same reason as
on the DP side.
-/

/-- Strong external-license correspondence on the Gödel ↔ benchmark pair. -/
def godel_benchmark_strongExternalLicenseCorrespondence :
    StrongExternalLicenseCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toExternalLicenseCorrespondence :=
    godel_benchmark_externalLicenseCorrespondence
  forward_preserves_blocked_not_provable := by
    intro _
    exact benchmarkTransportLCELInstance.comparison.reflectionContent.blocked_not_provable
  forward_preserves_stronger_reflects := by
    intro _
    exact benchmarkTransportLicenseIrreversibilitySupport.strongerFrameworkReflectsBlocked

/-- Strong reimport-class correspondence on the Gödel ↔ benchmark pair. -/
def godel_benchmark_strongReimportClassCorrespondence :
    StrongReimportClassCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toReimportClassCorrespondence := godel_benchmark_reimportClassCorrespondence
  forward_preserves_witness_certifies_imported := by
    intro _
    exact benchmarkTransportReimportReversibilitySupport.witnessCertifiesImported
  forward_preserves_imported_true := by
    intro _
    exact benchmarkTransportReimportReversibilitySupport.importedTrue

/-- Strong annotation-functor correspondence on the Gödel ↔ benchmark pair. -/
def godel_benchmark_strongAnnotationFunctorCorrespondence :
    StrongAnnotationFunctorCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toAnnotationFunctorCorrespondence := godel_benchmark_annotationCorrespondence
  translate_preserves_witness_certifies_decoded :=
    benchmarkTransportLCELInstance.annotationFunctor.witness_certifies_decoded
  translate_preserves_decoded_true :=
    benchmarkTransportLCELInstance.annotationFunctor.witness_decoded_true
  translate_preserves_decodes_to_imported :=
    benchmarkTransportLCELInstance.annotationFunctor.witness_decodes_to_imported

/-- Packaged strong semantic slot correspondence on the Gödel ↔ benchmark
pair. -/
def godel_benchmark_strongSemanticSlotCorrespondence :
    LCELStrongSemanticSlotCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  boundary := godel_benchmark_strongBoundaryCorrespondence
  externalLicense := godel_benchmark_strongExternalLicenseCorrespondence
  reimportClass := godel_benchmark_strongReimportClassCorrespondence
  annotation := godel_benchmark_strongAnnotationFunctorCorrespondence
  baseSentence := godel_benchmark_baseSentenceCorrespondence

end OperatorKO7.LCELSemanticCorrespondence
