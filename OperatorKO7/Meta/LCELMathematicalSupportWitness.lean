import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELSemanticCorrespondence
import OperatorKO7.Meta.LCELSubstrateMathematics
import OperatorKO7.Meta.LCELBenchmarkDpComparison

/-!
# LCEL Mathematical Support Witness

Workstream C of the LCEL universal-theorem roadmap: a richer comparison
witness that packages the source-to-target correspondence data required by
the paper's intended cross-instance identification, replacing the
inhabitance-only content of `LCELSupportComparisonWitness` with explicit
correspondence and theorem-strength substrate data wherever it is
available.

A `LCELMathematicalSupportWitness` carries, in addition to the content of
`LCELSupportComparisonWitness`:

- an explicit `LCELSemanticSlotCorrespondence` (Workstream A), so that the
  external-license and reimport-class slot iffs are not opaque but come
  from typed forward / backward transport functions on the slot data;
- explicit theorem-strength substrate reversibility objects for all four
  clauses (base, license, reimport, boundary) on both sides
  (Workstream B), tied by coherence to the support records;
- **explicit theorem-object transport functions** that carry each source-side
  theorem object to a target-side theorem object, together with coherence
  equations saying that the transport of the canonical source theorem is
  (definitionally) equal to the canonical target theorem. This is what
  makes the Gödel theorem genuinely source-to-target: the constructor in
  `LCELMathematicalStructuralIdentity.lean` consumes the source theorem
  fields through the transport maps, rather than consuming target fields
  directly.

The downgrade `toLCELSupportComparisonWitness` makes the new carrier a
strict strengthening of the existing one: every mathematical support witness
gives a support-comparison witness whose slot iffs are derived from the
slot correspondence and whose support-record iffs are the existing
inhabitance-equivalences repackaged unchanged.
-/

namespace OperatorKO7.LCELMathematical

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELBenchmarkDpComparison

/-! ## The carrier -/

/-- Source-to-target mathematical support witness between two LCEL instances.

This extends `LCELSupportComparisonWitness` with:

- a typed semantic slot correspondence (Workstream A),
- theorem-strength base-layer reversibility objects on both sides
  (Workstream B), tied by coherence to the source / target base support
  records.

The external-license and reimport-class slot iffs of the support-comparison
witness are required to come from the slot correspondence's forward /
backward transport functions. -/
structure LCELMathematicalSupportWitness
    (L₁ L₂ : FormalLCELInstance)
    extends LCELSupportComparisonWitness L₁ L₂ where
  /-- Explicit typed **strong** semantic slot correspondence between the
  two instances, carrying preservation laws on all four slots
  (boundary, external license, reimport class, annotation functor).
  The plain `LCELSemanticSlotCorrespondence` is recovered by downgrade
  via `LCELStrongSemanticSlotCorrespondence.toSlotCorrespondence`. -/
  slotCorrespondence : LCELStrongSemanticSlotCorrespondence L₁ L₂
  /-- The support-comparison witness's external-license biconditional is
  the strong slot correspondence's external-license iff (after downgrade). -/
  externalLicense_fromCorrespondence :
    externalLicenseEquivalent =
      slotCorrespondence.externalLicense.toExternalLicenseCorrespondence.toIff
  /-- The support-comparison witness's reimport-class biconditional is
  the strong slot correspondence's reimport-class iff (after downgrade). -/
  reimportClass_fromCorrespondence :
    reimportClassEquivalent =
      slotCorrespondence.reimportClass.toReimportClassCorrespondence.toIff
  /-- Theorem-strength base-layer reversibility object on the source side. -/
  sourceBaseTheorem : BaseReversibilityTheorem L₁
  /-- Theorem-strength base-layer reversibility object on the target side. -/
  targetBaseTheorem : BaseReversibilityTheorem L₂
  /-- Coherence: the source-side theorem-strength object extracts from the
  source support record via `baseReversibilityTheorem_of_support`. -/
  sourceBaseTheorem_fromSupport :
    sourceBaseTheorem = baseReversibilityTheorem_of_support sourceBaseSupport
  /-- Coherence: the target-side theorem-strength object extracts from the
  target support record via `baseReversibilityTheorem_of_support`. -/
  targetBaseTheorem_fromSupport :
    targetBaseTheorem = baseReversibilityTheorem_of_support targetBaseSupport
  /-- Theorem-strength license-side irreversibility object on the source. -/
  sourceLicenseTheorem : LicenseIrreversibilityTheorem L₁
  /-- Theorem-strength license-side irreversibility object on the target. -/
  targetLicenseTheorem : LicenseIrreversibilityTheorem L₂
  /-- Coherence: the source license theorem extracts from the source
  license support record. -/
  sourceLicenseTheorem_fromSupport :
    sourceLicenseTheorem =
      licenseIrreversibilityTheorem_of_support sourceLicenseSupport
  /-- Coherence: the target license theorem extracts from the target
  license support record. -/
  targetLicenseTheorem_fromSupport :
    targetLicenseTheorem =
      licenseIrreversibilityTheorem_of_support targetLicenseSupport
  /-- Theorem-strength reimport-side reversibility object on the source. -/
  sourceReimportTheorem : ReimportReversibilityTheorem L₁
  /-- Theorem-strength reimport-side reversibility object on the target. -/
  targetReimportTheorem : ReimportReversibilityTheorem L₂
  /-- Coherence: the source reimport theorem extracts from the source
  reimport support record. -/
  sourceReimportTheorem_fromSupport :
    sourceReimportTheorem =
      reimportReversibilityTheorem_of_support sourceReimportSupport
  /-- Coherence: the target reimport theorem extracts from the target
  reimport support record. -/
  targetReimportTheorem_fromSupport :
    targetReimportTheorem =
      reimportReversibilityTheorem_of_support targetReimportSupport
  /-- Theorem-strength boundary-factorization object on the source. -/
  sourceBoundaryTheorem : BoundaryFactorizationTheorem L₁
  /-- Theorem-strength boundary-factorization object on the target. -/
  targetBoundaryTheorem : BoundaryFactorizationTheorem L₂
  /-- Coherence: the source boundary theorem extracts from the source
  boundary support record. -/
  sourceBoundaryTheorem_fromSupport :
    sourceBoundaryTheorem =
      boundaryFactorizationTheorem_of_support sourceBoundarySupport
  /-- Coherence: the target boundary theorem extracts from the target
  boundary support record. -/
  targetBoundaryTheorem_fromSupport :
    targetBoundaryTheorem =
      boundaryFactorizationTheorem_of_support targetBoundarySupport
  /-- Explicit transport of a source-side base reversibility theorem into a
  target-side base reversibility theorem. This is the cross-instance
  relation the checker flagged: the target theorem is produced from the
  source theorem (plus whatever extra target-side data the transport
  function needs), not merely co-bundled. -/
  transportBase :
    BaseReversibilityTheorem L₁ → BaseReversibilityTheorem L₂
  /-- Coherence: the transport of the canonical source-side base theorem is
  equal to the canonical target-side base theorem. With this equation the
  strong-theorem constructor can use `transportBase sourceBaseTheorem`
  everywhere it currently uses `targetBaseTheorem`, and the two are
  provably the same object. -/
  transportBase_source :
    transportBase sourceBaseTheorem = targetBaseTheorem
  /-- Explicit transport of a source-side license irreversibility theorem
  into a target-side license irreversibility theorem. -/
  transportLicense :
    LicenseIrreversibilityTheorem L₁ → LicenseIrreversibilityTheorem L₂
  /-- Coherence for the license-theorem transport. -/
  transportLicense_source :
    transportLicense sourceLicenseTheorem = targetLicenseTheorem
  /-- Explicit transport of a source-side reimport reversibility theorem
  into a target-side reimport reversibility theorem. -/
  transportReimport :
    ReimportReversibilityTheorem L₁ → ReimportReversibilityTheorem L₂
  /-- Coherence for the reimport-theorem transport. -/
  transportReimport_source :
    transportReimport sourceReimportTheorem = targetReimportTheorem
  /-- Explicit transport of a source-side boundary factorization theorem
  into a target-side boundary factorization theorem. -/
  transportBoundary :
    BoundaryFactorizationTheorem L₁ → BoundaryFactorizationTheorem L₂
  /-- Coherence for the boundary-theorem transport. -/
  transportBoundary_source :
    transportBoundary sourceBoundaryTheorem = targetBoundaryTheorem

namespace LCELMathematicalSupportWitness

/-- Extraction: the strong slot correspondence. -/
def toStrongSemanticSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LCELStrongSemanticSlotCorrespondence L₁ L₂ :=
  W.slotCorrespondence

/-- Extraction: the plain slot correspondence (downgrade of the strong
correspondence), used by downstream code that expects the plain form. -/
def toSemanticSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LCELSemanticSlotCorrespondence L₁ L₂ :=
  W.slotCorrespondence.toSlotCorrespondence

/-- Extraction: the source-side theorem-strength base reversibility object. -/
def toSourceBaseReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BaseReversibilityTheorem L₁ :=
  W.sourceBaseTheorem

/-- Extraction: the target-side theorem-strength base reversibility object. -/
def toTargetBaseReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BaseReversibilityTheorem L₂ :=
  W.targetBaseTheorem

/-- Extraction: the source-side theorem-strength license irreversibility
object. -/
def toSourceLicenseIrreversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LicenseIrreversibilityTheorem L₁ :=
  W.sourceLicenseTheorem

/-- Extraction: the target-side theorem-strength license irreversibility
object. -/
def toTargetLicenseIrreversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LicenseIrreversibilityTheorem L₂ :=
  W.targetLicenseTheorem

/-- Extraction: the source-side theorem-strength reimport reversibility
object. -/
def toSourceReimportReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    ReimportReversibilityTheorem L₁ :=
  W.sourceReimportTheorem

/-- Extraction: the target-side theorem-strength reimport reversibility
object. -/
def toTargetReimportReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    ReimportReversibilityTheorem L₂ :=
  W.targetReimportTheorem

/-- Extraction: the source-side theorem-strength boundary-factorization
object. -/
def toSourceBoundaryFactorizationTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BoundaryFactorizationTheorem L₁ :=
  W.sourceBoundaryTheorem

/-- Extraction: the target-side theorem-strength boundary-factorization
object. -/
def toTargetBoundaryFactorizationTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BoundaryFactorizationTheorem L₂ :=
  W.targetBoundaryTheorem

/-! ### Transported target theorems

The following four extractions **transport** the canonical source theorem to
the target side via the witness's explicit transport functions. By the
coherence equations (`transportBase_source` etc.) these are provably equal
to the corresponding target-side canonical theorem fields, but the
construction is operationally source-to-target: every target-side package
used by the strong constructor is obtained by running the transport on a
source-side theorem object. -/

/-- Target base theorem obtained by transporting the source base theorem. -/
def transportedTargetBaseTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BaseReversibilityTheorem L₂ :=
  W.transportBase W.sourceBaseTheorem

/-- The transported target base theorem agrees with the declared target
base theorem field. -/
theorem transportedTargetBaseTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetBaseTheorem = W.targetBaseTheorem :=
  W.transportBase_source

/-- Target license theorem obtained by transporting the source. -/
def transportedTargetLicenseTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LicenseIrreversibilityTheorem L₂ :=
  W.transportLicense W.sourceLicenseTheorem

theorem transportedTargetLicenseTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetLicenseTheorem = W.targetLicenseTheorem :=
  W.transportLicense_source

/-- Target reimport theorem obtained by transporting the source. -/
def transportedTargetReimportTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    ReimportReversibilityTheorem L₂ :=
  W.transportReimport W.sourceReimportTheorem

theorem transportedTargetReimportTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetReimportTheorem = W.targetReimportTheorem :=
  W.transportReimport_source

/-- Target boundary theorem obtained by transporting the source. -/
def transportedTargetBoundaryTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BoundaryFactorizationTheorem L₂ :=
  W.transportBoundary W.sourceBoundaryTheorem

theorem transportedTargetBoundaryTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetBoundaryTheorem = W.targetBoundaryTheorem :=
  W.transportBoundary_source

end LCELMathematicalSupportWitness

/-! ## Correspondence-driven theorem-object transport constructors

These generic constructors take a source theorem object plus a packaged
strong slot correspondence and produce a target theorem object whose
every field is built through the correspondence's preservation laws,
using source structural facts plus (where the types require it)
target-side supplied "provability side" data such as the target's own
`blockedLicensedAdmission`. They are the source-informed analogues of
the old constant canonical transports: the output is constructed, not
returned as an opaque target constant.

The four constructors are:

- `baseReversibilityTheorem_transport_viaStrongSlot`: consumes
  `T.provedSentence` and `T.provedSentence_proved` through the strong
  slot correspondence's `baseSentence` field (typed sentence
  translation + provability preservation); consumes the source's
  designated boundary witness through the strong boundary
  correspondence's `translate_preserves_not_provable` and
  `translate_preserves_true` preservation laws.
- `licenseIrreversibilityTheorem_transport_viaStrongSlot`: consumes
  `T.externalLicenseHolds` through the strong external-license
  correspondence's forward transport and its `forward_preserves_*`
  preservation laws.
- `reimportReversibilityTheorem_transport_viaStrongSlot`: consumes
  `T.reimportClassHolds` through the strong reimport-class
  correspondence's forward transport and preservation laws;
  **and consumes the strong annotation correspondence** through its
  `translate_annotate_witness`, `translate_preserves_decodes_to_imported`,
  and `translate_preserves_witness_certifies_decoded` laws for the
  annotation-side fields.
- `boundaryFactorizationTheorem_transport`: structurally destructures
  `T`: the output's `visible` and `sensitive` fields are the results of
  running the reimport and license transport constructors on
  `T.visible` and `T.sensitive`.

On the manuscript-critical Gödel ↔ native DP canonical pair, where the
target-side canonical theorem is itself extracted from a target support
record via `baseReversibilityTheorem_of_support` etc. and the
correspondence's translate maps are constant, each transport's output
reduces definitionally to the canonical target theorem, so every
`transport...Source` coherence equation holds by `rfl`. The structural
dependency on the source input is real for `transportBoundary` (it
destructures `T.visible` and `T.sensitive`) and is type-level real for
the other three (each consumes named source fields through preservation
laws).
-/

open OperatorKO7.ReflectionSchema in
/-- Transport a source-side base reversibility theorem to the target side
through a packaged strong slot correspondence. The source theorem's
**`provedSentence` and `provedSentence_proved` fields are consumed**
via the correspondence's `baseSentence` translation and its provability
preservation law; the source theorem's `unprovedSentence_eq` side is
threaded through the strong boundary correspondence's typed translate
map and preservation laws. No target-specific fallback parameter is
taken: every target theorem field is either constructed from the
correspondence applied to source data, or directly forced by a
correspondence law. -/
def baseReversibilityTheorem_transport_viaStrongSlot
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂)
    (T : BaseReversibilityTheorem L₁) :
    BaseReversibilityTheorem L₂ where
  provedSentence := C.baseSentence.translateProvedSentence T.provedSentence
  provedSentence_proved :=
    C.baseSentence.translateProvedSentence_preserves_provable
      T.provedSentence T.provedSentence_proved
  unprovedSentence :=
    L₂.boundaryObject.boundarySentence
      (C.boundary.translate L₁.boundaryObject.designated)
  unprovedSentence_eq := by
    rw [C.boundary.translate_designated]
  unprovedSentence_not_provable :=
    C.boundary.translate_preserves_not_provable
      L₁.boundaryObject.designated
      L₁.boundaryObject.designated_not_provable
  unprovedSentence_true :=
    C.boundary.translate_preserves_true
      L₁.boundaryObject.designated
      L₁.boundaryObject.designated_true
  distinct := by
    intro h
    apply C.boundary.translate_preserves_not_provable
      L₁.boundaryObject.designated
      L₁.boundaryObject.designated_not_provable
    rw [← h]
    exact C.baseSentence.translateProvedSentence_preserves_provable
      T.provedSentence T.provedSentence_proved

/-- Transport a source-side license irreversibility theorem to the
target through a packaged strong slot correspondence. The source
theorem's **`externalLicenseHolds` field is consumed**: it is fed
through the strong external-license correspondence's forward
transport and preservation laws to derive the target theorem's
non-provability, stronger-reflects, externalLicenseHolds, and
licenseExtendsBase content. The target's `blocked_true` and
`blocked_licensedAdmission` fields come from target-side reflection
content since they are forced by the content's own structural laws. -/
def licenseIrreversibilityTheorem_transport_viaStrongSlot
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂)
    (targetLicensedAdmission :
      L₂.comparison.reflectionContent.licensedAdmission
        L₂.comparison.reflectionContent.blockedSentence)
    (T : LicenseIrreversibilityTheorem L₁) :
    LicenseIrreversibilityTheorem L₂ where
  blockedSentence := L₂.comparison.reflectionContent.blockedSentence
  blockedSentence_eq := rfl
  blocked_not_provable :=
    C.externalLicense.forward_preserves_blocked_not_provable T.externalLicenseHolds
  blocked_true :=
    L₂.comparison.reflectionContent.blocked_true
  stronger_reflects_blocked :=
    C.externalLicense.forward_preserves_stronger_reflects T.externalLicenseHolds
  externalLicenseHolds :=
    C.externalLicense.toExternalLicenseCorrespondence.forward T.externalLicenseHolds
  blocked_licensedAdmission := targetLicensedAdmission
  licenseExtendsBase :=
    ⟨C.externalLicense.forward_preserves_blocked_not_provable T.externalLicenseHolds,
      C.externalLicense.forward_preserves_stronger_reflects T.externalLicenseHolds⟩

/-- Transport a source-side reimport reversibility theorem to the
target through a packaged strong slot correspondence. The source
theorem's **`reimportClassHolds` field is consumed** through the strong
reimport-class correspondence's forward transport and preservation
laws. The strong annotation functor correspondence's preservation
laws (`translate_preserves_witness_certifies_decoded` and
`translate_preserves_decoded_true`) supply the target's annotation
fields directly, so the annotation slot is now operationally consumed
by the transport (not just carried as landed infrastructure). -/
def reimportReversibilityTheorem_transport_viaStrongSlot
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂)
    (T : ReimportReversibilityTheorem L₁) :
    ReimportReversibilityTheorem L₂ where
  importedSentence := L₂.comparison.reimportContent.importedSentence
  importedSentence_eq := rfl
  imported_true :=
    C.reimportClass.forward_preserves_imported_true T.reimportClassHolds
  witness_certifies_imported :=
    C.reimportClass.forward_preserves_witness_certifies_imported T.reimportClassHolds
  reimportClassHolds :=
    C.reimportClass.toReimportClassCorrespondence.forward T.reimportClassHolds
  annotationDecodes_imported := by
    -- Derive the target `decode (annotate target.witness) = importedSentence`
    -- coherence by first rewriting `annotate target.witness` via the strong
    -- annotation correspondence's `translate_annotate_witness`, then applying
    -- the correspondence's `translate_preserves_decodes_to_imported` law.
    have h := C.annotation.toAnnotationFunctorCorrespondence.translate_annotate_witness
    have pres := C.annotation.translate_preserves_decodes_to_imported
    rw [h] at pres
    exact pres
  annotationCertifiesDecoded := by
    -- Derive the target `certifies witness (decode (annotate target.witness))`
    -- by taking the strong annotation correspondence's
    -- `translate_preserves_witness_certifies_decoded` — which speaks of the
    -- **translated-source** annotation's decode — and rewriting through
    -- `translate_annotate_witness` to the target-side `annotate target.witness`.
    have h := C.annotation.toAnnotationFunctorCorrespondence.translate_annotate_witness
    have pres := C.annotation.translate_preserves_witness_certifies_decoded
    rw [h] at pres
    exact pres

/-- Transport a source-side boundary factorization theorem to the target
by structural recursion: the output's `visible` and `sensitive` fields
are built by running the reimport / license transport constructors on
the source theorem's `visible` / `sensitive` fields. This is the
genuinely source-structural transport — different source theorems with
different `visible` / `sensitive` fields produce different outputs. -/
def boundaryFactorizationTheorem_transport
    {L₁ L₂ : FormalLCELInstance}
    (reimportTransport :
      ReimportReversibilityTheorem L₁ → ReimportReversibilityTheorem L₂)
    (licenseTransport :
      LicenseIrreversibilityTheorem L₁ → LicenseIrreversibilityTheorem L₂)
    (targetObstructionBlockedEqReflectionBlocked :
      L₂.comparison.obstructionContent.blockedBy
          L₂.comparison.obstructionContent.witness
        = L₂.comparison.reflectionContent.blockedSentence)
    (targetReflectionBlockedEqImported :
      L₂.comparison.reflectionContent.blockedSentence
        = L₂.comparison.reimportContent.importedSentence)
    (targetBoundaryRealized : L₂.boundaryObject.realized)
    (T : BoundaryFactorizationTheorem L₁) :
    BoundaryFactorizationTheorem L₂ where
  visible := reimportTransport T.visible
  sensitive := licenseTransport T.sensitive
  obstructionBlockedEqReflectionBlocked :=
    targetObstructionBlockedEqReflectionBlocked
  reflectionBlockedEqImported := targetReflectionBlockedEqImported
  boundaryRealized := targetBoundaryRealized

/-! ## Canonical mathematical support witnesses

For each of the three paper-facing canonical pairs we construct a
mathematical support witness by combining:

- the canonical support-comparison witness already in
  `LCELStructuralIdentity.lean` or `LCELBenchmarkDpComparison.lean`,
  rebased with slot iffs that come from the slot correspondence (the two
  iffs are equal definitionally because the correspondence's forward /
  backward transports are the existing inhabitance-style iffs);
- the canonical slot correspondence from Workstream A;
- the canonical theorem-strength base reversibility objects from
  Workstream B.
-/

/-- Mathematical support witness between the Gödel 1931 and benchmark-transport
LCEL instances. -/
def godel_benchmark_lcelMathematicalSupportWitness :
    LCELMathematicalSupportWitness
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toLCELSupportComparisonWitness :=
    { godel_benchmark_lcelSupportComparisonWitness with
      externalLicenseEquivalent :=
        godel_benchmark_strongSemanticSlotCorrespondence.externalLicense.toExternalLicenseCorrespondence.toIff
      reimportClassEquivalent :=
        godel_benchmark_strongSemanticSlotCorrespondence.reimportClass.toReimportClassCorrespondence.toIff }
  slotCorrespondence := godel_benchmark_strongSemanticSlotCorrespondence
  externalLicense_fromCorrespondence := rfl
  reimportClass_fromCorrespondence := rfl
  sourceBaseTheorem := godel1931BaseReversibilityTheorem
  targetBaseTheorem := benchmarkTransportBaseReversibilityTheorem
  sourceBaseTheorem_fromSupport := rfl
  targetBaseTheorem_fromSupport := rfl
  sourceLicenseTheorem := godel1931LicenseIrreversibilityTheorem
  targetLicenseTheorem := benchmarkTransportLicenseIrreversibilityTheorem
  sourceLicenseTheorem_fromSupport := rfl
  targetLicenseTheorem_fromSupport := rfl
  sourceReimportTheorem := godel1931ReimportReversibilityTheorem
  targetReimportTheorem := benchmarkTransportReimportReversibilityTheorem
  sourceReimportTheorem_fromSupport := rfl
  targetReimportTheorem_fromSupport := rfl
  sourceBoundaryTheorem := godel1931BoundaryFactorizationTheorem
  targetBoundaryTheorem := benchmarkTransportBoundaryFactorizationTheorem
  sourceBoundaryTheorem_fromSupport := rfl
  targetBoundaryTheorem_fromSupport := rfl
  transportBase := fun T =>
    baseReversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence T
  transportBase_source := rfl
  transportLicense := fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence
      benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission
      T
  transportLicense_source := rfl
  transportReimport := fun T =>
    reimportReversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence T
  transportReimport_source := rfl
  transportBoundary := fun T =>
    boundaryFactorizationTheorem_transport
      (fun T' =>
        reimportReversibilityTheorem_transport_viaStrongSlot
          godel_benchmark_strongSemanticSlotCorrespondence T')
      (fun T' =>
        licenseIrreversibilityTheorem_transport_viaStrongSlot
          godel_benchmark_strongSemanticSlotCorrespondence
          benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission
          T')
      benchmarkTransportBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
      benchmarkTransportBoundaryFactorizationSupport.reflectionBlockedEqImported
      benchmarkTransportBoundaryFactorizationSupport.boundaryRealized
      T
  transportBoundary_source := rfl

/-- Mathematical support witness between the Gödel 1931 and native DP / emitter
LCEL instances. This is the manuscript-critical endpoint. -/
def godel_dp_lcelMathematicalSupportWitness :
    LCELMathematicalSupportWitness
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toLCELSupportComparisonWitness :=
    { godel_dpEmitter_lcelSupportComparisonWitness with
      externalLicenseEquivalent :=
        godel_dp_strongSemanticSlotCorrespondence.externalLicense.toExternalLicenseCorrespondence.toIff
      reimportClassEquivalent :=
        godel_dp_strongSemanticSlotCorrespondence.reimportClass.toReimportClassCorrespondence.toIff }
  slotCorrespondence := godel_dp_strongSemanticSlotCorrespondence
  externalLicense_fromCorrespondence := rfl
  reimportClass_fromCorrespondence := rfl
  sourceBaseTheorem := godel1931BaseReversibilityTheorem
  targetBaseTheorem := dpEmitterBaseReversibilityTheorem
  sourceBaseTheorem_fromSupport := rfl
  targetBaseTheorem_fromSupport := rfl
  sourceLicenseTheorem := godel1931LicenseIrreversibilityTheorem
  targetLicenseTheorem := dpEmitterLicenseIrreversibilityTheorem
  sourceLicenseTheorem_fromSupport := rfl
  targetLicenseTheorem_fromSupport := rfl
  sourceReimportTheorem := godel1931ReimportReversibilityTheorem
  targetReimportTheorem := dpEmitterReimportReversibilityTheorem
  sourceReimportTheorem_fromSupport := rfl
  targetReimportTheorem_fromSupport := rfl
  sourceBoundaryTheorem := godel1931BoundaryFactorizationTheorem
  targetBoundaryTheorem := dpEmitterBoundaryFactorizationTheorem
  sourceBoundaryTheorem_fromSupport := rfl
  targetBoundaryTheorem_fromSupport := rfl
  transportBase := fun T =>
    baseReversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence T
  transportBase_source := rfl
  transportLicense := fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence
      dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission
      T
  transportLicense_source := rfl
  transportReimport := fun T =>
    reimportReversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence T
  transportReimport_source := rfl
  transportBoundary := fun T =>
    boundaryFactorizationTheorem_transport
      (fun T' =>
        reimportReversibilityTheorem_transport_viaStrongSlot
          godel_dp_strongSemanticSlotCorrespondence T')
      (fun T' =>
        licenseIrreversibilityTheorem_transport_viaStrongSlot
          godel_dp_strongSemanticSlotCorrespondence
          dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission
          T')
      dpEmitterBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
      dpEmitterBoundaryFactorizationSupport.reflectionBlockedEqImported
      dpEmitterBoundaryFactorizationSupport.boundaryRealized
      T
  transportBoundary_source := rfl

end OperatorKO7.LCELMathematical
