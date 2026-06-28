import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance

/-!
# LCEL Structural Identity

Artifact-facing structural parallelism for the LCEL slot carrier.

This file deliberately avoids the earlier overstatement:

- it does **not** claim that mere realization of six propositional slots is
  enough to build a meaningful LCEL quasi-functor; and
- it does **not** claim the unrestricted schema theorem from the paper.

What it does mechanize is the honest reusable core now available in the
artifact:

1. if two formal LCEL instances have stagewise-equivalent comparison profiles,
2. and if their two extra explicit LCEL slots (`Σ` and `Γ'`) are equivalent,

then there is a six-slot LCEL quasi-functor between them.

The concrete Gödel-side and benchmark/DP-side instances satisfy those
hypotheses because both comparison profiles are already proved stagewise
equivalent to the same mechanized DP profile, and both explicit extra slots are
inhabited by theorem-backed semantic witnesses.
-/

namespace OperatorKO7.LCELStructuralIdentity

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELDpInstance
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.ReflectionSchema
open OperatorKO7.StructuralIdentityComparison

private theorem iff_of_true {P Q : Prop} (hP : P) (hQ : Q) : P ↔ Q := by
  constructor
  · intro _
    exact hQ
  · intro _
    exact hP

private theorem stagewise_equivalent_of_common_dp
    {P Q : OperatorKO7.ProofTheoreticRegister.SixStepStructuralProfile}
    (hP : StagewiseEquivalent P dpAsClassicalAscentProfile.shape)
    (hQ : StagewiseEquivalent Q dpAsClassicalAscentProfile.shape) :
    StagewiseEquivalent P Q := by
  intro s
  exact (hP s).trans (hQ s).symm

/-- Six-slot mapping between two LCEL slot profiles. Each field is a
biconditional expressing slot-level parallelism. -/
structure LCELQuasiFunctor (L₁ L₂ : FormalLCELInstance) : Type where
  baseSystemMap : L₁.toSlotProfile.hasBaseSystem ↔ L₂.toSlotProfile.hasBaseSystem
  boundaryMap : L₁.toSlotProfile.hasBoundary ↔ L₂.toSlotProfile.hasBoundary
  externalLicenseMap :
    L₁.toSlotProfile.hasExternalLicense ↔ L₂.toSlotProfile.hasExternalLicense
  licensedExtensionMap :
    L₁.toSlotProfile.hasLicensedExtension
      ↔ L₂.toSlotProfile.hasLicensedExtension
  reimportClassMap :
    L₁.toSlotProfile.hasReimportClass ↔ L₂.toSlotProfile.hasReimportClass
  annotationFunctorMap :
    L₁.toSlotProfile.hasAnnotationFunctor
      ↔ L₂.toSlotProfile.hasAnnotationFunctor

namespace LCELQuasiFunctor

/-- Clause-indexed access to the six biconditional components. -/
def clauseMap {L₁ L₂ : FormalLCELInstance}
    (F : LCELQuasiFunctor L₁ L₂) :
    ∀ c : LCELClause,
      ClauseHolds L₁.toSlotProfile c ↔ ClauseHolds L₂.toSlotProfile c
  | .baseSystem => F.baseSystemMap
  | .boundary => F.boundaryMap
  | .externalLicense => F.externalLicenseMap
  | .licensedExtension => F.licensedExtensionMap
  | .reimportClass => F.reimportClassMap
  | .annotationFunctor => F.annotationFunctorMap

/-- A quasi-functor between LCEL instances is a stagewise parallelism of their
slot profiles. -/
theorem stagewise_equivalent
    {L₁ L₂ : FormalLCELInstance}
    (F : LCELQuasiFunctor L₁ L₂) :
    StagewiseLCELEquivalent L₁.toSlotProfile L₂.toSlotProfile := by
  intro c
  exact F.clauseMap c

/-- Quasi-functors transport LCEL realization from source to target. -/
theorem transports_realization
    {L₁ L₂ : FormalLCELInstance}
    (F : LCELQuasiFunctor L₁ L₂)
    (hL₁ : RealizesLCELSchema L₁.toSlotProfile) :
    RealizesLCELSchema L₂.toSlotProfile :=
  F.stagewise_equivalent.preserves_realization hL₁

/-- Identity quasi-functor on any LCEL instance. -/
def id (L : FormalLCELInstance) : LCELQuasiFunctor L L where
  baseSystemMap := Iff.rfl
  boundaryMap := Iff.rfl
  externalLicenseMap := Iff.rfl
  licensedExtensionMap := Iff.rfl
  reimportClassMap := Iff.rfl
  annotationFunctorMap := Iff.rfl

/-- Reverse quasi-functor: invert each clause biconditional. -/
def symm {L₁ L₂ : FormalLCELInstance}
    (F : LCELQuasiFunctor L₁ L₂) :
    LCELQuasiFunctor L₂ L₁ where
  baseSystemMap := F.baseSystemMap.symm
  boundaryMap := F.boundaryMap.symm
  externalLicenseMap := F.externalLicenseMap.symm
  licensedExtensionMap := F.licensedExtensionMap.symm
  reimportClassMap := F.reimportClassMap.symm
  annotationFunctorMap := F.annotationFunctorMap.symm

/-- Composition of two quasi-functors. -/
def comp {L₁ L₂ L₃ : FormalLCELInstance}
    (G : LCELQuasiFunctor L₂ L₃) (F : LCELQuasiFunctor L₁ L₂) :
    LCELQuasiFunctor L₁ L₃ where
  baseSystemMap := F.baseSystemMap.trans G.baseSystemMap
  boundaryMap := F.boundaryMap.trans G.boundaryMap
  externalLicenseMap := F.externalLicenseMap.trans G.externalLicenseMap
  licensedExtensionMap := F.licensedExtensionMap.trans G.licensedExtensionMap
  reimportClassMap := F.reimportClassMap.trans G.reimportClassMap
  annotationFunctorMap := F.annotationFunctorMap.trans G.annotationFunctorMap

end LCELQuasiFunctor

/-- Honest artifact-facing comparison witness between two formal LCEL instances.

This packages exactly the three ingredients currently available in the artifact:

1. stagewise equivalence of the underlying comparison profiles;
2. equivalence of the explicit external-license slot; and
3. equivalence of the explicit reimport-class slot. -/
structure LCELComparisonWitness (L₁ L₂ : FormalLCELInstance) : Type where
  comparisonStagewise :
    StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape
  externalLicenseEquivalent :
    L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness
  reimportClassEquivalent :
    L₁.reimportClassWitness ↔ L₂.reimportClassWitness

private theorem baseSystem_slot_equivalent_of_comparison_shapes
    {L₁ L₂ : FormalLCELInstance}
    (hShape : StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape) :
    L₁.toSlotProfile.hasBaseSystem ↔ L₂.toSlotProfile.hasBaseSystem := by
  have hLeft :
      L₁.toSlotProfile.hasBaseSystem ↔ L₁.comparison.profile.shape.hasBaseSystem := by
    constructor
    · intro h
      have hSlot : L₁.comparison.baseSemantics.hasBaseSystem := by
        simpa [FormalLCELInstance.toSlotProfile] using h
      have hEq :
          L₁.comparison.profile.shape.hasBaseSystem =
            L₁.comparison.baseSemantics.hasBaseSystem := by
        rw [L₁.comparison.profileShape]
      exact hEq.symm ▸ hSlot
    · intro h
      have hEq :
          L₁.comparison.profile.shape.hasBaseSystem =
            L₁.comparison.baseSemantics.hasBaseSystem := by
        rw [L₁.comparison.profileShape]
      have hSlot : L₁.comparison.baseSemantics.hasBaseSystem := hEq ▸ h
      simpa [FormalLCELInstance.toSlotProfile] using hSlot
  have hRight :
      L₂.toSlotProfile.hasBaseSystem ↔ L₂.comparison.profile.shape.hasBaseSystem := by
    constructor
    · intro h
      have hSlot : L₂.comparison.baseSemantics.hasBaseSystem := by
        simpa [FormalLCELInstance.toSlotProfile] using h
      have hEq :
          L₂.comparison.profile.shape.hasBaseSystem =
            L₂.comparison.baseSemantics.hasBaseSystem := by
        rw [L₂.comparison.profileShape]
      exact hEq.symm ▸ hSlot
    · intro h
      have hEq :
          L₂.comparison.profile.shape.hasBaseSystem =
            L₂.comparison.baseSemantics.hasBaseSystem := by
        rw [L₂.comparison.profileShape]
      have hSlot : L₂.comparison.baseSemantics.hasBaseSystem := hEq ▸ h
      simpa [FormalLCELInstance.toSlotProfile] using hSlot
  exact hLeft.trans ((hShape .baseSystem).trans hRight.symm)

private theorem boundary_slot_equivalent_of_comparison_shapes
    {L₁ L₂ : FormalLCELInstance}
    (hShape : StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape) :
    L₁.toSlotProfile.hasBoundary ↔ L₂.toSlotProfile.hasBoundary := by
  have hLeft :
      L₁.toSlotProfile.hasBoundary ↔
        L₁.comparison.profile.shape.hasSelfObstruction := by
    change
      L₁.boundaryObject.realized ↔
        L₁.comparison.profile.shape.hasSelfObstruction
    exact L₁.boundaryMatchesProfile
  have hRight :
      L₂.toSlotProfile.hasBoundary ↔
        L₂.comparison.profile.shape.hasSelfObstruction := by
    change
      L₂.boundaryObject.realized ↔
        L₂.comparison.profile.shape.hasSelfObstruction
    exact L₂.boundaryMatchesProfile
  exact hLeft.trans ((hShape .selfObstruction).trans hRight.symm)

private theorem licensedExtension_slot_equivalent_of_comparison_shapes
    {L₁ L₂ : FormalLCELInstance}
    (hShape : StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape) :
    L₁.toSlotProfile.hasLicensedExtension ↔
      L₂.toSlotProfile.hasLicensedExtension := by
  have hLeft :
      L₁.toSlotProfile.hasLicensedExtension ↔
        L₁.comparison.profile.shape.hasStrongerFramework := by
    constructor
    · intro h
      have hSlot : L₁.comparison.frameworkSemantics.frameworkAvailable := by
        simpa [FormalLCELInstance.toSlotProfile] using h
      have hEq :
          L₁.comparison.profile.shape.hasStrongerFramework =
            L₁.comparison.frameworkSemantics.frameworkAvailable := by
        rw [L₁.comparison.profileShape]
      exact hEq.symm ▸ hSlot
    · intro h
      have hEq :
          L₁.comparison.profile.shape.hasStrongerFramework =
            L₁.comparison.frameworkSemantics.frameworkAvailable := by
        rw [L₁.comparison.profileShape]
      have hSlot : L₁.comparison.frameworkSemantics.frameworkAvailable := hEq ▸ h
      simpa [FormalLCELInstance.toSlotProfile] using hSlot
  have hRight :
      L₂.toSlotProfile.hasLicensedExtension ↔
        L₂.comparison.profile.shape.hasStrongerFramework := by
    constructor
    · intro h
      have hSlot : L₂.comparison.frameworkSemantics.frameworkAvailable := by
        simpa [FormalLCELInstance.toSlotProfile] using h
      have hEq :
          L₂.comparison.profile.shape.hasStrongerFramework =
            L₂.comparison.frameworkSemantics.frameworkAvailable := by
        rw [L₂.comparison.profileShape]
      exact hEq.symm ▸ hSlot
    · intro h
      have hEq :
          L₂.comparison.profile.shape.hasStrongerFramework =
            L₂.comparison.frameworkSemantics.frameworkAvailable := by
        rw [L₂.comparison.profileShape]
      have hSlot : L₂.comparison.frameworkSemantics.frameworkAvailable := hEq ▸ h
      simpa [FormalLCELInstance.toSlotProfile] using hSlot
  exact hLeft.trans ((hShape .strongerFramework).trans hRight.symm)

private theorem annotationFunctor_slot_equivalent_of_comparison_shapes
    {L₁ L₂ : FormalLCELInstance}
    (hShape : StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape) :
    L₁.toSlotProfile.hasAnnotationFunctor ↔
      L₂.toSlotProfile.hasAnnotationFunctor := by
  have hLeft :
      L₁.toSlotProfile.hasAnnotationFunctor ↔
        L₁.comparison.profile.shape.licensedReimport := by
    change
      L₁.annotationFunctor.realized ↔
        L₁.comparison.profile.shape.licensedReimport
    exact L₁.annotationMatchesProfile
  have hRight :
      L₂.toSlotProfile.hasAnnotationFunctor ↔
        L₂.comparison.profile.shape.licensedReimport := by
    change
      L₂.annotationFunctor.realized ↔
        L₂.comparison.profile.shape.licensedReimport
    exact L₂.annotationMatchesProfile
  exact hLeft.trans ((hShape .licensedReimport).trans hRight.symm)

/-- Honest construction principle for an LCEL quasi-functor.

The artifact currently needs three ingredients:

1. stagewise equivalence of the underlying comparison profiles;
2. equivalence of the explicit external-license slot; and
3. equivalence of the explicit reimport-class slot.

That is the real reusable core available today. -/
def lcelQuasiFunctor_of_comparison_and_slots
    {L₁ L₂ : FormalLCELInstance}
    (hShape : StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape)
    (hLicense :
      L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness)
    (hReimport :
      L₁.reimportClassWitness ↔ L₂.reimportClassWitness) :
    LCELQuasiFunctor L₁ L₂ where
  baseSystemMap := baseSystem_slot_equivalent_of_comparison_shapes hShape
  boundaryMap := boundary_slot_equivalent_of_comparison_shapes hShape
  externalLicenseMap := hLicense
  licensedExtensionMap :=
    licensedExtension_slot_equivalent_of_comparison_shapes hShape
  reimportClassMap := hReimport
  annotationFunctorMap :=
    annotationFunctor_slot_equivalent_of_comparison_shapes hShape

/-- Repackage an honest LCEL comparison witness as a quasi-functor. -/
def lcelQuasiFunctor_of_comparisonWitness
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELComparisonWitness L₁ L₂) :
    LCELQuasiFunctor L₁ L₂ :=
  lcelQuasiFunctor_of_comparison_and_slots
    W.comparisonStagewise
    W.externalLicenseEquivalent
    W.reimportClassEquivalent

/-- Artifact-facing LCEL structural identity: a quasi-functor exists once the
comparison-profile stages and the two explicit extra LCEL slots are aligned. -/
theorem lcel_structural_identity
    {L₁ L₂ : FormalLCELInstance}
    (hShape : StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape)
    (hLicense :
      L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness)
    (hReimport :
      L₁.reimportClassWitness ↔ L₂.reimportClassWitness) :
    Nonempty (LCELQuasiFunctor L₁ L₂) :=
  ⟨lcelQuasiFunctor_of_comparison_and_slots hShape hLicense hReimport⟩

/-- Bidirectional form of the artifact-facing LCEL structural-identity
construction. -/
theorem lcel_structural_identity_bidirectional
    {L₁ L₂ : FormalLCELInstance}
    (hShape : StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape)
    (hLicense :
      L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness)
    (hReimport :
      L₁.reimportClassWitness ↔ L₂.reimportClassWitness) :
    Nonempty (LCELQuasiFunctor L₁ L₂) ∧ Nonempty (LCELQuasiFunctor L₂ L₁) := by
  refine ⟨lcel_structural_identity hShape hLicense hReimport, ?_⟩
  exact lcel_structural_identity (StagewiseEquivalent.symm hShape) hLicense.symm hReimport.symm

namespace LCELComparisonWitness

/-- Build the corresponding quasi-functor from an honest comparison witness. -/
def toQuasiFunctor
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELComparisonWitness L₁ L₂) :
    LCELQuasiFunctor L₁ L₂ :=
  lcelQuasiFunctor_of_comparisonWitness W

/-- Any honest LCEL comparison witness yields artifact-facing structural identity. -/
theorem structural_identity
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELComparisonWitness L₁ L₂) :
    Nonempty (LCELQuasiFunctor L₁ L₂) :=
  ⟨W.toQuasiFunctor⟩

/-- Bidirectional form obtained by reversing the witness. -/
def symm
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELComparisonWitness L₁ L₂) :
    LCELComparisonWitness L₂ L₁ where
  comparisonStagewise := StagewiseEquivalent.symm W.comparisonStagewise
  externalLicenseEquivalent := W.externalLicenseEquivalent.symm
  reimportClassEquivalent := W.reimportClassEquivalent.symm

/-- Honest bidirectional structural identity from a single comparison witness. -/
theorem structural_identity_bidirectional
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELComparisonWitness L₁ L₂) :
    Nonempty (LCELQuasiFunctor L₁ L₂) ∧ Nonempty (LCELQuasiFunctor L₂ L₁) :=
  ⟨W.structural_identity, W.symm.structural_identity⟩

/-- Comparison witnesses induce stagewise equivalence of the six LCEL slot
profiles themselves. -/
theorem stagewise_slots
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELComparisonWitness L₁ L₂) :
    StagewiseLCELEquivalent L₁.toSlotProfile L₂.toSlotProfile :=
  W.toQuasiFunctor.stagewise_equivalent

/-- Comparison witnesses transport LCEL schema realization from left to right. -/
theorem transports_realization
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELComparisonWitness L₁ L₂)
    (hL₁ : RealizesLCELSchema L₁.toSlotProfile) :
    RealizesLCELSchema L₂.toSlotProfile :=
  W.toQuasiFunctor.transports_realization hL₁

end LCELComparisonWitness

/-- Stronger artifact-facing comparison witness between two formal LCEL
instances.

This extends `LCELComparisonWitness` with the current theorem-backed semantic
support surface used to realize the LCEL reversibility and boundary-
factorization packages on canonical instances. It is still conditional, but it
supports more of the paper's LCEL comparison story than slot parallelism alone. -/
structure LCELSemanticComparisonWitness (L₁ L₂ : FormalLCELInstance)
    extends LCELComparisonWitness L₁ L₂ where
  baseLayerSupportEquivalent :
    SemanticBaseLayerSupport L₁ ↔ SemanticBaseLayerSupport L₂
  licenseTransferSupportEquivalent :
    SemanticLicenseTransferSupport L₁ ↔ SemanticLicenseTransferSupport L₂
  reimportTransferSupportEquivalent :
    SemanticReimportTransferSupport L₁ ↔ SemanticReimportTransferSupport L₂

namespace LCELSemanticComparisonWitness

/-- Forget the semantic support fields and recover the slot-level comparison
witness. -/
def toComparisonWitness
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂) :
    LCELComparisonWitness L₁ L₂ :=
  W.toLCELComparisonWitness

/-- Reverse a semantic comparison witness. -/
def symm
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂) :
    LCELSemanticComparisonWitness L₂ L₁ where
  toLCELComparisonWitness := W.toComparisonWitness.symm
  baseLayerSupportEquivalent := W.baseLayerSupportEquivalent.symm
  licenseTransferSupportEquivalent := W.licenseTransferSupportEquivalent.symm
  reimportTransferSupportEquivalent := W.reimportTransferSupportEquivalent.symm

/-- Transport theorem-backed base-layer support across a semantic comparison
witness. -/
theorem transports_semanticBaseLayerSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hBase : SemanticBaseLayerSupport L₁) :
    SemanticBaseLayerSupport L₂ :=
  (W.baseLayerSupportEquivalent).1 hBase

/-- Transport theorem-backed license-transfer support across a semantic
comparison witness. -/
theorem transports_semanticLicenseTransferSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hLicense : SemanticLicenseTransferSupport L₁) :
    SemanticLicenseTransferSupport L₂ :=
  (W.licenseTransferSupportEquivalent).1 hLicense

/-- Transport theorem-backed reimport-transfer support across a semantic
comparison witness. -/
theorem transports_semanticReimportTransferSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hReimport : SemanticReimportTransferSupport L₁) :
    SemanticReimportTransferSupport L₂ :=
  (W.reimportTransferSupportEquivalent).1 hReimport

/-- Build the target-side LCEL reversibility-asymmetry package from a source-side
semantic support triple transported across the semantic comparison witness. -/
def transports_semanticReversibilityAsymmetry
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hBase : SemanticBaseLayerSupport L₁)
    (hLicense : SemanticLicenseTransferSupport L₁)
    (hReimport : SemanticReimportTransferSupport L₁) :
    LCELReversibilityAsymmetry L₂ :=
  lcelReversibilityAsymmetry_of_semanticSupports
    (W.transports_semanticBaseLayerSupport hBase)
    (W.transports_semanticLicenseTransferSupport hLicense)
    (W.transports_semanticReimportTransferSupport hReimport)

/-- Build the target-side LCEL boundary-factorization package from source-side
semantic support transported across the semantic comparison witness. -/
def transports_semanticBoundaryFactorization
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hVisible : SemanticReimportTransferSupport L₁)
    (hSensitive : SemanticLicenseTransferSupport L₁) :
    LCELBoundaryFactorization L₂ :=
  lcelBoundaryFactorization_of_semanticSupports
    (W.transports_semanticReimportTransferSupport hVisible)
    (W.transports_semanticLicenseTransferSupport hSensitive)

/-- Rebuild a target-side proof-carrying base-support record from a source-side
base-support record.

The target-side record is reconstructed from the transported semantic
base-layer support together with the target instance's own designated internal
proof witness and designated boundary witness. -/
def transports_baseReversibilitySupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (S : BaseReversibilitySupport L₁) :
    BaseReversibilitySupport L₂ :=
  baseReversibilitySupport_of_semanticBase
    (W.transports_semanticBaseLayerSupport S.supportsSemanticBase)

/-- Rebuild a target-side proof-carrying license-support record from a
source-side license-support record.

The target-side record is reconstructed from the transported obstruction-to-
reflection transfer together with the target instance's own designated
reflection/license data. -/
def transports_licenseIrreversibilitySupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (S : LicenseIrreversibilitySupport L₁) :
    LicenseIrreversibilitySupport L₂ :=
  licenseIrreversibilitySupport_of_semanticTransfer
    (W.transports_semanticLicenseTransferSupport S.supportsSemanticTransfer)

/-- Rebuild a target-side proof-carrying reimport-support record from a
source-side reimport-support record.

The target-side record is reconstructed from the transported reflection-to-
reimport transfer together with the target instance's own designated reimport
and annotation witnesses. -/
def transports_reimportReversibilitySupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (S : ReimportReversibilitySupport L₁) :
    ReimportReversibilitySupport L₂ :=
  reimportReversibilitySupport_of_semanticTransfer
    (W.transports_semanticReimportTransferSupport S.supportsSemanticTransfer)

/-- Rebuild a target-side proof-carrying boundary-factorization support record
from a source-side one by transporting its visible and sensitive support layers. -/
def transports_boundaryFactorizationSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (S : BoundaryFactorizationSupport L₁) :
    BoundaryFactorizationSupport L₂ :=
  boundaryFactorizationSupport_of_supports
    (W.transports_reimportReversibilitySupport S.visibleSupport)
    (W.transports_licenseIrreversibilitySupport S.sensitiveSupport)

/-- Build the target-side LCEL reversibility-asymmetry package from source-side
proof-carrying support records transported across the semantic comparison
witness. -/
def transports_reversibilityAsymmetryFromSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hBase : BaseReversibilitySupport L₁)
    (hLicense : LicenseIrreversibilitySupport L₁)
    (hReimport : ReimportReversibilitySupport L₁) :
    LCELReversibilityAsymmetry L₂ :=
  lcelReversibilityAsymmetry_of_strongerSupports
    (W.transports_baseReversibilitySupport hBase)
    (W.transports_licenseIrreversibilitySupport hLicense)
    (W.transports_reimportReversibilitySupport hReimport)

/-- Build the target-side LCEL boundary-factorization package from a
source-side proof-carrying boundary-factorization support record transported
across the semantic comparison witness. -/
def transports_boundaryFactorizationFromSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hSupport : BoundaryFactorizationSupport L₁) :
    LCELBoundaryFactorization L₂ :=
  lcelBoundaryFactorization_of_strongerSupport
    (W.transports_boundaryFactorizationSupport hSupport)

/-- Semantic comparison witnesses still transport LCEL schema realization, via
their underlying slot-level comparison witness. -/
theorem transports_realization
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSemanticComparisonWitness L₁ L₂)
    (hL₁ : RealizesLCELSchema L₁.toSlotProfile) :
    RealizesLCELSchema L₂.toSlotProfile :=
  W.toComparisonWitness.transports_realization hL₁

end LCELSemanticComparisonWitness

private theorem baseReversibilitySupport_supported
    {L : FormalLCELInstance}
    (S : BaseReversibilitySupport L) :
    BaseReversibilitySupport.supported S :=
  ⟨S.internalSentenceProved, S.boundaryRealized⟩

private theorem licenseIrreversibilitySupport_supported
    {L : FormalLCELInstance}
    (S : LicenseIrreversibilitySupport L) :
    LicenseIrreversibilitySupport.supported S :=
  ⟨S.strongerFrameworkReflectsBlocked, S.externalLicenseHolds,
    S.blockedNotProvable, S.blockedTrue, S.blockedLicensedAdmission⟩

private theorem reimportReversibilitySupport_supported
    {L : FormalLCELInstance}
    (S : ReimportReversibilitySupport L) :
    ReimportReversibilitySupport.supported S :=
  ⟨S.witnessCertifiesBlocked, S.reimportClassHolds, S.annotationRealized,
    S.witnessCertifiesImported, S.importedTrue⟩

private theorem boundaryFactorizationSupport_supported
    {L : FormalLCELInstance}
    (S : BoundaryFactorizationSupport L) :
    BoundaryFactorizationSupport.supported S := by
  refine ⟨reimportReversibilitySupport_supported S.visibleSupport,
    licenseIrreversibilitySupport_supported S.sensitiveSupport,
    S.boundaryRealized⟩

/-- Support-comparison witness between two formal LCEL instances.

This extends the semantic comparison witness by packaging the current
proof-carrying substrate support records on both sides together with
equivalence data for their `supported` propositions. -/
structure LCELSupportComparisonWitness (L₁ L₂ : FormalLCELInstance)
    extends LCELSemanticComparisonWitness L₁ L₂ where
  sourceBaseSupport : BaseReversibilitySupport L₁
  targetBaseSupport : BaseReversibilitySupport L₂
  sourceLicenseSupport : LicenseIrreversibilitySupport L₁
  targetLicenseSupport : LicenseIrreversibilitySupport L₂
  sourceReimportSupport : ReimportReversibilitySupport L₁
  targetReimportSupport : ReimportReversibilitySupport L₂
  sourceBoundarySupport : BoundaryFactorizationSupport L₁
  targetBoundarySupport : BoundaryFactorizationSupport L₂
  baseSupportEquivalent :
    BaseReversibilitySupport.supported sourceBaseSupport
      ↔ BaseReversibilitySupport.supported targetBaseSupport
  licenseSupportEquivalent :
    LicenseIrreversibilitySupport.supported sourceLicenseSupport
      ↔ LicenseIrreversibilitySupport.supported targetLicenseSupport
  reimportSupportEquivalent :
    ReimportReversibilitySupport.supported sourceReimportSupport
      ↔ ReimportReversibilitySupport.supported targetReimportSupport
  boundarySupportEquivalent :
    BoundaryFactorizationSupport.supported sourceBoundarySupport
      ↔ BoundaryFactorizationSupport.supported targetBoundarySupport

namespace LCELSupportComparisonWitness

/-- Forget the support-record fields and recover the semantic comparison
witness. -/
def toSemanticComparisonWitness
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    LCELSemanticComparisonWitness L₁ L₂ :=
  W.toLCELSemanticComparisonWitness

/-- Reverse a support comparison witness. -/
def symm
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    LCELSupportComparisonWitness L₂ L₁ where
  toLCELSemanticComparisonWitness := W.toSemanticComparisonWitness.symm
  sourceBaseSupport := W.targetBaseSupport
  targetBaseSupport := W.sourceBaseSupport
  sourceLicenseSupport := W.targetLicenseSupport
  targetLicenseSupport := W.sourceLicenseSupport
  sourceReimportSupport := W.targetReimportSupport
  targetReimportSupport := W.sourceReimportSupport
  sourceBoundarySupport := W.targetBoundarySupport
  targetBoundarySupport := W.sourceBoundarySupport
  baseSupportEquivalent := W.baseSupportEquivalent.symm
  licenseSupportEquivalent := W.licenseSupportEquivalent.symm
  reimportSupportEquivalent := W.reimportSupportEquivalent.symm
  boundarySupportEquivalent := W.boundarySupportEquivalent.symm

/-- The left-hand external-license slot is supported by the packaged stronger
license-side support record. -/
theorem sourceExternalLicense
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    L₁.externalLicenseWitness :=
  W.sourceLicenseSupport.externalLicenseHolds

/-- The right-hand external-license slot is supported by the packaged stronger
license-side support record. -/
theorem targetExternalLicense
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    L₂.externalLicenseWitness :=
  W.targetLicenseSupport.externalLicenseHolds

/-- The left-hand reimport-class slot is supported by the packaged stronger
reimport-side support record. -/
theorem sourceReimportClass
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    L₁.reimportClassWitness :=
  W.sourceReimportSupport.reimportClassHolds

/-- The right-hand reimport-class slot is supported by the packaged stronger
reimport-side support record. -/
theorem targetReimportClass
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    L₂.reimportClassWitness :=
  W.targetReimportSupport.reimportClassHolds

/-- Transport the left-hand stronger base-support record to the right-hand
instance using the underlying semantic comparison witness. -/
def transports_sourceBaseSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    BaseReversibilitySupport L₂ :=
  W.toSemanticComparisonWitness.transports_baseReversibilitySupport
    W.sourceBaseSupport

/-- Transport the left-hand stronger license-support record to the right-hand
instance using the underlying semantic comparison witness. -/
def transports_sourceLicenseSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    LicenseIrreversibilitySupport L₂ :=
  W.toSemanticComparisonWitness.transports_licenseIrreversibilitySupport
    W.sourceLicenseSupport

/-- Transport the left-hand stronger reimport-support record to the right-hand
instance using the underlying semantic comparison witness. -/
def transports_sourceReimportSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    ReimportReversibilitySupport L₂ :=
  W.toSemanticComparisonWitness.transports_reimportReversibilitySupport
    W.sourceReimportSupport

/-- Transport the left-hand stronger boundary-factorization support record to the
right-hand instance using the underlying semantic comparison witness. -/
def transports_sourceBoundarySupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    BoundaryFactorizationSupport L₂ :=
  W.toSemanticComparisonWitness.transports_boundaryFactorizationSupport
    W.sourceBoundarySupport

/-- Build the right-hand LCEL reversibility-asymmetry package from the left-hand
proof-carrying support records. -/
def transports_reversibilityAsymmetryFromSourceSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    LCELReversibilityAsymmetry L₂ :=
  W.toSemanticComparisonWitness.transports_reversibilityAsymmetryFromSupport
    W.sourceBaseSupport
    W.sourceLicenseSupport
    W.sourceReimportSupport

/-- Build the right-hand LCEL boundary-factorization package from the left-hand
proof-carrying boundary-factorization support record. -/
def transports_boundaryFactorizationFromSourceSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    LCELBoundaryFactorization L₂ :=
  W.toSemanticComparisonWitness.transports_boundaryFactorizationFromSupport
    W.sourceBoundarySupport

/-- Build the left-hand LCEL reversibility-asymmetry package from the right-hand
proof-carrying support records by reversing the witness. -/
def transports_reversibilityAsymmetryFromTargetSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    LCELReversibilityAsymmetry L₁ :=
  W.symm.transports_reversibilityAsymmetryFromSourceSupport

/-- Build the left-hand LCEL boundary-factorization package from the right-hand
proof-carrying boundary-factorization support record by reversing the witness. -/
def transports_boundaryFactorizationFromTargetSupport
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELSupportComparisonWitness L₁ L₂) :
    LCELBoundaryFactorization L₁ :=
  W.symm.transports_boundaryFactorizationFromSourceSupport

end LCELSupportComparisonWitness

private theorem godel_benchmark_comparison_stagewise_equivalent :
    StagewiseEquivalent
      godel1931LCELInstance.comparison.profile.shape
      benchmarkTransportLCELInstance.comparison.profile.shape := by
  refine stagewise_equivalent_of_common_dp ?_ ?_
  exact godel1931FormalExternalClassicalComparison_supported.2.2
  exact benchmarkTransportFormalExternalClassicalComparison_supported.2.2

private theorem godel_benchmark_externalLicense_equivalent :
    godel1931LCELInstance.externalLicenseWitness
      ↔ benchmarkTransportLCELInstance.externalLicenseWitness := by
  exact iff_of_true
    godel1931LicenseIrreversibilitySupport.externalLicenseHolds
    benchmarkTransportLicenseIrreversibilitySupport.externalLicenseHolds

private theorem godel_benchmark_reimportClass_equivalent :
    godel1931LCELInstance.reimportClassWitness
      ↔ benchmarkTransportLCELInstance.reimportClassWitness := by
  exact iff_of_true
    godel1931ReimportReversibilitySupport.reimportClassHolds
    benchmarkTransportReimportReversibilitySupport.reimportClassHolds

private theorem godel_benchmark_semanticBaseLayerSupport_equivalent :
    SemanticBaseLayerSupport godel1931LCELInstance
      ↔ SemanticBaseLayerSupport benchmarkTransportLCELInstance := by
  exact iff_of_true
    (BaseReversibilitySupport.supportsSemanticBase
      godel1931BaseReversibilitySupport)
    (BaseReversibilitySupport.supportsSemanticBase
      benchmarkTransportBaseReversibilitySupport)

private theorem godel_benchmark_semanticLicenseTransferSupport_equivalent :
    SemanticLicenseTransferSupport godel1931LCELInstance
      ↔ SemanticLicenseTransferSupport benchmarkTransportLCELInstance := by
  exact iff_of_true
    (LicenseIrreversibilitySupport.supportsSemanticTransfer
      godel1931LicenseIrreversibilitySupport)
    (LicenseIrreversibilitySupport.supportsSemanticTransfer
      benchmarkTransportLicenseIrreversibilitySupport)

private theorem godel_benchmark_semanticReimportTransferSupport_equivalent :
    SemanticReimportTransferSupport godel1931LCELInstance
      ↔ SemanticReimportTransferSupport benchmarkTransportLCELInstance := by
  exact iff_of_true
    (ReimportReversibilitySupport.supportsSemanticTransfer
      godel1931ReimportReversibilitySupport)
    (ReimportReversibilitySupport.supportsSemanticTransfer
      benchmarkTransportReimportReversibilitySupport)

/-- Honest comparison witness between the canonical Gödel-side and
benchmark/DP-side LCEL instances. -/
def godel_benchmark_lcelComparisonWitness :
    LCELComparisonWitness godel1931LCELInstance benchmarkTransportLCELInstance where
  comparisonStagewise := godel_benchmark_comparison_stagewise_equivalent
  externalLicenseEquivalent := godel_benchmark_externalLicense_equivalent
  reimportClassEquivalent := godel_benchmark_reimportClass_equivalent

/-- Stronger semantic comparison witness between the canonical Gödel-side and
benchmark/DP-side LCEL instances. This packages both slot parallelism and the
current theorem-backed semantic support surface used by the LCEL substrate
packages. -/
def godel_benchmark_lcelSemanticComparisonWitness :
    LCELSemanticComparisonWitness
      godel1931LCELInstance benchmarkTransportLCELInstance where
  toLCELComparisonWitness := godel_benchmark_lcelComparisonWitness
  baseLayerSupportEquivalent := godel_benchmark_semanticBaseLayerSupport_equivalent
  licenseTransferSupportEquivalent :=
    godel_benchmark_semanticLicenseTransferSupport_equivalent
  reimportTransferSupportEquivalent :=
    godel_benchmark_semanticReimportTransferSupport_equivalent

/-- Strongest current comparison witness between the canonical Gödel-side and
benchmark-side LCEL instances. This packages slot-level comparison, semantic
support comparison, and the proof-carrying substrate support records on both
sides. -/
def godel_benchmark_lcelSupportComparisonWitness :
    LCELSupportComparisonWitness
      godel1931LCELInstance benchmarkTransportLCELInstance where
  toLCELSemanticComparisonWitness := godel_benchmark_lcelSemanticComparisonWitness
  sourceBaseSupport := godel1931BaseReversibilitySupport
  targetBaseSupport := benchmarkTransportBaseReversibilitySupport
  sourceLicenseSupport := godel1931LicenseIrreversibilitySupport
  targetLicenseSupport := benchmarkTransportLicenseIrreversibilitySupport
  sourceReimportSupport := godel1931ReimportReversibilitySupport
  targetReimportSupport := benchmarkTransportReimportReversibilitySupport
  sourceBoundarySupport := godel1931BoundaryFactorizationSupport
  targetBoundarySupport := benchmarkTransportBoundaryFactorizationSupport
  baseSupportEquivalent := iff_of_true
    (baseReversibilitySupport_supported godel1931BaseReversibilitySupport)
    (baseReversibilitySupport_supported benchmarkTransportBaseReversibilitySupport)
  licenseSupportEquivalent := iff_of_true
    (licenseIrreversibilitySupport_supported
      godel1931LicenseIrreversibilitySupport)
    (licenseIrreversibilitySupport_supported
      benchmarkTransportLicenseIrreversibilitySupport)
  reimportSupportEquivalent := iff_of_true
    (reimportReversibilitySupport_supported
      godel1931ReimportReversibilitySupport)
    (reimportReversibilitySupport_supported
      benchmarkTransportReimportReversibilitySupport)
  boundarySupportEquivalent := iff_of_true
    (boundaryFactorizationSupport_supported
      godel1931BoundaryFactorizationSupport)
    (boundaryFactorizationSupport_supported
      benchmarkTransportBoundaryFactorizationSupport)

/-- The canonical LCEL slot profiles are stagewise equivalent in the current
artifact-facing sense. -/
theorem godel_benchmark_lcel_stagewise_slots :
    StagewiseLCELEquivalent
      godel1931LCELInstance.toSlotProfile
      benchmarkTransportLCELInstance.toSlotProfile :=
  godel_benchmark_lcelComparisonWitness.stagewise_slots

/-- Transport Gödel-side LCEL realization to the benchmark-side canonical LCEL
instance. -/
theorem godel_to_benchmark_lcel_realization :
    RealizesLCELSchema godel1931LCELInstance.toSlotProfile →
      RealizesLCELSchema benchmarkTransportLCELInstance.toSlotProfile :=
  godel_benchmark_lcelComparisonWitness.transports_realization

/-- Transport benchmark-side LCEL realization back to the Gödel-side canonical
LCEL instance. -/
theorem benchmark_to_godel_lcel_realization :
    RealizesLCELSchema benchmarkTransportLCELInstance.toSlotProfile →
      RealizesLCELSchema godel1931LCELInstance.toSlotProfile :=
  godel_benchmark_lcelComparisonWitness.symm.transports_realization

/-- The current semantic-support reading of LCEL base reversibility is
clausewise equivalent on the canonical Gödel-side and benchmark-side
instances. -/
theorem godel_benchmark_lcel_baseReversible_equivalent :
    godel1931LCELReversibilityAsymmetry.baseReversible
      ↔ benchmarkTransportLCELReversibilityAsymmetry.baseReversible := by
  simpa using godel_benchmark_semanticBaseLayerSupport_equivalent

/-- The current semantic-support reading of LCEL license irreversibility is
clausewise equivalent on the canonical Gödel-side and benchmark-side
instances. -/
theorem godel_benchmark_lcel_licenseIrreversible_equivalent :
    godel1931LCELReversibilityAsymmetry.licenseIrreversible
      ↔ benchmarkTransportLCELReversibilityAsymmetry.licenseIrreversible := by
  simpa using godel_benchmark_semanticLicenseTransferSupport_equivalent

/-- The current semantic-support reading of LCEL reimport reversibility is
clausewise equivalent on the canonical Gödel-side and benchmark-side
instances. -/
theorem godel_benchmark_lcel_reimportReversible_equivalent :
    godel1931LCELReversibilityAsymmetry.reimportReversibleOnReimportClass
      ↔ benchmarkTransportLCELReversibilityAsymmetry.reimportReversibleOnReimportClass := by
  simpa using godel_benchmark_semanticReimportTransferSupport_equivalent

/-- The current semantic-support reading of the reversible LCEL projection is
clausewise equivalent on the canonical Gödel-side and benchmark-side
instances. -/
theorem godel_benchmark_lcel_reversibleProjection_equivalent :
    godel1931LCELBoundaryFactorization.hasReversibleProjection
      ↔ benchmarkTransportLCELBoundaryFactorization.hasReversibleProjection := by
  simpa using godel_benchmark_semanticReimportTransferSupport_equivalent

/-- The current semantic-support reading of the irreversible LCEL quotient is
clausewise equivalent on the canonical Gödel-side and benchmark-side
instances. -/
theorem godel_benchmark_lcel_irreversibleQuotient_equivalent :
    godel1931LCELBoundaryFactorization.hasIrreversibleQuotient
      ↔ benchmarkTransportLCELBoundaryFactorization.hasIrreversibleQuotient := by
  simpa using godel_benchmark_semanticLicenseTransferSupport_equivalent

/-- The current semantic-support reading of LCEL boundary sensitivity is
clausewise equivalent on the canonical Gödel-side and benchmark-side
instances. -/
theorem godel_benchmark_lcel_boundarySensitivity_equivalent :
    godel1931LCELBoundaryFactorization.boundarySensitiveToIrreversible
      ↔ benchmarkTransportLCELBoundaryFactorization.boundarySensitiveToIrreversible := by
  simpa using godel_benchmark_semanticLicenseTransferSupport_equivalent

/-- Rebuild the benchmark-side LCEL reversibility-asymmetry package by
transporting the current semantic support surface from the Gödel side across the
stronger semantic comparison witness. -/
def godel_to_benchmark_lcelReversibilityAsymmetry_via_semanticComparison :
    LCELReversibilityAsymmetry benchmarkTransportLCELInstance :=
  godel_benchmark_lcelSemanticComparisonWitness.transports_semanticReversibilityAsymmetry
    godel1931_semanticBaseLayerSupport
    godel1931_semanticLicenseTransferSupport
    godel1931_semanticReimportTransferSupport

/-- Rebuild the Gödel-side LCEL reversibility-asymmetry package by transporting
the current semantic support surface from the benchmark side across the stronger
semantic comparison witness. -/
def benchmark_to_godel_lcelReversibilityAsymmetry_via_semanticComparison :
    LCELReversibilityAsymmetry godel1931LCELInstance :=
  godel_benchmark_lcelSemanticComparisonWitness.symm.transports_semanticReversibilityAsymmetry
    benchmarkTransport_semanticBaseLayerSupport
    benchmarkTransport_semanticLicenseTransferSupport
    benchmarkTransport_semanticReimportTransferSupport

/-- Rebuild the benchmark-side LCEL boundary-factorization package by
transporting the current semantic support surface from the Gödel side across the
stronger semantic comparison witness. -/
def godel_to_benchmark_lcelBoundaryFactorization_via_semanticComparison :
    LCELBoundaryFactorization benchmarkTransportLCELInstance :=
  godel_benchmark_lcelSemanticComparisonWitness.transports_semanticBoundaryFactorization
    godel1931_semanticReimportTransferSupport
    godel1931_semanticLicenseTransferSupport

/-- Rebuild the Gödel-side LCEL boundary-factorization package by transporting
the current semantic support surface from the benchmark side across the stronger
semantic comparison witness. -/
def benchmark_to_godel_lcelBoundaryFactorization_via_semanticComparison :
    LCELBoundaryFactorization godel1931LCELInstance :=
  godel_benchmark_lcelSemanticComparisonWitness.symm.transports_semanticBoundaryFactorization
    benchmarkTransport_semanticReimportTransferSupport
    benchmarkTransport_semanticLicenseTransferSupport

/-- Rebuild the benchmark-side LCEL reversibility-asymmetry package by
transporting the stronger proof-carrying support records from the Gödel side
across the semantic comparison witness. -/
def godel_to_benchmark_lcelReversibilityAsymmetryFromSupport_via_semanticComparison :
    LCELReversibilityAsymmetry benchmarkTransportLCELInstance :=
  godel_benchmark_lcelSupportComparisonWitness.transports_reversibilityAsymmetryFromSourceSupport

/-- Rebuild the Gödel-side LCEL reversibility-asymmetry package by transporting
the stronger proof-carrying support records from the benchmark side across the
semantic comparison witness. -/
def benchmark_to_godel_lcelReversibilityAsymmetryFromSupport_via_semanticComparison :
    LCELReversibilityAsymmetry godel1931LCELInstance :=
  godel_benchmark_lcelSupportComparisonWitness.transports_reversibilityAsymmetryFromTargetSupport

/-- Rebuild the benchmark-side LCEL boundary-factorization package by
transporting the stronger proof-carrying boundary-factorization support record
from the Gödel side across the semantic comparison witness. -/
def godel_to_benchmark_lcelBoundaryFactorizationFromSupport_via_semanticComparison :
    LCELBoundaryFactorization benchmarkTransportLCELInstance :=
  godel_benchmark_lcelSupportComparisonWitness.transports_boundaryFactorizationFromSourceSupport

/-- Rebuild the Gödel-side LCEL boundary-factorization package by transporting
the stronger proof-carrying boundary-factorization support record from the
benchmark side across the semantic comparison witness. -/
def benchmark_to_godel_lcelBoundaryFactorizationFromSupport_via_semanticComparison :
    LCELBoundaryFactorization godel1931LCELInstance :=
  godel_benchmark_lcelSupportComparisonWitness.transports_boundaryFactorizationFromTargetSupport

/-- Honest comparison witness between the canonical Gödel-side and the native
DP/emitter-side LCEL instances. -/
private theorem godel_dpEmitter_comparison_stagewise_equivalent :
    StagewiseEquivalent
      godel1931LCELInstance.comparison.profile.shape
      dpEmitterLCELInstance.comparison.profile.shape := by
  refine stagewise_equivalent_of_common_dp ?_ ?_
  exact godel1931FormalExternalClassicalComparison_supported.2.2
  exact dpEmitterFormalExternalClassicalComparison_supported.2.2

private theorem godel_dpEmitter_externalLicense_equivalent :
    godel1931LCELInstance.externalLicenseWitness
      ↔ dpEmitterLCELInstance.externalLicenseWitness := by
  exact iff_of_true
    godel1931LicenseIrreversibilitySupport.externalLicenseHolds
    dpEmitterLicenseIrreversibilitySupport.externalLicenseHolds

private theorem godel_dpEmitter_reimportClass_equivalent :
    godel1931LCELInstance.reimportClassWitness
      ↔ dpEmitterLCELInstance.reimportClassWitness := by
  exact iff_of_true
    godel1931ReimportReversibilitySupport.reimportClassHolds
    dpEmitterReimportReversibilitySupport.reimportClassHolds

private theorem godel_dpEmitter_semanticBaseLayerSupport_equivalent :
    SemanticBaseLayerSupport godel1931LCELInstance
      ↔ SemanticBaseLayerSupport dpEmitterLCELInstance := by
  exact iff_of_true
    (BaseReversibilitySupport.supportsSemanticBase
      godel1931BaseReversibilitySupport)
    (BaseReversibilitySupport.supportsSemanticBase
      dpEmitterBaseReversibilitySupport)

private theorem godel_dpEmitter_semanticLicenseTransferSupport_equivalent :
    SemanticLicenseTransferSupport godel1931LCELInstance
      ↔ SemanticLicenseTransferSupport dpEmitterLCELInstance := by
  exact iff_of_true
    (LicenseIrreversibilitySupport.supportsSemanticTransfer
      godel1931LicenseIrreversibilitySupport)
    (LicenseIrreversibilitySupport.supportsSemanticTransfer
      dpEmitterLicenseIrreversibilitySupport)

private theorem godel_dpEmitter_semanticReimportTransferSupport_equivalent :
    SemanticReimportTransferSupport godel1931LCELInstance
      ↔ SemanticReimportTransferSupport dpEmitterLCELInstance := by
  exact iff_of_true
    (ReimportReversibilitySupport.supportsSemanticTransfer
      godel1931ReimportReversibilitySupport)
    (ReimportReversibilitySupport.supportsSemanticTransfer
      dpEmitterReimportReversibilitySupport)

/-- Honest comparison witness between the canonical Gödel-side and the native
DP/emitter-side LCEL instances. -/
def godel_dpEmitter_lcelComparisonWitness :
    LCELComparisonWitness godel1931LCELInstance dpEmitterLCELInstance where
  comparisonStagewise := godel_dpEmitter_comparison_stagewise_equivalent
  externalLicenseEquivalent := godel_dpEmitter_externalLicense_equivalent
  reimportClassEquivalent := godel_dpEmitter_reimportClass_equivalent

/-- Stronger semantic comparison witness between the canonical Gödel-side and
the native DP/emitter-side LCEL instances. -/
def godel_dpEmitter_lcelSemanticComparisonWitness :
    LCELSemanticComparisonWitness
      godel1931LCELInstance dpEmitterLCELInstance where
  toLCELComparisonWitness := godel_dpEmitter_lcelComparisonWitness
  baseLayerSupportEquivalent := godel_dpEmitter_semanticBaseLayerSupport_equivalent
  licenseTransferSupportEquivalent :=
    godel_dpEmitter_semanticLicenseTransferSupport_equivalent
  reimportTransferSupportEquivalent :=
    godel_dpEmitter_semanticReimportTransferSupport_equivalent

/-- Strongest current comparison witness between the canonical Gödel-side and
native DP/emitter-side LCEL instances. This packages slot-level comparison,
semantic support comparison, and the proof-carrying substrate support records on
both sides. -/
def godel_dpEmitter_lcelSupportComparisonWitness :
    LCELSupportComparisonWitness
      godel1931LCELInstance dpEmitterLCELInstance where
  toLCELSemanticComparisonWitness := godel_dpEmitter_lcelSemanticComparisonWitness
  sourceBaseSupport := godel1931BaseReversibilitySupport
  targetBaseSupport := dpEmitterBaseReversibilitySupport
  sourceLicenseSupport := godel1931LicenseIrreversibilitySupport
  targetLicenseSupport := dpEmitterLicenseIrreversibilitySupport
  sourceReimportSupport := godel1931ReimportReversibilitySupport
  targetReimportSupport := dpEmitterReimportReversibilitySupport
  sourceBoundarySupport := godel1931BoundaryFactorizationSupport
  targetBoundarySupport := dpEmitterBoundaryFactorizationSupport
  baseSupportEquivalent := iff_of_true
    (baseReversibilitySupport_supported godel1931BaseReversibilitySupport)
    (baseReversibilitySupport_supported dpEmitterBaseReversibilitySupport)
  licenseSupportEquivalent := iff_of_true
    (licenseIrreversibilitySupport_supported
      godel1931LicenseIrreversibilitySupport)
    (licenseIrreversibilitySupport_supported
      dpEmitterLicenseIrreversibilitySupport)
  reimportSupportEquivalent := iff_of_true
    (reimportReversibilitySupport_supported
      godel1931ReimportReversibilitySupport)
    (reimportReversibilitySupport_supported
      dpEmitterReimportReversibilitySupport)
  boundarySupportEquivalent := iff_of_true
    (boundaryFactorizationSupport_supported
      godel1931BoundaryFactorizationSupport)
    (boundaryFactorizationSupport_supported
      dpEmitterBoundaryFactorizationSupport)

/-- The canonical Gödel-side and native DP/emitter-side LCEL slot profiles are
stagewise equivalent in the current artifact-facing sense. -/
theorem godel_dpEmitter_lcel_stagewise_slots :
    StagewiseLCELEquivalent
      godel1931LCELInstance.toSlotProfile
      dpEmitterLCELInstance.toSlotProfile :=
  godel_dpEmitter_lcelComparisonWitness.stagewise_slots

/-- Transport Gödel-side LCEL realization to the native DP/emitter-side LCEL
instance. -/
theorem godel_to_dpEmitter_lcel_realization :
    RealizesLCELSchema godel1931LCELInstance.toSlotProfile →
      RealizesLCELSchema dpEmitterLCELInstance.toSlotProfile :=
  godel_dpEmitter_lcelComparisonWitness.transports_realization

/-- Transport native DP/emitter-side LCEL realization back to the Gödel-side
LCEL instance. -/
theorem dpEmitter_to_godel_lcel_realization :
    RealizesLCELSchema dpEmitterLCELInstance.toSlotProfile →
      RealizesLCELSchema godel1931LCELInstance.toSlotProfile :=
  godel_dpEmitter_lcelComparisonWitness.symm.transports_realization

/-- The current semantic-support reading of LCEL base reversibility is
clausewise equivalent on the canonical Gödel-side and native DP/emitter-side
instances. -/
theorem godel_dpEmitter_lcel_baseReversible_equivalent :
    godel1931LCELReversibilityAsymmetry.baseReversible
      ↔ dpEmitterLCELReversibilityAsymmetry.baseReversible := by
  simpa using godel_dpEmitter_semanticBaseLayerSupport_equivalent

/-- The current semantic-support reading of LCEL license irreversibility is
clausewise equivalent on the canonical Gödel-side and native DP/emitter-side
instances. -/
theorem godel_dpEmitter_lcel_licenseIrreversible_equivalent :
    godel1931LCELReversibilityAsymmetry.licenseIrreversible
      ↔ dpEmitterLCELReversibilityAsymmetry.licenseIrreversible := by
  simpa using godel_dpEmitter_semanticLicenseTransferSupport_equivalent

/-- The current semantic-support reading of LCEL reimport reversibility is
clausewise equivalent on the canonical Gödel-side and native DP/emitter-side
instances. -/
theorem godel_dpEmitter_lcel_reimportReversible_equivalent :
    godel1931LCELReversibilityAsymmetry.reimportReversibleOnReimportClass
      ↔ dpEmitterLCELReversibilityAsymmetry.reimportReversibleOnReimportClass := by
  simpa using godel_dpEmitter_semanticReimportTransferSupport_equivalent

/-- The current semantic-support reading of the reversible LCEL projection is
clausewise equivalent on the canonical Gödel-side and native DP/emitter-side
instances. -/
theorem godel_dpEmitter_lcel_reversibleProjection_equivalent :
    godel1931LCELBoundaryFactorization.hasReversibleProjection
      ↔ dpEmitterLCELBoundaryFactorization.hasReversibleProjection := by
  simpa using godel_dpEmitter_semanticReimportTransferSupport_equivalent

/-- The current semantic-support reading of the irreversible LCEL quotient is
clausewise equivalent on the canonical Gödel-side and native DP/emitter-side
instances. -/
theorem godel_dpEmitter_lcel_irreversibleQuotient_equivalent :
    godel1931LCELBoundaryFactorization.hasIrreversibleQuotient
      ↔ dpEmitterLCELBoundaryFactorization.hasIrreversibleQuotient := by
  simpa using godel_dpEmitter_semanticLicenseTransferSupport_equivalent

/-- The current semantic-support reading of LCEL boundary sensitivity is
clausewise equivalent on the canonical Gödel-side and native DP/emitter-side
instances. -/
theorem godel_dpEmitter_lcel_boundarySensitivity_equivalent :
    godel1931LCELBoundaryFactorization.boundarySensitiveToIrreversible
      ↔ dpEmitterLCELBoundaryFactorization.boundarySensitiveToIrreversible := by
  simpa using godel_dpEmitter_semanticLicenseTransferSupport_equivalent

/-- Rebuild the native DP/emitter-side LCEL reversibility-asymmetry package by
transporting the current semantic support surface from the Gödel side across the
stronger semantic comparison witness. -/
def godel_to_dpEmitter_lcelReversibilityAsymmetry_via_semanticComparison :
    LCELReversibilityAsymmetry dpEmitterLCELInstance :=
  godel_dpEmitter_lcelSemanticComparisonWitness.transports_semanticReversibilityAsymmetry
    godel1931_semanticBaseLayerSupport
    godel1931_semanticLicenseTransferSupport
    godel1931_semanticReimportTransferSupport

/-- Rebuild the Gödel-side LCEL reversibility-asymmetry package by transporting
the current semantic support surface from the native DP/emitter side across the
stronger semantic comparison witness. -/
def dpEmitter_to_godel_lcelReversibilityAsymmetry_via_semanticComparison :
    LCELReversibilityAsymmetry godel1931LCELInstance :=
  godel_dpEmitter_lcelSemanticComparisonWitness.symm.transports_semanticReversibilityAsymmetry
    dpEmitter_semanticBaseLayerSupport
    dpEmitter_semanticLicenseTransferSupport
    dpEmitter_semanticReimportTransferSupport

/-- Rebuild the native DP/emitter-side LCEL boundary-factorization package by
transporting the current semantic support surface from the Gödel side across the
stronger semantic comparison witness. -/
def godel_to_dpEmitter_lcelBoundaryFactorization_via_semanticComparison :
    LCELBoundaryFactorization dpEmitterLCELInstance :=
  godel_dpEmitter_lcelSemanticComparisonWitness.transports_semanticBoundaryFactorization
    godel1931_semanticReimportTransferSupport
    godel1931_semanticLicenseTransferSupport

/-- Rebuild the Gödel-side LCEL boundary-factorization package by transporting
the current semantic support surface from the native DP/emitter side across the
stronger semantic comparison witness. -/
def dpEmitter_to_godel_lcelBoundaryFactorization_via_semanticComparison :
    LCELBoundaryFactorization godel1931LCELInstance :=
  godel_dpEmitter_lcelSemanticComparisonWitness.symm.transports_semanticBoundaryFactorization
    dpEmitter_semanticReimportTransferSupport
    dpEmitter_semanticLicenseTransferSupport

/-- Rebuild the native DP/emitter-side LCEL reversibility-asymmetry package by
transporting the stronger proof-carrying support records from the Gödel side
across the semantic comparison witness. -/
def godel_to_dpEmitter_lcelReversibilityAsymmetryFromSupport_via_semanticComparison :
    LCELReversibilityAsymmetry dpEmitterLCELInstance :=
  godel_dpEmitter_lcelSupportComparisonWitness.transports_reversibilityAsymmetryFromSourceSupport

/-- Rebuild the Gödel-side LCEL reversibility-asymmetry package by transporting
the stronger proof-carrying support records from the native DP/emitter side
across the semantic comparison witness. -/
def dpEmitter_to_godel_lcelReversibilityAsymmetryFromSupport_via_semanticComparison :
    LCELReversibilityAsymmetry godel1931LCELInstance :=
  godel_dpEmitter_lcelSupportComparisonWitness.transports_reversibilityAsymmetryFromTargetSupport

/-- Rebuild the native DP/emitter-side LCEL boundary-factorization package by
transporting the stronger proof-carrying boundary-factorization support record
from the Gödel side across the semantic comparison witness. -/
def godel_to_dpEmitter_lcelBoundaryFactorizationFromSupport_via_semanticComparison :
    LCELBoundaryFactorization dpEmitterLCELInstance :=
  godel_dpEmitter_lcelSupportComparisonWitness.transports_boundaryFactorizationFromSourceSupport

/-- Rebuild the Gödel-side LCEL boundary-factorization package by transporting
the stronger proof-carrying boundary-factorization support record from the
native DP/emitter side across the semantic comparison witness. -/
def dpEmitter_to_godel_lcelBoundaryFactorizationFromSupport_via_semanticComparison :
    LCELBoundaryFactorization godel1931LCELInstance :=
  godel_dpEmitter_lcelSupportComparisonWitness.transports_boundaryFactorizationFromTargetSupport

/-- Direct quasi-functor between the Gödel-side and native DP/emitter-side
canonical LCEL instances. -/
def godel_dp_lcelQuasiFunctor :
    LCELQuasiFunctor godel1931LCELInstance dpEmitterLCELInstance :=
  godel_dpEmitter_lcelComparisonWitness.toQuasiFunctor

/-- Artifact-facing structural identity for the Gödel-side and native
DP/emitter-side canonical LCEL instances. -/
theorem godel_dp_lcel_structural_identity :
    Nonempty
        (LCELQuasiFunctor
          godel1931LCELInstance dpEmitterLCELInstance)
      ∧ Nonempty
          (LCELQuasiFunctor
            dpEmitterLCELInstance godel1931LCELInstance) := by
  exact godel_dpEmitter_lcelComparisonWitness.structural_identity_bidirectional

end OperatorKO7.LCELStructuralIdentity
