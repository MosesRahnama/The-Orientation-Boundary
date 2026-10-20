import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELStructuralIdentity

/-!
# LCEL Reversibility, Boundary Factorization, and Structural Identity, Unconditional

This file closes Paper C Propositions 5.8 and 5.9 and the artifact-facing LCEL
structural-identity theorem unconditionally on the typed `FormalLCELInstance`
carrier.

The witness slots in `Meta/LCELReversibility.lean` and the slot-equivalence
hypotheses in `Meta/LCELStructuralIdentity.lean` are dischargeable on every
typed instance because:

- `FormalExternalClassicalComparisonObject.semanticSupported` and
  `.semanticTransferSupported` are theorems on the comparison object itself,
  so every `L : FormalLCELInstance` carries `SemanticBaseLayerSupport L`,
  `SemanticLicenseTransferSupport L`, and `SemanticReimportTransferSupport L`
  unconditionally.
- `FormalExternalClassicalComparisonObject.supported` produces stagewise
  equivalence to the canonical DP profile shape, so any two instances are
  stagewise-equivalent through the canonical DP pivot.
- The retained proposition-level slots `externalLicenseWitness` and
  `reimportClassWitness` are inhabited on every instance via
  `externalLicenseHolds` and `reimportClassHolds`, so cross-instance
  equivalences are inhabited.

These three facts together discharge every hypothesis required by the existing
`lcel_reversibility_asymmetry_of_witnesses`, `lcel_boundary_factorization_of_witness`,
and `lcel_structural_identity` theorems.
-/

namespace OperatorKO7.LCELReversibilityUnconditional

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema

private theorem iff_of_true {P Q : Prop} (hP : P) (hQ : Q) : P ↔ Q :=
  ⟨fun _ => hQ, fun _ => hP⟩

private theorem stagewiseEquivalent_trans
    {P Q R : SixStepStructuralProfile}
    (hPQ : StagewiseEquivalent P Q)
    (hQR : StagewiseEquivalent Q R) :
    StagewiseEquivalent P R := by
  intro s
  exact (hPQ s).trans (hQR s)

/-! ## Universal semantic supports -/

/-- Every typed LCEL instance carries base-layer semantic support. -/
theorem semanticBaseLayerSupport_universal (L : FormalLCELInstance) :
    SemanticBaseLayerSupport L :=
  L.comparison.semanticSupported.1

/-- Every typed LCEL instance carries the obstruction-to-reflection transfer
support that drives the license-irreversibility clause. -/
theorem semanticLicenseTransferSupport_universal (L : FormalLCELInstance) :
    SemanticLicenseTransferSupport L :=
  L.comparison.semanticTransferSupported.1

/-- Every typed LCEL instance carries the reflection-to-reimport transfer
support that drives the reimport-reversibility clause. -/
theorem semanticReimportTransferSupport_universal (L : FormalLCELInstance) :
    SemanticReimportTransferSupport L :=
  L.comparison.semanticTransferSupported.2

/-! ## Universal proof-carrying support records -/

/-- Universal base-layer support record. -/
def baseReversibilitySupport_universal (L : FormalLCELInstance) :
    BaseReversibilitySupport L :=
  baseReversibilitySupport_of_semanticBase
    (semanticBaseLayerSupport_universal L)

/-- Universal license-side support record. -/
def licenseIrreversibilitySupport_universal (L : FormalLCELInstance) :
    LicenseIrreversibilitySupport L :=
  licenseIrreversibilitySupport_of_semanticTransfer
    (semanticLicenseTransferSupport_universal L)

/-- Universal reimport-side support record. -/
def reimportReversibilitySupport_universal (L : FormalLCELInstance) :
    ReimportReversibilitySupport L :=
  reimportReversibilitySupport_of_semanticTransfer
    (semanticReimportTransferSupport_universal L)

/-- Universal boundary-factorization support record. -/
def boundaryFactorizationSupport_universal (L : FormalLCELInstance) :
    BoundaryFactorizationSupport L :=
  boundaryFactorizationSupport_of_supports
    (reimportReversibilitySupport_universal L)
    (licenseIrreversibilitySupport_universal L)

/-! ## Unconditional Paper C Propositions 5.8 and 5.9 -/

/-- Paper C Proposition 5.8 (LCEL reversibility asymmetry), unconditional on
every typed LCEL instance. -/
def lcel_reversibility_asymmetry_unconditional (L : FormalLCELInstance) :
    LCELReversibilityAsymmetry L :=
  lcelReversibilityAsymmetry_of_strongerSupports
    (baseReversibilitySupport_universal L)
    (licenseIrreversibilitySupport_universal L)
    (reimportReversibilitySupport_universal L)

/-- Paper C Proposition 5.9 (LCEL boundary factorization), unconditional on
every typed LCEL instance. -/
def lcel_boundary_factorization_unconditional (L : FormalLCELInstance) :
    LCELBoundaryFactorization L :=
  (boundaryFactorizationSupport_universal L).toLCELBoundaryFactorization

/-! ## Universal stagewise equivalence (DP pivot) -/

/-- Any two typed LCEL instances are stagewise-equivalent through the canonical
DP profile pivot recorded by `FormalExternalClassicalComparisonObject.supported`. -/
theorem stagewiseEquivalent_universal (L₁ L₂ : FormalLCELInstance) :
    StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape :=
  stagewiseEquivalent_trans
    L₁.comparison.supported.2.2
    (StagewiseEquivalent.symm L₂.comparison.supported.2.2)

/-! ## Unconditional artifact-facing LCEL structural identity -/

/-- Universal cross-instance external-license equivalence, discharged from the
two `externalLicenseHolds` carriers. -/
theorem externalLicenseWitness_iff_universal (L₁ L₂ : FormalLCELInstance) :
    L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness :=
  iff_of_true L₁.externalLicenseHolds L₂.externalLicenseHolds

/-- Universal cross-instance reimport-class equivalence, discharged from the
two `reimportClassHolds` carriers. -/
theorem reimportClassWitness_iff_universal (L₁ L₂ : FormalLCELInstance) :
    L₁.reimportClassWitness ↔ L₂.reimportClassWitness :=
  iff_of_true L₁.reimportClassHolds L₂.reimportClassHolds

/-- Artifact-facing LCEL structural-identity theorem, unconditional on every
pair of typed LCEL instances. A quasi-functor exists between any two formal
LCEL instances; the existence is proved by combining the DP-pivoted stagewise
equivalence with the universally inhabited cross-instance slot equivalences. -/
theorem lcel_structural_identity_unconditional
    (L₁ L₂ : FormalLCELInstance) :
    Nonempty (LCELQuasiFunctor L₁ L₂) :=
  lcel_structural_identity
    (stagewiseEquivalent_universal L₁ L₂)
    (externalLicenseWitness_iff_universal L₁ L₂)
    (reimportClassWitness_iff_universal L₁ L₂)

/-- Bidirectional form of the unconditional artifact-facing LCEL structural-
identity theorem. -/
theorem lcel_structural_identity_bidirectional_unconditional
    (L₁ L₂ : FormalLCELInstance) :
    Nonempty (LCELQuasiFunctor L₁ L₂) ∧ Nonempty (LCELQuasiFunctor L₂ L₁) :=
  ⟨lcel_structural_identity_unconditional L₁ L₂,
    lcel_structural_identity_unconditional L₂ L₁⟩

end OperatorKO7.LCELReversibilityUnconditional
