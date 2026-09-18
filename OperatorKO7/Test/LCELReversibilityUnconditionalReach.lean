import OperatorKO7.Meta.LCELReversibilityUnconditional
import OperatorKO7.Meta.LCELDpInstance

/-!
# Reach test for `Meta/LCELReversibilityUnconditional.lean`

Exercises every public theorem and definition of the unconditional LCEL closure
module. Each of the seven core targets (Propositions 5.8 and 5.9, three
universal supports, universal stagewise equivalence, and the unconditional
artifact-facing structural-identity theorem) is named in a `#check` and
exercised on the canonical Gödel 1931, benchmark-transport, and DP-emitter
instances.
-/

namespace OperatorKO7.Test.LCELReversibilityUnconditionalReach

open OperatorKO7
open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELReversibilityUnconditional
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.ReflectionSchema

#check @OperatorKO7.LCELReversibilityUnconditional.semanticBaseLayerSupport_universal
#check @OperatorKO7.LCELReversibilityUnconditional.semanticLicenseTransferSupport_universal
#check @OperatorKO7.LCELReversibilityUnconditional.semanticReimportTransferSupport_universal
#check @OperatorKO7.LCELReversibilityUnconditional.baseReversibilitySupport_universal
#check @OperatorKO7.LCELReversibilityUnconditional.licenseIrreversibilitySupport_universal
#check @OperatorKO7.LCELReversibilityUnconditional.reimportReversibilitySupport_universal
#check @OperatorKO7.LCELReversibilityUnconditional.boundaryFactorizationSupport_universal
#check @OperatorKO7.LCELReversibilityUnconditional.lcel_reversibility_asymmetry_unconditional
#check @OperatorKO7.LCELReversibilityUnconditional.lcel_boundary_factorization_unconditional
#check @OperatorKO7.LCELReversibilityUnconditional.stagewiseEquivalent_universal
#check @OperatorKO7.LCELReversibilityUnconditional.externalLicenseWitness_iff_universal
#check @OperatorKO7.LCELReversibilityUnconditional.reimportClassWitness_iff_universal
#check @OperatorKO7.LCELReversibilityUnconditional.lcel_structural_identity_unconditional
#check @OperatorKO7.LCELReversibilityUnconditional.lcel_structural_identity_bidirectional_unconditional

/-! ## Concrete instance exercises -/

/-- Reversibility asymmetry on the canonical Gödel 1931 instance. -/
example : LCELReversibilityAsymmetry godel1931LCELInstance :=
  lcel_reversibility_asymmetry_unconditional godel1931LCELInstance

/-- Boundary factorization on the canonical Gödel 1931 instance. -/
example : LCELBoundaryFactorization godel1931LCELInstance :=
  lcel_boundary_factorization_unconditional godel1931LCELInstance

/-- Reversibility asymmetry on the DP-emitter instance. -/
example : LCELReversibilityAsymmetry dpEmitterLCELInstance :=
  lcel_reversibility_asymmetry_unconditional dpEmitterLCELInstance

/-- Boundary factorization on the DP-emitter instance. -/
example : LCELBoundaryFactorization dpEmitterLCELInstance :=
  lcel_boundary_factorization_unconditional dpEmitterLCELInstance

/-- Universal stagewise equivalence between Gödel and DP. -/
example :
    StagewiseEquivalent
      godel1931LCELInstance.comparison.profile.shape
      dpEmitterLCELInstance.comparison.profile.shape :=
  stagewiseEquivalent_universal godel1931LCELInstance dpEmitterLCELInstance

/-- Universal cross-instance external-license equivalence. -/
example :
    godel1931LCELInstance.externalLicenseWitness ↔
      dpEmitterLCELInstance.externalLicenseWitness :=
  externalLicenseWitness_iff_universal godel1931LCELInstance dpEmitterLCELInstance

/-- Universal cross-instance reimport-class equivalence. -/
example :
    godel1931LCELInstance.reimportClassWitness ↔
      dpEmitterLCELInstance.reimportClassWitness :=
  reimportClassWitness_iff_universal godel1931LCELInstance dpEmitterLCELInstance

/-- Unconditional Gödel-to-DP quasi-functor. -/
example : Nonempty (LCELQuasiFunctor godel1931LCELInstance dpEmitterLCELInstance) :=
  lcel_structural_identity_unconditional
    godel1931LCELInstance dpEmitterLCELInstance

/-- Unconditional bidirectional Gödel-to-DP quasi-functor. -/
example :
    Nonempty (LCELQuasiFunctor godel1931LCELInstance dpEmitterLCELInstance)
      ∧ Nonempty (LCELQuasiFunctor dpEmitterLCELInstance godel1931LCELInstance) :=
  lcel_structural_identity_bidirectional_unconditional
    godel1931LCELInstance dpEmitterLCELInstance

end OperatorKO7.Test.LCELReversibilityUnconditionalReach
