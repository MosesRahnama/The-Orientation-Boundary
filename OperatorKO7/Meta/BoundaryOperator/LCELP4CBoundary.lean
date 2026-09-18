import OperatorKO7.Meta.BoundaryOperator.EngineContract
import OperatorKO7.Meta.LCELP4CResidualObligation

/-!
# Boundary Operator LCEL P4C Boundary

Explicit boundary between the WS-D engine-contract surface and the LCEL P4C
residual-obligation layer.
-/

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.MetaHalt.Predicate
open OperatorKO7.LCELSchema
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELUnrestrictedExistence
open OperatorKO7.LCELP4CResidualObligation

universe u

/-- Explicit hypothesis package needed before a runtime-facing engine contract
can consume the LCEL P4C residual layer honestly. The contract exposes the
typed-refusal surface, while the raw-pair carrier and residual package remain
named external obligations. -/
structure EngineContractLCELP4CResidualHypothesisPackage
    {X : Type u} (C : EngineContract X TypedOutput) where
  status : TypedRefusalRuntimeStatus TypedOutput
  refusalStatus_eq : C.refusalStatus? = some status
  source : FormalLCELInstance
  target : FormalLCELInstance
  residual : LCELRouteLiftResidualPackage source target

/-- Consequences transported once the engine contract is paired with an explicit
LCEL P4C residual package. -/
structure EngineContractLCELP4CResidualConsequence
    (L₁ L₂ : FormalLCELInstance) where
  unrestrictedWitness : AdmitsLCELUnrestrictedWitness L₁ L₂
  witnessFreeStructuralIdentity :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = L₁
        ∧ A₂.instance_ = L₂
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂)

/-- The typed-refusal surface advertised by the engine contract remains live
under the same residual-package hypothesis package. -/
theorem engineContract_refusal_surface_support_under_LCEL_P4C_obligation
    {X : Type u}
    {C : EngineContract X TypedOutput}
    (H : EngineContractLCELP4CResidualHypothesisPackage C)
    (y : TypedOutput) :
    H.status.classifier.classify y ∈ refusalTypeSupport :=
  EngineContract.refusal_support H.refusalStatus_eq y

/-- Boundary-level LCEL P4C corollary: once the runtime-facing engine contract
is paired with the explicit residual-obligation package, the LCEL unrestricted-
witness admission and the existence-form universal-license conclusion both
follow. The contract does not synthesize the raw pair or residual package on
its own; those are exactly the named obligations carried by the hypothesis
package. -/
theorem engineContract_admits_LCEL_P4C_residual_under_obligation
    {X : Type u}
    {C : EngineContract X TypedOutput}
    (H : EngineContractLCELP4CResidualHypothesisPackage C) :
    EngineContractLCELP4CResidualConsequence H.source H.target := by
  refine {
    unrestrictedWitness := H.residual.admitsUnrestrictedWitness
    witnessFreeStructuralIdentity :=
      lcel_witness_free_structural_identity_of_residualPackage H.residual
  }

end OperatorKO7.Meta.BoundaryOperator
