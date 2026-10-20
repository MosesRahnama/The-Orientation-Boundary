import OperatorKO7.Meta.BoundaryOperator.LCELP4CBoundary
import OperatorKO7.Meta.BoundaryOperator.TRSInstance

noncomputable section

namespace BoundaryOperatorLCELP4CBoundaryReach

open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.MetaHalt.Predicate
open OperatorKO7.LCELP4CResidualObligation

#check EngineContractLCELP4CResidualHypothesisPackage
#check EngineContractLCELP4CResidualConsequence
#check engineContract_refusal_surface_support_under_LCEL_P4C_obligation
#check engineContract_admits_LCEL_P4C_residual_under_obligation

noncomputable def trsEngineContract : EngineContract TRSPlugInput TypedOutput :=
  withTypedOutputStatus TRS_BoundaryOperator

noncomputable def trsLCELP4CBoundaryPackage :
    EngineContractLCELP4CResidualHypothesisPackage trsEngineContract where
  status := ⟨typedOutputClassifier, typedOutputToRefusalType_mem_support⟩
  refusalStatus_eq := rfl
  source := OperatorKO7.LCELSchema.benchmarkTransportLCELInstance
  target := OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
  residual := benchmark_dp_routeLiftResidualPackage

example (y : TypedOutput) :
    trsLCELP4CBoundaryPackage.status.classifier.classify y ∈ refusalTypeSupport :=
  engineContract_refusal_surface_support_under_LCEL_P4C_obligation
    trsLCELP4CBoundaryPackage y

example :
    (engineContract_admits_LCEL_P4C_residual_under_obligation
      trsLCELP4CBoundaryPackage).unrestrictedWitness =
      benchmark_dp_admitsUnrestrictedWitness_of_routeLiftData :=
  rfl

example :
    (engineContract_admits_LCEL_P4C_residual_under_obligation
      trsLCELP4CBoundaryPackage).witnessFreeStructuralIdentity =
      benchmark_dp_witness_free_structural_identity_viaResidualPackage :=
  rfl

end BoundaryOperatorLCELP4CBoundaryReach
