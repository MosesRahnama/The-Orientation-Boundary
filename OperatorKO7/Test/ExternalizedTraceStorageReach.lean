import OperatorKO7.Meta.ExternalizedTraceStorage

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema
namespace BaseDuplicatingSystem

example (K : Nat) :
    (freeRecordEmissionWitness_tracePackage K).storage.toStorageForm
      = (freeRecordEmissionWitness_tracePackage K).storageForm := by
  exact (freeRecordEmissionWitness_tracePackage K).storageForm_eq

example (K : Nat) (i : Fin (K + 1)) :
    (freeRecordEmissionWitness_tracePackage K).storage.imageToIndex
      (((freeRecordEmissionWitness_tracePackage K).storage).indexToImage i) = i := by
  exact (freeRecordEmissionWitness_tracePackage K).exactRecovery i

example (K : Nat) :
    Fin (K + 1) ≃ (freeFaithfulRecordEmitter_tracePackage K).imageCarrier := by
  exact (freeFaithfulRecordEmitter_tracePackage K).imageEquiv

example (K : Nat) (i : Fin (K + 1)) :
    (freeFaithfulRecordEmitter_tracePackage K).storage.imageToIndex
      (((freeFaithfulRecordEmitter_tracePackage K).storage).indexToImage i) = i := by
  exact (freeFaithfulRecordEmitter_tracePackage K).exactRecovery i

example {K : Nat} {Obs : Type} (X : ExternalizedTraceStorage K Obs)
    (R : ExternalizedTraceStorage.CarrierEquivalenceResidual X) :
    Fin (K + 1) ≃ Obs :=
  X.index_equiv_of_carrierResidual R

end BaseDuplicatingSystem
end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
