import OperatorKO7.Meta.RecordStorageForm

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema
namespace BaseDuplicatingSystem
namespace RecordEmissionWitness

example {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (W.terminalStorageForm K).code i = i.1 := by
  exact W.terminalStorageForm_code K i

example {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    Function.Injective (W.terminalStorageForm K).code :=
  W.terminalStorageForm_injective K

example {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    i.1 ≤ (W.terminalNormalizedStorageForm K).code i :=
  W.terminalNormalizedStorageForm_lower_bound K i

example {K : Nat} (F : StorageForm.Normalized K) (i : Fin (K + 1)) :
    i.1 ≤ F.code i :=
  normalized_storage_description_lower_bound F i

end RecordEmissionWitness
end BaseDuplicatingSystem
end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
