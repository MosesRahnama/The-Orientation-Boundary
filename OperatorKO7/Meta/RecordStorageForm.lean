import OperatorKO7.Meta.ComputationalLayerCrossing

/-!
# Record Storage Form

This module packages the terminal record family from
`ComputationalLayerCrossing.lean` as a first-class storage-form object.

The exact layer-crossing theorem already lives in `RecordEmissionWitness`: the
terminal record coordinate recovers the hidden progress index exactly. The new
definitions below isolate the reusable externalized-storage surface and record
the strongest honest numeric lower bound currently derivable from the live
definitions: any normalized storage description on the terminal family must
assign code value at least the recovered depth index.

A full Kolmogorov-style theorem would require an additional coding-model
hypothesis beyond this monotone normal form.
-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema
namespace BaseDuplicatingSystem

/-- A storage form externalizes a hidden progress index into a numeric code
with an exact decoder. -/
structure StorageForm (K : Nat) where
  code : Fin (K + 1) → Nat
  decode : Nat → Fin (K + 1)
  decode_code : ∀ i, decode (code i) = i

namespace StorageForm

variable {K : Nat}

theorem code_injective (F : StorageForm K) : Function.Injective F.code := by
  intro i j hij
  have h := congrArg F.decode hij
  simpa [F.decode_code i, F.decode_code j] using h

/-- A normalized storage form is a storage form whose numeric code increases
strictly with the hidden progress index. This is the exact extra hypothesis
needed for a numeric lower-bound theorem. -/
structure Normalized (K : Nat) extends StorageForm K where
  strictMono_code : StrictMono code

namespace Normalized

private theorem index_le_code_aux (F : Normalized K) :
    ∀ n (hn : n < K + 1), n ≤ F.code ⟨n, hn⟩
  | 0, _ => Nat.zero_le _
  | n + 1, hn => by
      have hprev : n < K + 1 := Nat.lt_of_succ_lt hn
      have ih : n ≤ F.code ⟨n, hprev⟩ := index_le_code_aux F n hprev
      have hstep : F.code ⟨n, hprev⟩ < F.code ⟨n + 1, hn⟩ := by
        apply F.strictMono_code
        change n < n + 1
        exact Nat.lt_succ_self n
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hstep)

theorem index_le_code (F : Normalized K) (i : Fin (K + 1)) :
    i.1 ≤ F.code i := by
  simpa using index_le_code_aux F i.1 i.2

end Normalized
end StorageForm

namespace RecordEmissionWitness

variable {Sys : BaseDuplicatingSystem} {b s : Sys.T}

/-- The terminal record family already carries an exact externalized storage
form for the hidden progress index. -/
def terminalStorageForm (W : RecordEmissionWitness Sys b s) (K : Nat) :
    StorageForm K where
  code := fun i => W.recordCoord (Sys.wrapChain s i.1 b)
  decode := fun n => ⟨Nat.min n K, by
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.lt_succ_self K)⟩
  decode_code := by
    intro i
    apply Fin.ext
    rw [W.record_terminal i.1]
    simp [Nat.min_eq_left (Nat.le_of_lt_succ i.2)]

@[simp] theorem terminalStorageForm_code
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (W.terminalStorageForm K).code i = i.1 := by
  show W.recordCoord (Sys.wrapChain s i.1 b) = i.1
  exact W.record_terminal i.1

@[simp] theorem terminalStorageForm_decode_code
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (W.terminalStorageForm K).decode ((W.terminalStorageForm K).code i) = i :=
  (W.terminalStorageForm K).decode_code i

theorem terminalStorageForm_injective
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    Function.Injective (W.terminalStorageForm K).code :=
  (W.terminalStorageForm K).code_injective

/-- The canonical terminal family is already a normalized storage form. -/
def terminalNormalizedStorageForm
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    StorageForm.Normalized K where
  toStorageForm := W.terminalStorageForm K
  strictMono_code := by
    intro i j hij
    simpa [terminalStorageForm, W.record_terminal] using hij

theorem terminalNormalizedStorageForm_lower_bound
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    i.1 ≤ (W.terminalNormalizedStorageForm K).code i :=
  StorageForm.Normalized.index_le_code (W.terminalNormalizedStorageForm K) i

/-- Any normalized storage description on the externalized terminal family has
code value at least the recovered progress index. This is the strongest honest
numeric lower bound available from the current definitions. -/
theorem normalized_storage_description_lower_bound
    {K : Nat} (F : StorageForm.Normalized K) (i : Fin (K + 1)) :
    i.1 ≤ F.code i :=
  StorageForm.Normalized.index_le_code F i

end RecordEmissionWitness

end BaseDuplicatingSystem
end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
