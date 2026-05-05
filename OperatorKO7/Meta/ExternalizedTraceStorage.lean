import OperatorKO7.Meta.RecordStorageForm

/-!
# Externalized Trace Storage

This module packages the terminal record family from the record-emission layer
as a first-class externalized-trace object.

The existing storage-form layer already proves exact terminal decoding for the
hidden progress index. The new package below keeps that theorem surface but
adds an explicit object-level carrier for the externalized trace family itself,
so the terminal records are available as reusable theorem objects rather than
only through a numeric storage code.

As in `RecordStorageForm.lean`, any stronger description-length theorem still
needs a stricter coding-model hypothesis than the current normalized numeric
storage interface.
-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema
namespace BaseDuplicatingSystem

/-- A first-class externalized trace/storage object over a finite hidden index
family. `externalize i` is the observable object associated with hidden index
`i`, while `code` and `decode` recover that hidden index exactly. -/
structure ExternalizedTraceStorage (K : Nat) (Obs : Type) where
  externalize : Fin (K + 1) → Obs
  code : Obs → Nat
  decode : Nat → Fin (K + 1)
  decode_externalize : ∀ i, decode (code (externalize i)) = i

namespace ExternalizedTraceStorage

variable {K : Nat} {Obs : Type}

@[simp] theorem decode_code_externalize
    (X : ExternalizedTraceStorage K Obs) (i : Fin (K + 1)) :
    X.decode (X.code (X.externalize i)) = i :=
  X.decode_externalize i

theorem externalize_injective (X : ExternalizedTraceStorage K Obs) :
    Function.Injective X.externalize := by
  intro i j hij
  have hdecode := congrArg (fun x => X.decode (X.code x)) hij
  simpa using hdecode

/-- The explicit observed image of the externalized carrier. -/
def imageCarrier (X : ExternalizedTraceStorage K Obs) : Type :=
  { obs : Obs // ∃ i, X.externalize i = obs }

/-- Send a hidden progress index to its observed externalized image point. -/
def indexToImage (X : ExternalizedTraceStorage K Obs) (i : Fin (K + 1)) :
    X.imageCarrier :=
  ⟨X.externalize i, ⟨i, rfl⟩⟩

/-- Recover a hidden progress index from a point known to lie in the observed
externalized image. -/
def imageToIndex (X : ExternalizedTraceStorage K Obs) (y : X.imageCarrier) :
    Fin (K + 1) :=
  X.decode (X.code y.1)

theorem indexToImage_injective (X : ExternalizedTraceStorage K Obs) :
    Function.Injective X.indexToImage := by
  intro i j hij
  apply X.externalize_injective
  simpa [indexToImage] using congrArg Subtype.val hij

@[simp] theorem imageToIndex_indexToImage
    (X : ExternalizedTraceStorage K Obs) (i : Fin (K + 1)) :
    X.imageToIndex (X.indexToImage i) = i := by
  simp [imageToIndex, indexToImage]

@[simp] theorem indexToImage_imageToIndex
    (X : ExternalizedTraceStorage K Obs) (y : X.imageCarrier) :
    X.indexToImage (X.imageToIndex y) = y := by
  rcases y with ⟨obs, ⟨i, rfl⟩⟩
  apply Subtype.ext
  simp [imageToIndex, indexToImage]

/-- Explicit equivalence between hidden indices and the observed externalized
image. -/
def index_image_equiv (X : ExternalizedTraceStorage K Obs) :
    Fin (K + 1) ≃ X.imageCarrier where
  toFun := X.indexToImage
  invFun := X.imageToIndex
  left_inv := X.imageToIndex_indexToImage
  right_inv := X.indexToImage_imageToIndex

/-- Forgetting the observable carrier yields the numeric storage-form surface. -/
def toStorageForm (X : ExternalizedTraceStorage K Obs) : StorageForm K where
  code := fun i => X.code (X.externalize i)
  decode := X.decode
  decode_code := X.decode_externalize

@[simp] theorem toStorageForm_code
    (X : ExternalizedTraceStorage K Obs) (i : Fin (K + 1)) :
    X.toStorageForm.code i = X.code (X.externalize i) :=
  rfl

@[simp] theorem toStorageForm_decode_code
    (X : ExternalizedTraceStorage K Obs) (i : Fin (K + 1)) :
    X.toStorageForm.decode (X.toStorageForm.code i) = i :=
  X.toStorageForm.decode_code i

/-- Compact theorem-backed summary of the exact mathematical content already
carried by an externalized-trace object. -/
structure ContentSummary (X : ExternalizedTraceStorage K Obs) where
  storageForm : StorageForm K
  storageForm_eq : X.toStorageForm = storageForm
  imageEquiv : Fin (K + 1) ≃ X.imageCarrier
  exactRecovery : ∀ i, X.imageToIndex (X.indexToImage i) = i

/-- Generic content summary: exact recovery, observed-image equivalence, and
the induced storage-form surface. -/
def contentSummary (X : ExternalizedTraceStorage K Obs) : ContentSummary X where
  storageForm := X.toStorageForm
  storageForm_eq := rfl
  imageEquiv := X.index_image_equiv
  exactRecovery := X.imageToIndex_indexToImage

/-- Reusable schema-side package for an externalized trace object together with
its exact proved content. This is fully generic in the observable carrier. -/
structure Package (K : Nat) (Obs : Type) where
  storage : ExternalizedTraceStorage K Obs
  summary : ContentSummary storage

namespace Package

/-- Every externalized-trace object canonically yields the reusable package. -/
def ofStorage (X : ExternalizedTraceStorage K Obs) : Package K Obs where
  storage := X
  summary := X.contentSummary

/-- Paper-facing numeric storage-form projection from the packaged trace. -/
abbrev storageForm (P : Package K Obs) : StorageForm K :=
  P.summary.storageForm

@[simp] theorem storageForm_eq (P : Package K Obs) :
    P.storage.toStorageForm = P.storageForm :=
  P.summary.storageForm_eq

/-- Observed image carrier projected from the packaged trace. -/
abbrev imageCarrier (P : Package K Obs) : Type :=
  P.storage.imageCarrier

/-- Finite-index equivalence projected from the packaged trace. -/
abbrev imageEquiv (P : Package K Obs) :
    Fin (K + 1) ≃ P.imageCarrier :=
  P.summary.imageEquiv

@[simp] theorem exactRecovery (P : Package K Obs) (i : Fin (K + 1)) :
    P.storage.imageToIndex (P.storage.indexToImage i) = i :=
  P.summary.exactRecovery i

end Package

/-- Canonical package view of an externalized trace. -/
def package (X : ExternalizedTraceStorage K Obs) : Package K Obs :=
  Package.ofStorage X

/-- Exact extra data needed to upgrade the observed-image equivalence to an
equivalence with the entire ambient observable carrier. -/
structure CarrierEquivalenceResidual (X : ExternalizedTraceStorage K Obs) where
  indexOf : Obs → Fin (K + 1)
  externalize_indexOf : ∀ obs, X.externalize (indexOf obs) = obs

/-- Under the explicit carrier-equivalence residual hypothesis, the hidden
index family is equivalent to the whole ambient observable carrier, not only
to the observed image. -/
def index_equiv_of_carrierResidual
    (X : ExternalizedTraceStorage K Obs)
    (R : CarrierEquivalenceResidual X) :
    Fin (K + 1) ≃ Obs where
  toFun := X.externalize
  invFun := R.indexOf
  left_inv := by
    intro i
    apply X.externalize_injective
    simpa using R.externalize_indexOf (X.externalize i)
  right_inv := R.externalize_indexOf

end ExternalizedTraceStorage

namespace RecordEmissionWitness

variable {Sys : BaseDuplicatingSystem} {b s : Sys.T}

/-- The terminal record family itself is an externalized trace/storage object:
the emitted terminal record is the observable, and the record coordinate
recovers the hidden progress index exactly. -/
def terminalExternalizedTraceStorage
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    ExternalizedTraceStorage K Sys.T where
  externalize := fun i => Sys.wrapChain s i.1 b
  code := W.recordCoord
  decode := fun n => ⟨Nat.min n K, by
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.lt_succ_self K)⟩
  decode_externalize := by
    intro i
    apply Fin.ext
    rw [W.record_terminal i.1]
    simp [Nat.min_eq_left (Nat.le_of_lt_succ i.2)]

@[simp] theorem terminalExternalizedTraceStorage_externalize
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (W.terminalExternalizedTraceStorage K).externalize i = Sys.wrapChain s i.1 b :=
  rfl

@[simp] theorem terminalExternalizedTraceStorage_code
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (W.terminalExternalizedTraceStorage K).code
        ((W.terminalExternalizedTraceStorage K).externalize i) = i.1 := by
  exact W.record_terminal i.1

@[simp] theorem terminalExternalizedTraceStorage_decode
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (W.terminalExternalizedTraceStorage K).decode
        ((W.terminalExternalizedTraceStorage K).code
          ((W.terminalExternalizedTraceStorage K).externalize i)) = i :=
  (W.terminalExternalizedTraceStorage K).decode_externalize i

theorem terminalExternalizedTraceStorage_toStorageForm
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    (W.terminalExternalizedTraceStorage K).toStorageForm = W.terminalStorageForm K :=
  rfl

theorem terminalExternalizedTraceStorage_lower_bound
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    i.1 ≤ (W.terminalExternalizedTraceStorage K).toStorageForm.code i := by
  rw [W.terminalExternalizedTraceStorage_toStorageForm K]
  exact W.terminalNormalizedStorageForm_lower_bound K i

def terminalExternalizedTraceStorage_index_image_equiv
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    Fin (K + 1) ≃ (W.terminalExternalizedTraceStorage K).imageCarrier :=
  (W.terminalExternalizedTraceStorage K).index_image_equiv

/-- Paper-facing terminal-family content summary: the storage form is the
existing terminal storage form, the observed image is equivalent to
`Fin (K + 1)`, and recovery is exact. -/
def terminalExternalizedTraceContentSummary
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    ExternalizedTraceStorage.ContentSummary (W.terminalExternalizedTraceStorage K) where
  storageForm := W.terminalStorageForm K
  storageForm_eq := W.terminalExternalizedTraceStorage_toStorageForm K
  imageEquiv := W.terminalExternalizedTraceStorage_index_image_equiv K
  exactRecovery := by
    intro i
    simpa [ExternalizedTraceStorage.imageToIndex, ExternalizedTraceStorage.indexToImage] using
      W.terminalExternalizedTraceStorage_decode K i

/-- Reusable terminal-family package for the record-emission witness surface. -/
def terminalExternalizedTracePackage
    (W : RecordEmissionWitness Sys b s) (K : Nat) :
    ExternalizedTraceStorage.Package K Sys.T where
  storage := W.terminalExternalizedTraceStorage K
  summary := W.terminalExternalizedTraceContentSummary K

@[simp] theorem terminalExternalizedTraceStorage_imageToIndex_indexToImage
    (W : RecordEmissionWitness Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (W.terminalExternalizedTraceStorage K).imageToIndex
      ((W.terminalExternalizedTraceStorage K).indexToImage i) = i := by
  simpa [ExternalizedTraceStorage.imageToIndex, ExternalizedTraceStorage.indexToImage] using
    W.terminalExternalizedTraceStorage_decode K i

@[simp] theorem terminalExternalizedTraceStorage_indexToImage_imageToIndex
    (W : RecordEmissionWitness Sys b s) (K : Nat)
    (y : (W.terminalExternalizedTraceStorage K).imageCarrier) :
    (W.terminalExternalizedTraceStorage K).indexToImage
      ((W.terminalExternalizedTraceStorage K).imageToIndex y) = y := by
  exact
    (W.terminalExternalizedTraceStorage K).indexToImage_imageToIndex y

end RecordEmissionWitness

namespace FaithfulRecordEmitter

variable {Sys : BaseDuplicatingSystem} {b s : Sys.T}

/-- The more semantic faithful-emitter interface induces the same terminal
externalized-trace object, now at the level of emitted record observations. -/
def terminalExternalizedTraceStorage
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) :
    ExternalizedTraceStorage K E.RecordObs where
  externalize := fun i => E.recordObs (Sys.wrapChain s i.1 b)
  code := E.decodeRecord
  decode := fun n => ⟨Nat.min n K, by
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.lt_succ_self K)⟩
  decode_externalize := by
    intro i
    apply Fin.ext
    rw [E.decode_record_at_terminal i.1]
    simp [Nat.min_eq_left (Nat.le_of_lt_succ i.2)]

@[simp] theorem terminalExternalizedTraceStorage_code
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (E.terminalExternalizedTraceStorage K).code
        ((E.terminalExternalizedTraceStorage K).externalize i) = i.1 := by
  exact E.decode_record_at_terminal i.1

@[simp] theorem terminalExternalizedTraceStorage_decode
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (E.terminalExternalizedTraceStorage K).decode
        ((E.terminalExternalizedTraceStorage K).code
          ((E.terminalExternalizedTraceStorage K).externalize i)) = i :=
  (E.terminalExternalizedTraceStorage K).decode_externalize i

theorem terminalExternalizedTraceStorage_toStorageForm
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) :
    (E.terminalExternalizedTraceStorage K).toStorageForm
      = (E.toRecordEmissionWitness).terminalStorageForm K :=
  rfl

def terminalExternalizedTraceStorage_index_image_equiv
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) :
    Fin (K + 1) ≃ (E.terminalExternalizedTraceStorage K).imageCarrier :=
  (E.terminalExternalizedTraceStorage K).index_image_equiv

/-- Semantic emitter version of the same paper-facing content summary. -/
def terminalExternalizedTraceContentSummary
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) :
    ExternalizedTraceStorage.ContentSummary (E.terminalExternalizedTraceStorage K) where
  storageForm := (E.toRecordEmissionWitness).terminalStorageForm K
  storageForm_eq := E.terminalExternalizedTraceStorage_toStorageForm K
  imageEquiv := E.terminalExternalizedTraceStorage_index_image_equiv K
  exactRecovery := by
    intro i
    simpa [ExternalizedTraceStorage.imageToIndex, ExternalizedTraceStorage.indexToImage] using
      E.terminalExternalizedTraceStorage_decode K i

/-- Reusable terminal-family package for the faithful-emitter surface. -/
def terminalExternalizedTracePackage
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) :
    ExternalizedTraceStorage.Package K E.RecordObs where
  storage := E.terminalExternalizedTraceStorage K
  summary := E.terminalExternalizedTraceContentSummary K

@[simp] theorem terminalExternalizedTraceStorage_imageToIndex_indexToImage
    (E : FaithfulRecordEmitter Sys b s) (K : Nat) (i : Fin (K + 1)) :
    (E.terminalExternalizedTraceStorage K).imageToIndex
      ((E.terminalExternalizedTraceStorage K).indexToImage i) = i := by
  simpa [ExternalizedTraceStorage.imageToIndex, ExternalizedTraceStorage.indexToImage] using
    E.terminalExternalizedTraceStorage_decode K i

@[simp] theorem terminalExternalizedTraceStorage_indexToImage_imageToIndex
    (E : FaithfulRecordEmitter Sys b s) (K : Nat)
    (y : (E.terminalExternalizedTraceStorage K).imageCarrier) :
    (E.terminalExternalizedTraceStorage K).indexToImage
      ((E.terminalExternalizedTraceStorage K).imageToIndex y) = y := by
  exact
    (E.terminalExternalizedTraceStorage K).indexToImage_imageToIndex y

end FaithfulRecordEmitter

end BaseDuplicatingSystem

def freeRecordEmissionWitness_index_image_equiv (K : Nat) :
    Fin (K + 1) ≃
      ((BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTraceStorage
          (W := freeRecordEmissionWitness) K).imageCarrier) :=
  BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTraceStorage_index_image_equiv
    (W := freeRecordEmissionWitness) K

def freeRecordEmissionWitness_contentSummary (K : Nat) :
    BaseDuplicatingSystem.ExternalizedTraceStorage.ContentSummary
      ((BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTraceStorage
          (W := freeRecordEmissionWitness) K)) :=
  BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTraceContentSummary
    (W := freeRecordEmissionWitness) K

/-- Canonical free-syntax package for the record-emission witness surface. -/
def freeRecordEmissionWitness_tracePackage (K : Nat) :
    BaseDuplicatingSystem.ExternalizedTraceStorage.Package K freeBaseSystem.T :=
  BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTracePackage
    (W := freeRecordEmissionWitness) K

@[simp] theorem freeRecordEmissionWitness_imageToIndex_indexToImage
    (K : Nat) (i : Fin (K + 1)) :
    (BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTraceStorage
        (W := freeRecordEmissionWitness) K).imageToIndex
      ((BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTraceStorage
          (W := freeRecordEmissionWitness) K).indexToImage i) = i := by
  exact
    BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTraceStorage_imageToIndex_indexToImage
      (W := freeRecordEmissionWitness) K i

def freeFaithfulRecordEmitter_index_image_equiv (K : Nat) :
    Fin (K + 1) ≃
      ((BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTraceStorage
          (E := freeFaithfulRecordEmitter) K).imageCarrier) :=
  BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTraceStorage_index_image_equiv
    (E := freeFaithfulRecordEmitter) K

def freeFaithfulRecordEmitter_contentSummary (K : Nat) :
    BaseDuplicatingSystem.ExternalizedTraceStorage.ContentSummary
      ((BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTraceStorage
          (E := freeFaithfulRecordEmitter) K)) :=
  BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTraceContentSummary
    (E := freeFaithfulRecordEmitter) K

/-- Canonical free-syntax package for the faithful-emitter surface. -/
def freeFaithfulRecordEmitter_tracePackage (K : Nat) :
    BaseDuplicatingSystem.ExternalizedTraceStorage.Package K Nat :=
  BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTracePackage
    (E := freeFaithfulRecordEmitter) K

@[simp] theorem freeFaithfulRecordEmitter_imageToIndex_indexToImage
    (K : Nat) (i : Fin (K + 1)) :
    (BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTraceStorage
        (E := freeFaithfulRecordEmitter) K).imageToIndex
      ((BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTraceStorage
          (E := freeFaithfulRecordEmitter) K).indexToImage i) = i := by
  exact
    BaseDuplicatingSystem.FaithfulRecordEmitter.terminalExternalizedTraceStorage_imageToIndex_indexToImage
      (E := freeFaithfulRecordEmitter) K i

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
