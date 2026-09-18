import OperatorKO7.Meta.DistinctionBoundary.UniqueCheck

set_option autoImplicit false

/-!
# Relocation: where a sharing implementation puts the check

Manuscript anchor: `rem:relocation` of `Rahnama_The_Distinction_Boundary`.
Roadmap: `ROADMAP-08-the-unique-check.md`, item U5.

A hash-consed or maximally shared representation appears to replace the
equality check by a pointer comparison. This module states what actually
happens, on a finite store model.

* Soundness of pointer comparison is free: identical nodes denote identical
  terms, by congruence.
* Completeness of pointer comparison is exactly the maximal-sharing invariant
  (`pointer_check_iff_maxSharing`).
* The maximal-sharing invariant is exactly injectivity of the denotation map
  (`maxSharing_iff_denote_injective`), which is the hypothesis the injectivity
  barrier of `UniqueCheck` demands. Pointer equality is therefore not an escape
  from the barrier; it is an instance of the barrier's positive side.
* A store that maintains the invariant and can insert a term yields a sound and
  complete comparator on the carrier (`sharing_insert_yields_check`), which by
  uniqueness is the check itself (`sharing_insert_check_is_structEq`). The
  check is not removed by sharing. It is paid when the structure is built and
  spent when the pointers are compared.

Scope. The extraction result is interface-relative: it says that a store
exposing a correctness-carrying insert contains the check, not that every
conceivable sharing scheme must expose such an insert. Randomised fingerprints
relax soundness and are outside this development by construction.

Relation: not a rewrite relation; store model over the kernel carrier.
Closure: not applicable. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.CheckRelocation

open OperatorKO7 Trace
open OperatorKO7.Meta.DistinctionBoundary.UniqueCheck
open OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension

/-- A store of nodes together with the term each node denotes. -/
structure Store (N : Type) where
  /-- The term denoted by a node. -/
  denote : N → Trace

variable {N : Type}

/-- Maximal sharing: distinct nodes denote distinct terms, so no term is
represented twice in the store. -/
def MaxSharing (S : Store N) : Prop :=
  ∀ n₁ n₂ : N, S.denote n₁ = S.denote n₂ → n₁ = n₂

/-- Pointer comparison on nodes. -/
def pointerEq [DecidableEq N] (n₁ n₂ : N) : Bool := decide (n₁ = n₂)

/-- Pointer comparison is always sound for denotations: identical nodes denote
identical terms. Nothing is assumed about the store. -/
theorem pointer_sound (S : Store N) [DecidableEq N] (n₁ n₂ : N)
    (h : pointerEq n₁ n₂ = true) : S.denote n₁ = S.denote n₂ := by
  have : n₁ = n₂ := of_decide_eq_true h
  rw [this]

/-- **U5a, the completeness half.** Pointer comparison decides equality of
denotations if and only if the store is maximally shared. The invariant is not
a convenience of the implementation; it is the whole content of the claim that
pointer comparison is a check. -/
theorem pointer_check_iff_maxSharing (S : Store N) [DecidableEq N] :
    (∀ n₁ n₂ : N, pointerEq n₁ n₂ = true ↔ S.denote n₁ = S.denote n₂)
      ↔ MaxSharing S := by
  constructor
  · intro hiff n₁ n₂ hden
    exact of_decide_eq_true ((hiff n₁ n₂).mpr hden)
  · intro hms n₁ n₂
    constructor
    · intro h
      exact pointer_sound S n₁ n₂ h
    · intro hden
      exact decide_eq_true (hms n₁ n₂ hden)

/-- **The relocation identity.** Maximal sharing is injectivity of the
denotation map. The invariant a shared representation maintains is exactly the
hypothesis the injectivity barrier requires of any abstraction a check may read
through. -/
theorem maxSharing_iff_denote_injective (S : Store N) :
    MaxSharing S ↔ Function.Injective S.denote := by
  constructor
  · intro hms n₁ n₂ h
    exact hms n₁ n₂ h
  · intro hinj n₁ n₂ h
    exact hinj h

/-- **The barrier, applied to the store.** A comparator on terms that reads
them only through the store, by inserting and comparing nodes, forces the
denotation map to be injective on the inserted nodes. Sharing does not evade
the injectivity barrier of `UniqueCheck`; it is the implementation that
satisfies it. Stated through the denotation map itself: if pointer comparison
of nodes decides equality of their denotations, then the store is maximally
shared, which is that injectivity. -/
theorem pointer_check_forces_injective (S : Store N) [DecidableEq N]
    (hiff : ∀ n₁ n₂ : N, pointerEq n₁ n₂ = true ↔ S.denote n₁ = S.denote n₂) :
    Function.Injective S.denote :=
  (maxSharing_iff_denote_injective S).mp
    ((pointer_check_iff_maxSharing S).mp hiff)

/-- An insert operation that returns a node denoting the inserted term. -/
structure SharingInsert (S : Store N) where
  /-- The node allocated or found for a term. -/
  ins : Trace → N
  /-- The allocated node denotes the term it was allocated for. -/
  correct : ∀ t : Trace, S.denote (ins t) = t

/-- **U5a, the extraction theorem.** A maximally shared store with a correct
insert contains a sound and complete comparator on the carrier: compare the
nodes the two terms insert to. The check was paid during construction and is
spent at comparison time. -/
theorem sharing_insert_yields_check (S : Store N) [DecidableEq N]
    (I : SharingInsert S) (hms : MaxSharing S) :
    IsCheck (fun a b : Trace => pointerEq (I.ins a) (I.ins b)) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    have hnode : I.ins a = I.ins b := of_decide_eq_true h
    have : S.denote (I.ins a) = S.denote (I.ins b) := by rw [hnode]
    rw [I.correct a, I.correct b] at this
    exact this
  · intro a b h
    have hden : S.denote (I.ins a) = S.denote (I.ins b) := by
      rw [I.correct a, I.correct b, h]
    exact decide_eq_true (hms _ _ hden)

/-- **The conservation statement.** The comparator a sharing implementation
exposes is the structural comparator, pointwise. Different implementations do
not compute different checks; they relocate the one check to a different point
in the lifecycle. -/
theorem sharing_insert_check_is_structEq (S : Store N) [DecidableEq N]
    (I : SharingInsert S) (hms : MaxSharing S) (a b : Trace) :
    pointerEq (I.ins a) (I.ins b) = structEq a b :=
  structEq_canonical (sharing_insert_yields_check S I hms) a b

/-- The insert map is injective from correctness alone, with no sharing
invariant required: a node determines its denotation, and the denotation of an
inserted term is that term. The sharing invariant is what the converse
direction needs, and the two directions together are why the store carries the
check rather than avoiding it. -/
theorem sharing_insert_injective (S : Store N)
    (I : SharingInsert S) : Function.Injective I.ins := by
  intro a b h
  have : S.denote (I.ins a) = S.denote (I.ins b) := by rw [h]
  rw [I.correct a, I.correct b] at this
  exact this

/-- Non-vacuity: the identity store over the carrier is maximally shared,
carries a correct insert, and its extracted comparator is the structural
comparator. -/
def idStore : Store Trace := ⟨id⟩

theorem idStore_maxSharing : MaxSharing idStore := by
  intro n₁ n₂ h
  exact h

def idInsert : SharingInsert idStore := ⟨id, fun _ => rfl⟩

theorem idStore_extracted_check_is_structEq (a b : Trace) :
    pointerEq (idInsert.ins a) (idInsert.ins b) = structEq a b :=
  sharing_insert_check_is_structEq idStore idInsert idStore_maxSharing a b

/-- Negative control: a store that collapses the carrier to a single node
admits no correct insert at all, so it never reaches the point where its
pointer comparison could be consulted. The collapsing store is the finite-range
hash of the barrier's third corollary in store clothing, and it fails at the
same place. -/
def collapsedStore : Store Unit := ⟨fun _ => void⟩

theorem collapsedStore_admits_no_correct_insert :
    ¬ Nonempty (SharingInsert collapsedStore) := by
  rintro ⟨I⟩
  have h := I.correct (delta void)
  exact Trace.noConfusion h

end OperatorKO7.Meta.DistinctionBoundary.CheckRelocation
