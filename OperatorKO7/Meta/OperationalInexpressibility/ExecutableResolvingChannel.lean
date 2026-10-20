import Mathlib.Data.BitVec
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph

/-!
# Executable optimal resolving channel

The existing capacity theorems characterize the minimum alphabet by fiber
multiplicity.  This module adds a deterministic synthesis algorithm for finite
input carriers.  The algorithm receives an explicit complete enumeration,
orders target values by first appearance inside each observer fiber, and uses
the local rank as the side-channel code.

No `Classical.choice` occurs in the executable definitions.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence

universe u v w

/-- Explicit finite enumeration used by all synthesis definitions. -/
structure Enumeration (X : Type u) [DecidableEq X] where
  items : List X
  nodup : items.Nodup
  complete : ∀ x, x ∈ items

namespace Enumeration

variable {X : Type u} [DecidableEq X]

/-- Every explicit enumeration induces a `Fintype`. -/
def toFintype (E : Enumeration X) : Fintype X where
  elems := E.items.toFinset
  complete := by
    intro x
    simpa using E.complete x

end Enumeration

variable {X : Type u} {Q : Type v} {V : Type w}
variable [DecidableEq X] [DecidableEq Q] [DecidableEq V]

/-- Distinct target values in an observer fiber, ordered by first appearance in
`E.items`. -/
def orderedFiberValues (E : Enumeration X) (q : X → Q) (P : X → V) (o : Q) : List V :=
  ((E.items.filter fun x => q x = o).map P).reverse.dedup.reverse

@[simp] theorem orderedFiberValues_nodup
    (E : Enumeration X) (q : X → Q) (P : X → V) (o : Q) :
    (orderedFiberValues E q P o).Nodup := by
  exact List.nodup_reverse.mpr (List.nodup_dedup
    ((E.items.filter fun x => q x = o).map P).reverse)

/-- Every input's target value occurs in its own ordered fiber list. -/
theorem target_mem_orderedFiberValues
    (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    P x ∈ orderedFiberValues E q P (q x) := by
  simp only [orderedFiberValues, List.mem_reverse, List.mem_dedup,
    List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨x, ⟨E.complete x, rfl⟩, rfl⟩

/-- The executable local code before conversion to the common finite alphabet. -/
def localRank (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) : Nat :=
  (orderedFiberValues E q P (q x)).idxOf (P x)

/-- The local rank is inside its attained target list. -/
theorem localRank_lt_fiberLength
    (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    localRank E q P x < (orderedFiberValues E q P (q x)).length := by
  exact List.idxOf_lt_length_iff.mpr (target_mem_orderedFiberValues E q P x)

/-- A total constructor for a finite code when the bound is available. -/
def toFin? (n k : Nat) : Option (Fin n) :=
  if h : k < n then some ⟨k, h⟩ else none

@[simp] theorem toFin?_some_iff {n k : Nat} :
    (∃ c, toFin? n k = some c) ↔ k < n := by
  unfold toFin?
  split <;> simp_all

section FintypeBridge

variable [Fintype X]

/-- Ordered fiber values enumerate exactly the set used by `fiberVerdicts`. -/
theorem orderedFiberValues_toFinset
    (E : Enumeration X) (q : X → Q) (P : X → V) (o : Q) :
    (orderedFiberValues E q P o).toFinset = fiberVerdicts q P o := by
  classical
  ext v
  simp [orderedFiberValues, fiberVerdicts, E.complete]

/-- Ordered fiber length is the existing observer-fiber multiplicity at `o`. -/
theorem orderedFiberValues_length
    (E : Enumeration X) (q : X → Q) (P : X → V) (o : Q) :
    (orderedFiberValues E q P o).length = (fiberVerdicts q P o).card := by
  have hn := orderedFiberValues_nodup E q P o
  rw [← orderedFiberValues_toFinset E q P o]
  exact (List.toFinset_card_of_nodup hn).symm

/-- Common optimal alphabet size, independent of enumeration order. -/
def alphabetSize (_E : Enumeration X) (q : X → Q) (P : X → V) : Nat :=
  fiberMultiplicity q P

/-- Every local rank fits inside the common optimal alphabet whenever an input
exists. -/
theorem localRank_lt_alphabetSize
    (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    localRank E q P x < alphabetSize E q P := by
  have hlocal := localRank_lt_fiberLength E q P x
  rw [orderedFiberValues_length E q P (q x)] at hlocal
  have hmem : q x ∈ Finset.univ.image q := by simp
  have hle := fiberVerdicts_card_le_of_mem (q := q) (P := P) hmem
  exact lt_of_lt_of_le hlocal hle

/-- Executable optimal side-channel encoder. Empty carriers are handled by the
`Option`: there is no input on which `none` can be observed. -/
def encode? (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    Option (Fin (alphabetSize E q P)) :=
  toFin? (alphabetSize E q P) (localRank E q P x)

/-- Every actual input receives a code. -/
theorem encode?_isSome
    (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    (encode? E q P x).isSome := by
  unfold encode?
  simp [toFin?, localRank_lt_alphabetSize E q P x]

/-- Decoder for an attained observation and a common code. Codes that exceed the
local fiber size return `none`. -/
def decode? (E : Enumeration X) (q : X → Q) (P : X → V)
    (o : Q) (c : Fin (alphabetSize E q P)) : Option V :=
  (orderedFiberValues E q P o)[c.val]?

omit [Fintype X] in
/-- The encoder's code points at the target value used to create it. -/
theorem decode_localRank
    (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    (orderedFiberValues E q P (q x))[localRank E q P x]? = some (P x) := by
  exact List.getElem?_idxOf (target_mem_orderedFiberValues E q P x)

/-- Exact executable recovery. -/
theorem decode_encode
    (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    ∃ c, encode? E q P x = some c ∧ decode? E q P (q x) c = some (P x) := by
  let c : Fin (alphabetSize E q P) :=
    ⟨localRank E q P x, localRank_lt_alphabetSize E q P x⟩
  refine ⟨c, ?_, ?_⟩
  · simp [encode?, toFin?, c, localRank_lt_alphabetSize E q P x]
  · simpa [decode?, c] using decode_localRank E q P x

/-- Convert the optional algorithm into a total channel on actual inputs. -/
def encode (E : Enumeration X) (q : X → Q) (P : X → V) :
    X → Fin (alphabetSize E q P) := fun x =>
  ⟨localRank E q P x, localRank_lt_alphabetSize E q P x⟩

/-- The synthesized channel is resolving. -/
theorem encode_resolving
    (E : Enumeration X) (q : X → Q) (P : X → V) :
    ResolvingSideChannel q P (encode E q P) := by
  intro x y hconf hs
  have hx := decode_localRank E q P x
  have hy := decode_localRank E q P y
  have hcode : localRank E q P x = localRank E q P y := by
    exact congrArg Fin.val hs
  rw [hconf.1, hcode] at hx
  rw [hx] at hy
  exact hconf.2 (Option.some.inj hy)

/-- The augmented observer is licensed by construction. -/
theorem encode_licensed
    (E : Enumeration X) (q : X → Q) (P : X → V) :
    Licensed (augmentObserver q (encode E q P)) P :=
  (licensed_augment_iff_resolving q P (encode E q P)).2 (encode_resolving E q P)

/-- The synthesized alphabet reaches the existing lower bound exactly. -/
theorem encode_alphabet_optimal
    (E : Enumeration X) (q : X → Q) (P : X → V) :
    alphabetSize E q P = fiberMultiplicity q P := rfl

/-- No smaller `Fin n` alphabet can resolve all fibers. -/
theorem no_smaller_fin_channel
    (E : Enumeration X) (q : X → Q) (P : X → V) {n : Nat}
    (hn : n < alphabetSize E q P) :
    ¬ ∃ s : X → Fin n, Licensed (augmentObserver q s) P := by
  intro h
  have hcap := (colorable_iff_fiberMultiplicity_le q P n).1
    ((colorable_iff_exists_fin_resolving_channel q P n).2 h)
  simp [alphabetSize] at hn
  omega

/-- The minimum fixed-length binary width is the existing code deficit. -/
theorem optimal_fixedLength_bits
    (E : Enumeration X) (q : X → Q) (P : X → V) :
    Nat.clog 2 (alphabetSize E q P) = fiberCodeDeficit q P := rfl

/-- Enumeration order changes code labels but not the required alphabet size. -/
theorem alphabetSize_enumeration_independent
    (E₁ E₂ : Enumeration X) (q : X → Q) (P : X → V) :
    alphabetSize E₁ q P = alphabetSize E₂ q P := rfl

/-! ## Actual fixed-width binary codec -/

/-- Minimum fixed bit width of the synthesized optimal side-channel alphabet. -/
def fixedBitWidth (E : Enumeration X) (q : X → Q) (P : X → V) : Nat :=
  Nat.clog 2 (alphabetSize E q P)

/-- Every optimal alphabet code embeds in the exact minimum-width bit space. -/
def codeToBits (E : Enumeration X) (q : X → Q) (P : X → V)
    (c : Fin (alphabetSize E q P)) : BitVec (fixedBitWidth E q P) :=
  let hcap : alphabetSize E q P ≤ 2 ^ fixedBitWidth E q P :=
    Nat.le_pow_clog (by omega : 1 < 2) (alphabetSize E q P)
  BitVec.ofFin (Fin.castLE hcap c)

/-- Decode a bit word back into an optimal alphabet code. Bit patterns outside
the alphabet are rejected. -/
def bitsToCode? (E : Enumeration X) (q : X → Q) (P : X → V)
    (bits : BitVec (fixedBitWidth E q P)) : Option (Fin (alphabetSize E q P)) :=
  toFin? (alphabetSize E q P) bits.toNat

/-- Fixed-width coding round-trips every actual alphabet code. -/
@[simp] theorem bitsToCode?_codeToBits
    (E : Enumeration X) (q : X → Q) (P : X → V)
    (c : Fin (alphabetSize E q P)) :
    bitsToCode? E q P (codeToBits E q P c) = some c := by
  unfold bitsToCode? codeToBits toFin?
  simp [c.isLt]

/-- Executable minimum-width bit encoder for an input state. -/
def encodeBits? (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    Option (BitVec (fixedBitWidth E q P)) :=
  (encode? E q P x).map (codeToBits E q P)

/-- Decoder for the fixed-width binary side channel. -/
def decodeBits? (E : Enumeration X) (q : X → Q) (P : X → V)
    (o : Q) (bits : BitVec (fixedBitWidth E q P)) : Option V :=
  (bitsToCode? E q P bits).bind (decode? E q P o)

/-- Actual fixed-width encoding and decoding recover every target. -/
theorem decodeBits_encodeBits
    (E : Enumeration X) (q : X → Q) (P : X → V) (x : X) :
    ∃ bits, encodeBits? E q P x = some bits ∧
      decodeBits? E q P (q x) bits = some (P x) := by
  rcases decode_encode E q P x with ⟨c, hc, hdecode⟩
  refine ⟨codeToBits E q P c, ?_, ?_⟩
  · simp [encodeBits?, hc]
  · simp [decodeBits?, hdecode]

/-- The actual bit width is the previously proved minimum fixed-length deficit. -/
theorem fixedBitWidth_eq_fiberCodeDeficit
    (E : Enumeration X) (q : X → Q) (P : X → V) :
    fixedBitWidth E q P = fiberCodeDeficit q P := by
  exact optimal_fixedLength_bits E q P

end FintypeBridge

/-- Finite dynamic observer refinement needs to be checked only at the existing
image-cardinality stabilization bound. This is the inherited persistent-channel
theorem on the executable-channel surface. -/
theorem fixed_channel_stabilizes_at_image_bound
    {X : Type u} {Q : Type v} {V : Type w} {C : Type*}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) (s : X → C) :
    (∀ n, Licensed (augmentObserver (orbitObserver F q n) s) P) ↔
      Licensed (augmentObserver
        (orbitObserver F q (Nat.card (ObservedValue q) - 1)) s) P :=
  fixed_channel_licenses_all_iff_at_image_bound F q hc P s

/-- Compute the stabilization stage from the enumerated observation image. -/
def stabilizationStage (E : Enumeration X) (q : X → Q) : Nat :=
  (E.items.toFinset.image q).card - 1

/-- The computed image size gives the semantic stabilization bound. -/
theorem stabilizationStage_eq_image_bound (E : Enumeration X) (q : X → Q) :
    stabilizationStage E q = Nat.card (ObservedValue q) - 1 := by
  have hcard : Nat.card (ObservedValue q) = (E.items.toFinset.image q).card :=
    Nat.subtype_card _ (by intro y; simp [E.complete])
  exact congrArg (fun n : Nat => n - 1) hcard.symm

/-- Executable channel synthesized from the observer at the proved stabilization stage. -/
def stabilizedEncoder
    {X : Type u} {Q : Type v} {V : Type w}
    [DecidableEq X] [DecidableEq Q] [DecidableEq V]
    (E : Enumeration X) (F : X → X) (q : X → Q)
    (P : X → V) :
    letI : Fintype X := E.toFintype
    X → Fin (fiberMultiplicity (orbitObserver F q (stabilizationStage E q)) P) := by
  letI : Fintype X := E.toFintype
  exact encode E (orbitObserver F q (stabilizationStage E q)) P

/-- The computed stabilization-stage channel licenses the target at that stage. -/
theorem stabilizedEncoder_licensed
    {X : Type u} {Q : Type v} {V : Type w}
    [DecidableEq X] [DecidableEq Q] [DecidableEq V]
    (E : Enumeration X) (F : X → X) (q : X → Q)
    (P : X → V) :
    Licensed (augmentObserver (orbitObserver F q (stabilizationStage E q))
      (stabilizedEncoder E F q P)) P := by
  letI : Fintype X := E.toFintype
  exact encode_licensed E (orbitObserver F q (stabilizationStage E q)) P

/-- Under observation-compatible dynamics, the channel computed once at the
stabilization stage is a permanent channel for every later or earlier stage. -/
theorem stabilizedEncoder_permanent
    {X : Type u} {Q : Type v} {V : Type w}
    [DecidableEq X] [DecidableEq Q] [DecidableEq V]
    (E : Enumeration X) (F : X → X) (q : X → Q)
    (hc : ObservationCompatible F q) (P : X → V) :
    ∀ n, Licensed (augmentObserver (orbitObserver F q n)
      (stabilizedEncoder E F q P)) P := by
  letI : Fintype X := E.toFintype
  letI : Finite (ObservedValue q) := Finite.of_surjective (observedValue q) (by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩)
  apply (fixed_channel_licenses_all_iff_at_image_bound F q hc P
    (stabilizedEncoder E F q P)).2
  simpa only [stabilizationStage_eq_image_bound] using stabilizedEncoder_licensed E F q P

/-- Consequently, existence of one permanent finite alphabet channel is decided
by the stabilized fiber capacity rather than an unbounded sequence of stages. -/
theorem permanent_channel_capacity_at_stabilization
    {X : Type u} {Q : Type v} {V : Type w}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) (m : Nat) :
    (∃ s : X → Fin m, ∀ n, Licensed (augmentObserver (orbitObserver F q n) s) P) ↔
      ∀ o, Finite (FiberTargetValues
        (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P o) ∧
        Nat.card (FiberTargetValues
          (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P o) ≤ m :=
  permanent_fin_channel_iff_fiber_capacity F q hc P m

/-! ## Concrete capacity fixture -/

/-- Three target values collapsed into one observation require a three-symbol
side channel and two fixed-length bits. -/
def threeValueEnumeration : Enumeration (Fin 3) where
  items := [0, 1, 2]
  nodup := by decide
  complete := by intro x; fin_cases x <;> decide

@[simp] theorem three_values_require_three_symbols :
    letI := threeValueEnumeration.toFintype
    alphabetSize threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x) = 3 := by
  decide

@[simp] theorem three_values_require_two_bits :
    letI := threeValueEnumeration.toFintype
    Nat.clog 2 (alphabetSize threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x)) = 2 := by
  change Nat.clog 2 3 = 2
  rw [Nat.clog_of_two_le (by decide) (by decide)]
  norm_num [Nat.clog_eq_one (by decide : 2 ≤ 2) (by decide : 2 ≤ 2)]

end OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
