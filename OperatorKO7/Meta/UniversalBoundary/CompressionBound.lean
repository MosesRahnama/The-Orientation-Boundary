import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# Compression capacity boundary

This module gives a finite counting boundary for lossless compression into all
strictly shorter Boolean words.  It concerns worst-case losslessness only;
entropy models, distributions, and typical-input compression are outside scope.

Relation: equality of finite encodings and identity verdicts.
Closure: not applicable.
Strategy: finite cardinality and fiber capacity.
Trust: kernel-only.
Scope: fixed-length Boolean words and strictly shorter outputs.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.CompressionBound

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-- Boolean words of length `n`. -/
abbrev Word (n : Nat) := Fin n → Bool

/-- A Boolean word whose recorded length is strictly below `n`. -/
abbrev Short (n : Nat) := Σ m : Fin n, Word m.1

/--
Proves: the number of strictly shorter Boolean words is `2 ^ n - 1`.
Does not prove: any probabilistic or average-case compression claim.
Relation: the sigma-cardinality formula followed by the finite geometric sum.
Closure: not applicable.
Strategy: finite cardinality.
Trust: kernel-only.
Scope: every natural length `n`.
-/
theorem card_short (n : Nat) : Fintype.card (Short n) = 2 ^ n - 1 := by
  rw [Fintype.card_sigma]
  simp only [Word, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hgeom : (∑ i ∈ Finset.range n, 2 ^ i) * (2 - 1) + 1 = 2 ^ n :=
    geom_sum_mul_add 1 n
  rw [← Finset.sum_range]
  simpa using congrArg (fun k : Nat => k - 1) hgeom


/-- A lossless encoder into strictly shorter words, paired with its decoder. -/
structure Compressor (n : Nat) where
  encode : Word n → Short n
  decode : Short n → Word n
  lossless : ∀ w, decode (encode w) = w

/--
Proves: a lossless encoder is fiber-faithful for the identity verdict.
Does not prove: existence of such an encoder.
Relation: `Licensed C.encode id`.
Closure: not applicable.
Strategy: apply the decoder to equal encodings.
Trust: kernel-only.
Scope: every proposed `Compressor n`.
-/
theorem encode_licenses {n : Nat} (C : Compressor n) : Licensed C.encode id := by
  intro x y hxy
  calc
    x = C.decode (C.encode x) := (C.lossless x).symm
    _ = C.decode (C.encode y) := by rw [hxy]
    _ = y := C.lossless y

/--
Proves: length-`n` Boolean words have cardinality `2 ^ n`.
Does not prove: a compression statement.
Relation: function-space cardinality.
Closure: not applicable.
Strategy: finite cardinality.
Trust: kernel-only.
Scope: every natural length `n`.
-/
theorem card_word (n : Nat) : Fintype.card (Word n) = 2 ^ n := by
  simp [Word]

/--
Proves: for positive `n`, no lossless encoder maps every length-`n` word to a shorter word.
Does not prove: an average-case, non-total, or distribution-sensitive impossibility.
Relation: `additional_channel_card_lower_bound` applied to a unit observer and the encoder.
Closure: not applicable.
Strategy: fiber-capacity counting.
Trust: kernel-only.
Scope: positive finite Boolean word lengths.
-/
theorem no_compressor_shrinks_everything (n : Nat) (_hn : 0 < n) :
    IsEmpty (Compressor n) := by
  refine ⟨fun C => ?_⟩
  have hfactor : FactorsThrough (fun w : Word n => ((), C.encode w)) id := by
    intro x y hxy
    have henc : C.encode x = C.encode y := congrArg Prod.snd hxy
    calc
      x = C.decode (C.encode x) := (C.lossless x).symm
      _ = C.decode (C.encode y) := by rw [henc]
      _ = y := C.lossless y
  have hbound :=
    additional_channel_card_lower_bound (fun _ : Word n => ()) id C.encode hfactor
  rw [fiberMultiplicity_const] at hbound
  have himage : (Finset.univ.image (id : Word n → Word n)).card = Fintype.card (Word n) := by simp
  rw [himage, card_word, card_short] at hbound
  have hpow : 0 < 2 ^ n := pow_pos (by decide) n
  omega


/--
Proves: every map from length-`n` words to shorter words has a collision.
Does not prove: which input pair a practical encoder will collide on.
Relation: failure of `FactorsThrough f id`, normalized to an explicit pair.
Closure: not applicable.
Strategy: the unit-observer fiber bound and finite counting.
Trust: kernel-only.
Scope: every total `f : Word n → Short n`.
-/
theorem exists_collision_of_short_output (n : Nat) (f : Word n → Short n) :
    ∃ w v, w ≠ v ∧ f w = f v := by
  have hnot : ¬ FactorsThrough f id := by
    intro hf
    have hjoint : FactorsThrough (fun w : Word n => ((), f w)) id := by
      intro x y hxy
      exact hf (congrArg Prod.snd hxy)
    have hbound :=
      additional_channel_card_lower_bound (fun _ : Word n => ()) id f hjoint
    rw [fiberMultiplicity_const] at hbound
    have himage : (Finset.univ.image (id : Word n → Word n)).card = Fintype.card (Word n) := by simp
    rw [himage, card_word, card_short] at hbound
    have hpow : 0 < 2 ^ n := pow_pos (by decide) n
    omega
  obtain ⟨w, v, hfv, hwv⟩ :=
    (not_factorsThrough_iff_exists_collision f id).1 hnot
  exact ⟨w, v, hwv, hfv⟩

/--
Proves: the identity verdict is not determined by any strictly-shorter output map.
Does not prove: nonexistence of lossy or non-total encoders.
Relation: negated `FactorsThrough f id`.
Closure: not applicable.
Strategy: apply the explicit collision.
Trust: kernel-only.
Scope: every total `f : Word n → Short n`.
-/
theorem short_output_does_not_license (n : Nat) (f : Word n → Short n) :
    ¬ FactorsThrough f id := by
  obtain ⟨w, v, hwv, hfv⟩ := exists_collision_of_short_output n f
  exact not_factorsThrough_of_collision ⟨hfv, hwv⟩

/--
Proves: every shorter-output map at length above one instantiates a typed boundary.
Does not prove: a canonical choice of the colliding inputs.
Relation: equal encoded observations with distinct identity verdicts.
Closure: not applicable.
Strategy: package the finite collision.
Trust: kernel-only.
Scope: `1 < n` and total shorter-output maps.
-/
noncomputable def compressionBoundary (n : Nat) (_hn : 1 < n) (f : Word n → Short n) :
    TypedBoundary :=
  let h := exists_collision_of_short_output n f
  let w := Classical.choose h
  let v := Classical.choose (Classical.choose_spec h)
  { State := Word n
    Obs := Short n
    Verdict := Word n
    observe := f
    verdict := id
    s₁ := w
    s₂ := v
    obs_eq := (Classical.choose_spec (Classical.choose_spec h)).2
    verdict_ne := (Classical.choose_spec (Classical.choose_spec h)).1 }

/--
Proves: the compression boundary obeys the universal no-observation-only-verdict law.
Does not prove: that the larger escape output is unavailable.
Relation: `TypedBoundary.verdict_not_observation_function`.
Closure: not applicable.
Strategy: specialize the universal boundary law.
Trust: kernel-only.
Scope: `1 < n` and total shorter-output maps.
-/
theorem compressionBoundary_obeys_law (n : Nat) (hn : 1 < n)
    (f : Word n → Short n) :
    ¬ ∃ g : Short n → Word n, ∀ w, id w = g (f w) :=
  by
    simpa [compressionBoundary] using
      TypedBoundary.verdict_not_observation_function (compressionBoundary n hn f)

/-- Escape encoding into the unrestricted right summand. -/
def escapeEncode {n : Nat} (w : Word n) : Short n ⊕ Word n := Sum.inr w

/-- Escape decoding; the left summand uses the all-false fallback word. -/
def escapeDecode {n : Nat} : Short n ⊕ Word n → Word n
  | Sum.inl _ => fun _ => false
  | Sum.inr w => w

/--
Proves: adding the unrestricted right summand permits a lossless total encoding.
Does not prove: that every word receives a strictly shorter representation.
Relation: `escapeDecode (escapeEncode w) = w`.
Closure: not applicable.
Strategy: right-summand inclusion.
Trust: kernel-only.
Scope: every natural word length.
-/
theorem escape_lossless {n : Nat} (w : Word n) :
    escapeDecode (escapeEncode w) = w := rfl

/-- Two explicitly represented inputs, corresponding to words `00` and `01`. -/
abbrev RestrictedTwo := Bool

/-- Embed the two restricted inputs as actual length-two words. -/
def restrictedWord (b : RestrictedTwo) : Word 2 :=
  fun i => if i.1 = 0 then false else b

/-- Encode the two restricted inputs as length-one words. -/
def restrictedEncode (b : RestrictedTwo) : Short 2 :=
  ⟨⟨1, by decide⟩, fun _ => b⟩

/-- Decode a shorter word when it contains a zeroth position. -/
def restrictedDecode (s : Short 2) : RestrictedTwo :=
  if h : 0 < s.1.1 then s.2 ⟨0, h⟩ else false

/--
Proves: the explicit two-input restriction has a lossless strictly-shorter encoding.
Does not prove: an encoding of all four length-two words.
Relation: left inverse for `restrictedEncode`.
Closure: not applicable.
Strategy: store the varying bit in a length-one output.
Trust: kernel-only.
Scope: exactly the represented pair `00`, `01`.
-/
theorem restricted_two_lossless (b : RestrictedTwo) :
    restrictedDecode (restrictedEncode b) = b := by
  simp [restrictedDecode, restrictedEncode]

/--
Proves: the two-input restricted encoder is injective.
Does not prove: injectivity on all length-two words.
Relation: injectivity of `restrictedEncode`.
Closure: not applicable.
Strategy: its explicit left inverse.
Trust: kernel-only.
Scope: exactly the represented pair `00`, `01`.
-/
theorem restrictedEncode_injective : Function.Injective restrictedEncode :=
  Function.LeftInverse.injective restricted_two_lossless

/--
Proves: at length two the shorter-output carrier has three values, fewer than the four inputs.
Does not prove: a claim at another length.
Relation: concrete cardinality inequality.
Closure: not applicable.
Strategy: decidable finite computation.
Trust: kernel-only via `decide`.
Scope: `n = 2`.
-/
theorem short_two_cardinality :
    Fintype.card (Short 2) = 3 ∧ Fintype.card (Word 2) = 4 ∧
      Fintype.card (Short 2) < Fintype.card (Word 2) := by
  decide

/--
Proves: no lossless all-input compressor exists at length two.
Does not prove: refusal of the explicit two-input restricted encoder.
Relation: specialization of `no_compressor_shrinks_everything`.
Closure: not applicable.
Strategy: reuse the general capacity bound.
Trust: kernel-only.
Scope: `n = 2`.
-/
theorem no_compressor_two : IsEmpty (Compressor 2) :=
  no_compressor_shrinks_everything 2 (by decide)

end OperatorKO7.Meta.UniversalBoundary.CompressionBound
