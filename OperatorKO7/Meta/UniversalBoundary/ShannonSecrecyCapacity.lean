import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph

/-!
# Shannon's 1949 key bound as a fiber-capacity instance

Shannon's theorem in its probabilistic form (Shannon, "Communication theory of secrecy
systems", Bell System Technical Journal 28, 1949) is ESTABLISHED and is cited, never
re-derived. This module proves the support-level consequence: the combinatorial condition
that every ciphertext reachable from one message is reachable from every message, which
the probabilistic definition implies when the ciphertext distribution does not depend on
the message.

On that condition the ciphertext is the cheap observer, the message is the verdict, the
key is the licensing channel, and `additional_channel_card_lower_bound` forces
`Fintype.card M ≤ Fintype.card K`.

```
Relation: observer-fiber equality of `ciphertextObs` against `messageVerdict`, with
          `keyChannel` as the added licensing coordinate.
Closure:  not applicable; no rewriting closure is claimed.
Strategy: not applicable.
Trust:    kernel-only; finite Bool fixtures use `decide`. Shannon 1949 remains ESTABLISHED
          citation, not a kernel theorem.
Scope:    support-level perfect secrecy on a cipher `Cipher K M C`; the cardinality bound
          uses finite `K` and `M` with decidable equality on `C` and `M`.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.ShannonSecrecyCapacity

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.Confusability

/-! ## NameGate -/

#check @TypedBoundary
#check @TypedBoundary.verdict_not_observation_function
#check @OperationallyInexpressibleAt
#check @FactorsThrough
#check @not_factorsThrough_of_collision
#check @fiberVerdicts
#check @fiberMultiplicity
#check @additional_channel_card_lower_bound
#check @Licensed
#check @licensed_iff_factorsThrough
#check @augmentObserver
#check @mem_fiberVerdicts
#check @fiberVerdicts_card_le

/-- A cipher: encryption of a message under a key, with a matching decryption. -/
structure Cipher (K M C : Type) where
  enc : K → M → C
  dec : K → C → M
  dec_enc : ∀ k m, dec k (enc k m) = m

/-- Support-level perfect secrecy: every ciphertext reachable from one message is
reachable from every message. -/
def PerfectSecrecySupport {K M C : Type} (E : Cipher K M C) : Prop :=
  ∀ (m m' : M) (c : C), (∃ k, E.enc k m = c) → ∃ k', E.enc k' m' = c

/-- State space: a key-message pair. -/
abbrev St (K M : Type) := K × M

/-- Cheap observer: the ciphertext of the stored key and message. -/
def ciphertextObs {K M C : Type} (E : Cipher K M C) : St K M → C :=
  fun p => E.enc p.1 p.2

/-- Verdict: the stored message. -/
def messageVerdict {K M : Type} : St K M → M :=
  Prod.snd

/-- Licensing channel: the stored key. -/
def keyChannel {K M : Type} : St K M → K :=
  Prod.fst

/--
Proves: decryption licenses the message through the joint observer of ciphertext and key.
Does not prove: that the ciphertext alone licenses the message, or Shannon's probabilistic theorem.
Relation: `Licensed` of `augmentObserver (ciphertextObs E) keyChannel` against `messageVerdict`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; one use of `Cipher.dec_enc`.
Scope: every cipher `E : Cipher K M C`; no finiteness hypothesis.
-/
theorem key_licenses_message {K M C : Type} (E : Cipher K M C) :
    Licensed (augmentObserver (ciphertextObs E) keyChannel) messageVerdict := by
  intro p q h
  have henc : E.enc p.1 p.2 = E.enc q.1 q.2 := by
    simpa [augmentObserver, ciphertextObs, keyChannel] using congrArg Prod.fst h
  have hk : p.1 = q.1 := by
    simpa [augmentObserver, ciphertextObs, keyChannel] using congrArg Prod.snd h
  calc
    messageVerdict p = E.dec p.1 (E.enc p.1 p.2) := (E.dec_enc p.1 p.2).symm
    _ = E.dec p.1 (E.enc q.1 q.2) := by rw [henc]
    _ = E.dec q.1 (E.enc q.1 q.2) := by rw [hk]
    _ = messageVerdict q := E.dec_enc q.1 q.2

/--
Proves: under support-level perfect secrecy, one ciphertext fiber contains two states with
distinct messages.
Does not prove: a cardinality bound, or that every pair of states collides.
Relation: `OperationallyInexpressibleAt (ciphertextObs E) messageVerdict`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; the colliding pair is constructed from `PerfectSecrecySupport`.
Scope: a cipher `E`, a key `k₀`, and two distinct messages `m₁`, `m₂`.
-/
theorem ciphertext_alone_collides {K M C : Type} (E : Cipher K M C)
    (hPS : PerfectSecrecySupport E) (k₀ : K) {m₁ m₂ : M} (hm : m₁ ≠ m₂) :
    ∃ p q : St K M, OperationallyInexpressibleAt (ciphertextObs E) messageVerdict p q := by
  obtain ⟨k', hk'⟩ := hPS m₁ m₂ (E.enc k₀ m₁) ⟨k₀, rfl⟩
  refine ⟨(k₀, m₁), (k', m₂), ?_⟩
  constructor
  · change E.enc k₀ m₁ = E.enc k' m₂
    exact hk'.symm
  · exact hm

/--
Proves: the ciphertext observer does not factor the message verdict under support-level
perfect secrecy, once two distinct messages exist.
Does not prove: the key-cardinality bound.
Relation: `¬ FactorsThrough (ciphertextObs E) messageVerdict`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `not_factorsThrough_of_collision` on `ciphertext_alone_collides`.
Scope: a cipher `E`, a key `k₀`, and two distinct messages `m₁`, `m₂`.
-/
theorem ciphertext_does_not_license {K M C : Type} (E : Cipher K M C)
    (hPS : PerfectSecrecySupport E) (k₀ : K) {m₁ m₂ : M} (hm : m₁ ≠ m₂) :
    ¬ FactorsThrough (ciphertextObs E) messageVerdict := by
  obtain ⟨p, q, hcoll⟩ := ciphertext_alone_collides E hPS k₀ hm
  exact not_factorsThrough_of_collision hcoll

section FiniteBound

variable {K M C : Type}
variable [Fintype K] [Fintype M] [DecidableEq C] [DecidableEq M]

/--
Proves: under support-level perfect secrecy, the ciphertext fiber of `E.enc k₀ m₀`
contains every message.
Does not prove: a uniform distribution on that fiber, or Shannon's probabilistic theorem.
Relation: `fiberVerdicts (ciphertextObs E) messageVerdict`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `mem_fiberVerdicts` and `PerfectSecrecySupport`.
Scope: finite `K` and `M` with decidable equality on `C` and `M`.
-/
theorem fiber_holds_every_message (E : Cipher K M C) (hPS : PerfectSecrecySupport E)
    (k₀ : K) (m₀ : M) :
    fiberVerdicts (ciphertextObs E) messageVerdict (E.enc k₀ m₀) = Finset.univ := by
  ext m
  constructor
  · intro _
    exact Finset.mem_univ m
  · intro _
    refine mem_fiberVerdicts.2 ?_
    obtain ⟨k', hk'⟩ := hPS m₀ m (E.enc k₀ m₀) ⟨k₀, rfl⟩
    exact ⟨(k', m), hk', rfl⟩

/--
Proves: support-level perfect secrecy forces fiber multiplicity at least `Fintype.card M`.
Does not prove: the key-cardinality bound by itself.
Relation: `fiberMultiplicity (ciphertextObs E) messageVerdict`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `fiber_holds_every_message` and `fiberVerdicts_card_le`.
Scope: nonempty finite `K` and `M` with decidable equality on `C` and `M`.
-/
theorem fiberMultiplicity_ge_card_M (E : Cipher K M C) (hPS : PerfectSecrecySupport E)
    [Nonempty K] [Nonempty M] :
    Fintype.card M ≤ fiberMultiplicity (ciphertextObs E) messageVerdict := by
  let k₀ : K := Classical.choice ‹Nonempty K›
  let m₀ : M := Classical.choice ‹Nonempty M›
  have hfiber := fiber_holds_every_message E hPS k₀ m₀
  have hcard :
      (fiberVerdicts (ciphertextObs E) messageVerdict (E.enc k₀ m₀)).card =
        Fintype.card M := by
    rw [hfiber, Finset.card_univ]
  rw [← hcard]
  exact fiberVerdicts_card_le (ciphertextObs E) messageVerdict (E.enc k₀ m₀)

/--
Proves: a support-level perfectly secret cipher on finite nonempty `K` and `M` satisfies
`Fintype.card M ≤ Fintype.card K`.
Does not prove: Shannon's probabilistic theorem, or a bound for infinite carriers.
Relation: `additional_channel_card_lower_bound` on `ciphertextObs`, `messageVerdict`, and
`keyChannel`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; the bound is the fiber-capacity law, not a direct pigeonhole.
Scope: nonempty finite `K` and `M` with decidable equality on `C` and `M`.
-/
theorem shannon_key_bound (E : Cipher K M C) (hPS : PerfectSecrecySupport E)
    [Nonempty K] [Nonempty M] : Fintype.card M ≤ Fintype.card K :=
  (fiberMultiplicity_ge_card_M E hPS).trans
    (additional_channel_card_lower_bound (ciphertextObs E) messageVerdict keyChannel
      ((licensed_iff_factorsThrough
          (augmentObserver (ciphertextObs E) keyChannel) messageVerdict).1
        (key_licenses_message E)))

end FiniteBound

/-- Binary one-time pad: encryption and decryption are both `xor`. -/
def oneTimePad : Cipher Bool Bool Bool :=
  { enc := xor, dec := xor, dec_enc := by decide }

/--
Proves: the binary one-time pad satisfies support-level perfect secrecy.
Does not prove: Shannon's probabilistic theorem for this cipher.
Relation: `PerfectSecrecySupport oneTimePad`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; finite Bool case analysis on the recovering key `xor c m'`.
Scope: `oneTimePad` on `Bool`.
-/
theorem oneTimePad_perfect : PerfectSecrecySupport oneTimePad := by
  intro _m m' c _h
  refine ⟨xor c m', ?_⟩
  change xor (xor c m') m' = c
  cases m' <;> cases c <;> rfl

/--
Proves: the ciphertext fiber multiplicity of the binary one-time pad is 2.
Does not prove: the same multiplicity for every cipher, or a probabilistic entropy claim.
Relation: `fiberMultiplicity (ciphertextObs oneTimePad) messageVerdict`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; finite Bool evaluation by `decide`.
Scope: `oneTimePad` on `Bool`.
-/
theorem oneTimePad_fiberMultiplicity :
    fiberMultiplicity (ciphertextObs oneTimePad) messageVerdict = 2 := by
  decide

/-- Binary one-time pad as a `TypedBoundary`: ciphertext `false` from `(false, false)` and
`(true, true)` with opposite messages. -/
def shannonBoundary : TypedBoundary where
  State := Bool × Bool
  Obs := Bool
  Verdict := Bool
  observe := ciphertextObs oneTimePad
  verdict := messageVerdict
  s₁ := (false, false)
  s₂ := (true, true)
  obs_eq := by decide
  verdict_ne := by decide

/--
Proves: `shannonBoundary` obeys the universal law: the message is not a function of the
ciphertext.
Does not prove: the key-cardinality bound (that is `shannon_key_bound`).
Relation: `TypedBoundary.verdict_not_observation_function`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; one application of the imported universal law.
Scope: the fixture `shannonBoundary`.
-/
theorem shannonBoundary_obeys_law :
    ¬ ∃ f : shannonBoundary.Obs → shannonBoundary.Verdict,
      ∀ s, shannonBoundary.verdict s = f (shannonBoundary.observe s) :=
  TypedBoundary.verdict_not_observation_function shannonBoundary

/-- Identity cipher: the ciphertext is the message, independent of the key. -/
def identityCipher : Cipher Bool Bool Bool :=
  { enc := fun _ m => m, dec := fun _ c => c, dec_enc := by intros; rfl }

/--
Proves: the identity cipher fails support-level perfect secrecy.
Does not prove: anything about other ciphers.
Relation: `¬ PerfectSecrecySupport identityCipher`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; ciphertext `false` of message `false` is unreachable from message `true`.
Scope: `identityCipher` on `Bool`.
-/
theorem identityCipher_not_perfect : ¬ PerfectSecrecySupport identityCipher := by
  intro h
  obtain ⟨_, hk'⟩ := h false true false ⟨false, rfl⟩
  simp [identityCipher] at hk'

/--
Proves: the identity cipher's ciphertext already licenses the message, so no key channel
is required.
Does not prove: perfect secrecy, which this cipher fails.
Relation: `Licensed (ciphertextObs identityCipher) messageVerdict`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; definitional equality of ciphertext and message.
Scope: `identityCipher` on `Bool`.
-/
theorem identityCipher_ciphertext_licenses :
    Licensed (ciphertextObs identityCipher) messageVerdict := by
  intro p q h
  simpa [ciphertextObs, messageVerdict, identityCipher] using h

example : Fintype.card Bool ≤ Fintype.card Bool :=
  shannon_key_bound oneTimePad oneTimePad_perfect

end OperatorKO7.Meta.UniversalBoundary.ShannonSecrecyCapacity
