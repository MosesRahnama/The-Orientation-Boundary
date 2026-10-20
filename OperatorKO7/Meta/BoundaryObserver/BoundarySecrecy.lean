import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

set_option autoImplicit false

/-!
# Boundary secrecy: exact M6.15 goals

Three source-bound proofs for secrecy at the ciphertext pole, a fair one-time pad,
and Shannon's positive-key support lower bound.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy

open scoped BigOperators
open ProtocolResolution BoundarySingularity

noncomputable section

/-- The ciphertext law of a message under a key law. -/
def cipherLaw {K M C : Type} [Fintype K] [DecidableEq C] (key : FiniteLaw K) (enc : K → M → C)
    (m : M) (c : C) : ℝ :=
  ∑ k, if enc k m = c then key.mass k else 0

/-- M6.15(i): perfect secrecy for two messages places them at the pole of the ciphertext reading. -/
def PerfectSecrecyPoleGoal : Prop :=
  ∀ (K M C : Type) [Fintype K] [Fintype C] [DecidableEq C] (key : FiniteLaw K)
    (enc : K → M → C) (m₀ m₁ : M),
    (∀ c, cipherLaw key enc m₀ c = cipherLaw key enc m₁ c) →
      discrimination (cipherLaw key enc m₀) (cipherLaw key enc m₁) = 0

/-- M6.15(ii): the pad on one bit with a fair key gives the uniform ciphertext law for each
message. -/
def OneTimePadGoal : Prop :=
  ∀ key : FiniteLaw Bool, (∀ k, key.mass k = 1 / 2) → ∀ m c : Bool,
    cipherLaw key (fun k m => xor k m) m c = 1 / 2

/-- M6.15(iii): a decryptable cipher with one ciphertext law for all messages has at least as many
keys of positive mass as messages: the symbol that merges a separated pair carries as many values
as the symbol that separates a merged one. -/
def ShannonKeyGoal : Prop :=
  ∀ (K M C : Type) [Fintype K] [Fintype M] [Fintype C] [DecidableEq C] (key : FiniteLaw K)
    (enc : K → M → C) (dec : K → C → M),
    (∀ k m, dec k (enc k m) = m) → (∀ m m' c, cipherLaw key enc m c = cipherLaw key enc m' c) →
      Fintype.card M ≤ (Finset.univ.filter (fun k => 0 < key.mass k)).card

/-- Pointwise equal ciphertext laws have zero triangular discrimination. -/
theorem perfectSecrecyPoleGoal : PerfectSecrecyPoleGoal := by
  intro K M C _ _ _ key enc m₀ m₁ heq
  have hf : cipherLaw key enc m₀ = cipherLaw key enc m₁ := by
    funext c
    exact heq c
  rw [hf]
  simp [discrimination]

/-- For each message and ciphertext exactly one Boolean key has the required XOR. -/
theorem oneTimePadGoal : OneTimePadGoal := by
  intro key hfair m c
  cases m <;> cases c <;> simp [cipherLaw, hfair]

/-- Decryption injects messages into the strictly positive support of a secret key law. -/
theorem shannonKeyGoal : ShannonKeyGoal := by
  classical
  intro K M C _ _ _ _ key enc dec hdec hsecret
  by_cases hM : Nonempty M
  · obtain ⟨m₀⟩ := hM
    have hpositiveKey : ∃ k : K, 0 < key.mass k := by
      by_contra hn
      have hz (k : K) : key.mass k = 0 := by
        have hnpos : ¬ 0 < key.mass k := by
          intro hp
          exact hn ⟨k, hp⟩
        exact le_antisymm (le_of_not_gt hnpos) (key.nonnegative k)
      have ht := key.total
      simp [hz] at ht
    obtain ⟨k₀, hk₀⟩ := hpositiveKey
    let c₀ : C := enc k₀ m₀
    have hpositiveCipher : 0 < cipherLaw key enc m₀ c₀ := by
      have hnonneg (k : K) :
          0 ≤ (if enc k m₀ = c₀ then key.mass k else 0) := by
        split_ifs
        · exact key.nonnegative k
        · exact le_rfl
      have hle :
          (if enc k₀ m₀ = c₀ then key.mass k₀ else 0) ≤
            cipherLaw key enc m₀ c₀ := by
        unfold cipherLaw
        exact Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ k₀)
      have hleK : key.mass k₀ ≤ cipherLaw key enc m₀ c₀ := by
        simpa [c₀] using hle
      exact lt_of_lt_of_le hk₀ hleK
    have hfind (m : M) : ∃ k : K, 0 < key.mass k ∧ enc k m = c₀ := by
      have hrow : 0 < cipherLaw key enc m c₀ := by
        rw [hsecret m m₀ c₀]
        exact hpositiveCipher
      by_contra hn
      have hz (k : K) :
          (if enc k m = c₀ then key.mass k else 0) = 0 := by
        by_cases he : enc k m = c₀
        · have hnpos : ¬ 0 < key.mass k := by
            intro hp
            exact hn ⟨k, hp, he⟩
          have hkzero : key.mass k = 0 :=
            le_antisymm (le_of_not_gt hnpos) (key.nonnegative k)
          simp [he, hkzero]
        · simp [he]
      have hzero : cipherLaw key enc m c₀ = 0 := by
        unfold cipherLaw
        exact Finset.sum_eq_zero (fun k _ => hz k)
      exact (ne_of_gt hrow) hzero
    let pick (m : M) : K := Classical.choose (hfind m)
    have hpick (m : M) : 0 < key.mass (pick m) ∧ enc (pick m) m = c₀ :=
      Classical.choose_spec (hfind m)
    let f : M → {k : K // 0 < key.mass k} :=
      fun m => ⟨pick m, (hpick m).1⟩
    have hdecode (m : M) : dec (pick m) c₀ = m := by
      rw [← (hpick m).2]
      exact hdec (pick m) m
    have hinj : Function.Injective f := by
      intro m m' hf
      have hk : pick m = pick m' := congrArg Subtype.val hf
      calc
        m = dec (pick m) c₀ := (hdecode m).symm
        _ = dec (pick m') c₀ := congrArg (fun k => dec k c₀) hk
        _ = m' := hdecode m'
    have hcard :
        Fintype.card M ≤ Fintype.card {k : K // 0 < key.mass k} :=
      Fintype.card_le_of_injective f hinj
    simpa only [Fintype.card_subtype] using hcard
  · haveI : IsEmpty M := ⟨fun m => hM ⟨m⟩⟩
    simp

end

end OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy
