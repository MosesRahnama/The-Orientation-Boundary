import OperatorKO7.Meta.BoundaryObserver.SecrecyGeneralMessages
import OperatorKO7.Meta.BoundaryObserver.TranscriptLaw

set_option autoImplicit false

/-!
# Perfect secrecy under arbitrary discrete priors

Manuscript: thm:secrecy-privacy(ii), the quantifier over every message prior.
The message type is arbitrary. Its normalized real masses can have infinite
support. Ciphertexts have a finite alphabet. The information is the convergent
logarithmic joint/product sum of the actual message-ciphertext law. Its entropy
identity is derived from that law, with no assumption on message entropy.
-/

namespace OperatorKO7.Meta.BoundaryObserver.SecrecyCountablePriors

open scoped BigOperators
open ProtocolResolution BoundarySingularity
open SecrecyGeneralMessages TranscriptLaw

noncomputable section

/-- Nonnegative real masses with total one on an arbitrary discrete carrier. -/
structure DiscretePrior (M : Type) where
  mass : M → ℝ
  nonnegative : ∀ m, 0 ≤ mass m
  total : HasSum mass 1

/-- A probability distribution has at least one message in its carrier. -/
theorem DiscretePrior.nonempty {M : Type} (π : DiscretePrior M) : Nonempty M := by
  have h : ∃ m, π.mass m ≠ 0 := by
    by_contra hn
    push_neg at hn
    have ht := π.total.tsum_eq
    simp [hn] at ht
  obtain ⟨m, _⟩ := h
  exact ⟨m⟩

/-- Each fixed-ciphertext source column is summable, bounded by the message prior. -/
theorem jointColumn_summable {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) (c : C) :
    Summable (fun m => π.mass m * (E m).mass c) :=
  Summable.of_nonneg_of_le
    (fun m => mul_nonneg (π.nonnegative m) ((E m).nonnegative c))
    (fun m => by nlinarith [(E m).mass_le_one c, π.nonnegative m]) π.total.summable

/-- The ciphertext marginal of the actual encryption experiment. -/
def ciphertextMass {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) (c : C) : ℝ :=
  ∑' m, π.mass m * (E m).mass c

theorem ciphertextMass_nonnegative {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) (c : C) :
    0 ≤ ciphertextMass E π c :=
  tsum_nonneg (fun m => mul_nonneg (π.nonnegative m) ((E m).nonnegative c))

/-- Summing both coordinates of the source law gives one. -/
theorem ciphertextMass_total {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) :
    (∑ c, ciphertextMass E π c) = 1 := by
  unfold ciphertextMass
  rw [← Summable.tsum_finsetSum (fun c _ => jointColumn_summable E π c)]
  have heq : (fun m => ∑ c, π.mass m * (E m).mass c) = π.mass := by
    funext m
    rw [← Finset.mul_sum, (E m).total, mul_one]
  rw [heq]
  exact π.total.tsum_eq

/-- The normalized finite output law comes from the given prior and reading. -/
def ciphertextLaw {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) : FiniteLaw C where
  mass := ciphertextMass E π
  nonnegative := ciphertextMass_nonnegative E π
  total := ciphertextMass_total E π

/-- Every finite output row has the same entropy upper bound. -/
theorem row_entropy_bounds {C : Type} [Fintype C] (P : FiniteLaw C) :
    0 ≤ entropy P.mass ∧ entropy P.mass ≤ Real.logb 2 (Fintype.card C) := by
  haveI : Nonempty C := by
    obtain ⟨c, _⟩ := Finset.nonempty_of_sum_ne_zero
      (show (∑ c, P.mass c) ≠ 0 by rw [P.total]; norm_num)
    exact ⟨c⟩
  exact ⟨entropy_nonnegative_of_bounds P.mass P.nonnegative P.mass_le_one,
    entropy_le_logb_card P.mass P.nonnegative P.total⟩

/-- Finite output entropy makes conditional output entropy summable even if
message entropy or the message support is infinite. -/
theorem conditionalEntropy_summable {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) :
    Summable (fun m => π.mass m * entropy (E m).mass) :=
  Summable.of_nonneg_of_le
    (fun m => mul_nonneg (π.nonnegative m) (row_entropy_bounds (E m)).1)
    (fun m => mul_le_mul_of_nonneg_left (row_entropy_bounds (E m)).2 (π.nonnegative m))
    (π.total.summable.mul_right (Real.logb 2 (Fintype.card C)))

/-- The uncertainty of a message slice of the source law is its probability
multiplied by the entropy of the specified ciphertext row. -/
theorem source_uncertainty {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) (m : M) :
    massUncertainty (fun c => π.mass m * (E m).mass c) =
      π.mass m * entropy (E m).mass := by
  rw [massUncertainty_scale, massUncertainty_of_total_one _ (E m).total]

/-- A normalized joint-law object, with finite ciphertext target and message
index, built from the actual prior and encryption rows. -/
def messageCiphertextLaw {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) : CountableTranscriptJointLaw C M where
  prior := ciphertextLaw E π
  cell := fun c m => π.mass m * (E m).mass c
  nonnegative := fun c m => mul_nonneg (π.nonnegative m) ((E m).nonnegative c)
  summable := jointColumn_summable E π
  target_marginal := fun _ => rfl
  uncertainty_summable := by
    have heq : (fun m => massUncertainty (fun c => π.mass m * (E m).mass c)) =
        (fun m => π.mass m * entropy (E m).mass) := funext (source_uncertainty E π)
    rw [heq]
    exact conditionalEntropy_summable E π

/-- The other marginal is the original message prior. -/
theorem messageCiphertextLaw_message_marginal {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) (m : M) :
    (messageCiphertextLaw E π).historyMass m = π.mass m := by
  change (∑ c, π.mass m * (E m).mass c) = π.mass m
  rw [← Finset.mul_sum, (E m).total, mul_one]

/-- Information is the summable logarithmic joint/product expression of the
same normalized law; no subtraction of two infinite entropies occurs. -/
def information {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) : ℝ :=
  (messageCiphertextLaw E π).information

/-- The finite-output Shannon identity follows from the joint-law definition. -/
theorem information_eq_entropy_sub {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : DiscretePrior M) :
    information E π = entropy (ciphertextMass E π) -
      ∑' m, π.mass m * entropy (E m).mass := by
  rw [information, CountableTranscriptJointLaw.information_eq_entropy_sub]
  change entropy (ciphertextMass E π) -
    (∑' m, massUncertainty (fun c => π.mass m * (E m).mass c)) = _
  simp_rw [source_uncertainty E π]

/-- Every previous finite-support prior is a normalized summable prior. -/
def ofFiniteSupport {M : Type} (π : FiniteSupportPrior M) : DiscretePrior M where
  mass := π.mass
  nonnegative := π.nonnegative
  total := by
    have h := hasSum_sum_of_ne_finset_zero π.zero_off
    simpa only [π.total] using h

/-- The general output marginal agrees with the finite-support marginal. -/
theorem finiteSupport_ciphertextMass {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : FiniteSupportPrior M) (c : C) :
    ciphertextMass E (ofFiniteSupport π) c =
      ∑ m : π.support, π.mass m * (E m).mass c := by
  change (∑' m, π.mass m * (E m).mass c) = _
  rw [tsum_eq_sum (s := π.support) (fun m hm => by rw [π.zero_off m hm, zero_mul])]
  exact (Finset.sum_coe_sort π.support (fun m => π.mass m * (E m).mass c)).symm

/-- The general logarithmic information agrees with the original finite joint-law MI. -/
theorem finiteSupport_information {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (π : FiniteSupportPrior M) :
    information E (ofFiniteSupport π) = supportInformation E π := by
  rw [information_eq_entropy_sub, supportInformation,
    jointMI_kernel (fun m : π.support => π.mass m) (fun m : π.support => (E m).mass)
      (fun m => (E m).total)]
  have hout : ciphertextMass E (ofFiniteSupport π) =
      (fun c => ∑ m : π.support, π.mass m * (E m).mass c) :=
    funext (finiteSupport_ciphertextMass E π)
  rw [hout]
  congr 1
  change (∑' m, π.mass m * entropy (E m).mass) = _
  rw [tsum_eq_sum (s := π.support)
    (fun m hm => by rw [π.zero_off m hm, zero_mul])]
  exact (Finset.sum_coe_sort π.support (fun m => π.mass m * entropy (E m).mass)).symm

/-- Equal ciphertext rows give zero information under every normalized prior,
including infinite-support priors. -/
theorem equal_rows_zero_information {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) (heq : ∀ m m' c, (E m).mass c = (E m').mass c)
    (π : DiscretePrior M) : information E π = 0 := by
  obtain ⟨m₀⟩ := π.nonempty
  have hrow (m : M) : (E m).mass = (E m₀).mass := funext (heq m m₀)
  have hout : ciphertextMass E π = (E m₀).mass := by
    funext c
    unfold ciphertextMass
    simp_rw [heq _ m₀ c]
    simpa only [one_mul] using (π.total.mul_right ((E m₀).mass c)).tsum_eq
  have hc : (∑' m, π.mass m * entropy (E m).mass) = entropy (E m₀).mass := by
    simp_rw [hrow]
    simpa only [one_mul] using (π.total.mul_right (entropy (E m₀).mass)).tsum_eq
  rw [information_eq_entropy_sub, hout, hc, sub_self]

/-- The every-prior secrecy equivalence on an arbitrary discrete message type. -/
theorem equal_rows_iff_every_prior_zero {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) :
    (∀ m m' c, (E m).mass c = (E m').mass c) ↔
      ∀ π : DiscretePrior M, information E π = 0 := by
  constructor
  · exact equal_rows_zero_information E
  · intro h
    apply (SecrecyGeneralMessages.equal_rows_iff_zero_information E).mpr
    intro π
    rw [← finiteSupport_information E π]
    exact h (ofFiniteSupport π)

/-- Zero discrimination, equal rows and zero logarithmic information under
every normalized discrete prior are the same condition. -/
theorem perfect_secrecy_every_prior {M C : Type} [Fintype C]
    (E : M → FiniteLaw C) :
    ((∀ m m', discrimination (E m).mass (E m').mass = 0) ↔
      (∀ m m' c, (E m).mass c = (E m').mass c)) ∧
    ((∀ m m' c, (E m).mass c = (E m').mass c) ↔
      ∀ π : DiscretePrior M, information E π = 0) :=
  ⟨zero_discrimination_iff_equal_rows E, equal_rows_iff_every_prior_zero E⟩

/-- A geometric prior assigns positive mass to every natural-number message. -/
def geometricPrior : DiscretePrior ℕ where
  mass := fun n => (1 / 2 : ℝ) ^ (n + 1)
  nonnegative := fun _ => by positivity
  total := by
    have h := hasSum_geometric_two.mul_left (1 / 2)
    have hf : (fun n : ℕ => (1 : ℝ) / 2 * (1 / 2) ^ n) =
        (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      funext n
      rw [pow_succ]
      ring
    rw [hf] at h
    norm_num at h
    exact h

theorem geometricPrior_positive (n : ℕ) : 0 < geometricPrior.mass n := by
  unfold geometricPrior
  positivity

/-- The prior's support is infinite, so this case lies beyond finite-support priors. -/
theorem geometricPrior_infinite_support :
    Set.Infinite {n : ℕ | geometricPrior.mass n ≠ 0} := by
  have hs : {n : ℕ | geometricPrior.mass n ≠ 0} = Set.univ := by
    ext n
    simp [(geometricPrior_positive n).ne']
  rw [hs]
  exact Set.infinite_univ

/-- A real infinite-support instance of the every-prior secrecy theorem. -/
theorem geometric_secret_reading_zero :
    information (fun _ : ℕ => fairCoin) geometricPrior = 0 :=
  equal_rows_zero_information _ (fun _ _ _ => rfl) geometricPrior

end
end OperatorKO7.Meta.BoundaryObserver.SecrecyCountablePriors
