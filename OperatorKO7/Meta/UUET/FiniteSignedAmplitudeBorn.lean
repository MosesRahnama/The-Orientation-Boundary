import OperatorKO7.Meta.UUET.FiniteAmplitudeEntanglement

set_option autoImplicit false

/-!
# UUET finite signed-amplitude Born carrier (U-61)

This upgrades U-58 from a normalized probability weight to a *signed amplitude*:
a finite two-branch real amplitude `(a, b)` (not both zero) whose Born weights are
the squared-amplitude ratios

 `weightA = a^2 / (a^2 + b^2)`, `weightB = b^2 / (a^2 + b^2)`.

The denominator is strictly positive, the weights are nonnegative and normalized,
and they are *sign-gauge invariant*: flipping the sign of `a` or `b` leaves the
weights unchanged. This is the finite, real-signed analogue of the Born `|.|^2`
phase-gauge invariance (the sign is the discrete real shadow of a complex phase).
A signed amplitude induces a U-58 `TwoBranchWeight` (`p := weightA`) and its
amplitude entanglement is `weightA * weightB`, recovering the earlier carriers.

Scope and honesty: FINITE STRUCTURAL Lean over real amplitudes. The Born squaring
here is the finite ratio `a^2/(a^2+b^2)`; this is NOT Hilbert-space quantum
mechanics (no complex Hilbert space, no state vector, no Born postulate). The
reading as physical Born probabilities is a structural model, not a Lean claim.
No `sorry`, `admit`, new `axiom`, `native_decide`, `bv_decide`, `@[csimp]`,
`unsafe`, `partial`, or `opaque`. Headline declarations are `#print axioms`-checked
against the baseline whitelist `{propext, Classical.choice, Quot.sound}`.
-/

namespace OperatorKO7.Meta.UUET

noncomputable section

/-- A finite two-branch real signed amplitude `(a, b)`, not both zero. -/
structure SignedAmplitude where
  a : ℝ
  b : ℝ
  ne_zero : ¬ (a = 0 ∧ b = 0)

namespace SignedAmplitude

/-- The Born denominator `a^2 + b^2`. -/
def norm2 (s : SignedAmplitude) : ℝ := s.a ^ 2 + s.b ^ 2

/-- The Born denominator is strictly positive (the amplitudes are not both zero). -/
theorem norm2_pos (s : SignedAmplitude) : 0 < s.norm2 := by
  unfold norm2
  rcases not_and_or.mp s.ne_zero with ha | hb
  · have h : 0 < s.a ^ 2 := (sq_nonneg s.a).lt_of_ne (pow_ne_zero 2 ha).symm
    nlinarith [sq_nonneg s.b]
  · have h : 0 < s.b ^ 2 := (sq_nonneg s.b).lt_of_ne (pow_ne_zero 2 hb).symm
    nlinarith [sq_nonneg s.a]

theorem norm2_ne_zero (s : SignedAmplitude) : s.norm2 ≠ 0 := s.norm2_pos.ne'

end SignedAmplitude

/-- The Born weight of branch A: `a^2 / (a^2 + b^2)`. -/
def weightA (s : SignedAmplitude) : ℝ := s.a ^ 2 / s.norm2

/-- The Born weight of branch B: `b^2 / (a^2 + b^2)`. -/
def weightB (s : SignedAmplitude) : ℝ := s.b ^ 2 / s.norm2

theorem weightA_nonneg (s : SignedAmplitude) : 0 ≤ weightA s :=
  div_nonneg (sq_nonneg _) s.norm2_pos.le

theorem weightB_nonneg (s : SignedAmplitude) : 0 ≤ weightB s :=
  div_nonneg (sq_nonneg _) s.norm2_pos.le

/-- **Normalization.** The two Born weights sum to one. -/
theorem weights_normalized (s : SignedAmplitude) : weightA s + weightB s = 1 := by
  unfold weightA weightB
  rw [div_add_div_same]
  exact div_self s.norm2_ne_zero

theorem weightA_le_one (s : SignedAmplitude) : weightA s ≤ 1 := by
  have h := weights_normalized s
  have hb := weightB_nonneg s
  linarith

/-- **Sign-gauge invariance (branch A weight).** Flipping the sign of either
amplitude leaves the Born weight `weightA` unchanged. -/
theorem weightA_sign_gauge_invariant (s s' : SignedAmplitude)
    (ha : s'.a = -s.a) (hb : s'.b = -s.b) :
    weightA s' = weightA s := by
  have h2a : s'.a ^ 2 = s.a ^ 2 := by rw [ha]; ring
  have h2b : s'.b ^ 2 = s.b ^ 2 := by rw [hb]; ring
  unfold weightA SignedAmplitude.norm2
  rw [h2a, h2b]

/-- **Sign-gauge invariance (branch B weight).** -/
theorem weightB_sign_gauge_invariant (s s' : SignedAmplitude)
    (ha : s'.a = -s.a) (hb : s'.b = -s.b) :
    weightB s' = weightB s := by
  have h2a : s'.a ^ 2 = s.a ^ 2 := by rw [ha]; ring
  have h2b : s'.b ^ 2 = s.b ^ 2 := by rw [hb]; ring
  unfold weightB SignedAmplitude.norm2
  rw [h2a, h2b]

/-- The balanced signed amplitude `(1, 1)`. -/
def balancedSigned : SignedAmplitude where
  a := 1
  b := 1
  ne_zero := by norm_num

theorem balancedSigned_weightA : weightA balancedSigned = 1 / 2 := by
  unfold weightA balancedSigned SignedAmplitude.norm2; norm_num

theorem balancedSigned_weightB : weightB balancedSigned = 1 / 2 := by
  unfold weightB balancedSigned SignedAmplitude.norm2; norm_num

/-- A collapsed signed amplitude `(1, 0)`: all weight on branch A (certain). -/
def collapsedSigned : SignedAmplitude where
  a := 1
  b := 0
  ne_zero := by norm_num

theorem collapsedSigned_weightA : weightA collapsedSigned = 1 := by
  unfold weightA collapsedSigned SignedAmplitude.norm2; norm_num

theorem collapsedSigned_weightB : weightB collapsedSigned = 0 := by
  unfold weightB collapsedSigned SignedAmplitude.norm2; norm_num

/-- **Recovery of the U-58 `TwoBranchWeight`.** A signed amplitude induces a
normalized two-branch weight with `p := weightA`. -/
def SignedAmplitude.toTwoBranchWeight (s : SignedAmplitude) : TwoBranchWeight where
  p := weightA s
  nonneg := weightA_nonneg s
  le_one := weightA_le_one s

theorem toTwoBranchWeight_p (s : SignedAmplitude) :
    (s.toTwoBranchWeight).p = weightA s := rfl

theorem toTwoBranchWeight_q (s : SignedAmplitude) :
    (s.toTwoBranchWeight).q = weightB s := by
  unfold TwoBranchWeight.q SignedAmplitude.toTwoBranchWeight
  have h := weights_normalized s
  linarith

/-- **Recovery of `amplitudeEntanglement`.** The U-58 amplitude entanglement of
the induced two-branch weight is the product of the two Born weights. -/
theorem toTwoBranchWeight_amplitudeEntanglement (s : SignedAmplitude) :
    amplitudeEntanglement s.toTwoBranchWeight = weightA s * weightB s := by
  unfold amplitudeEntanglement
  rw [toTwoBranchWeight_p, toTwoBranchWeight_q]

/-- Non-vacuity: balanced `(1,1)` gives `(1/2, 1/2)`, collapsed `(1,0)` gives
`(1, 0)`, weights are always normalized and nonnegative, and the balanced
amplitude entanglement recovers `1/4`. -/
theorem finiteSignedAmplitudeBorn_nonvacuous :
    weightA balancedSigned = 1 / 2
      ∧ weightB balancedSigned = 1 / 2
      ∧ weightA collapsedSigned = 1
      ∧ weightB collapsedSigned = 0
      ∧ (∀ s : SignedAmplitude, weightA s + weightB s = 1)
      ∧ (∀ s : SignedAmplitude, 0 ≤ weightA s)
      ∧ amplitudeEntanglement balancedSigned.toTwoBranchWeight = 1 / 4 := by
  refine ⟨balancedSigned_weightA, balancedSigned_weightB, collapsedSigned_weightA,
    collapsedSigned_weightB, weights_normalized, weightA_nonneg, ?_⟩
  rw [toTwoBranchWeight_amplitudeEntanglement, balancedSigned_weightA,
    balancedSigned_weightB]
  norm_num

#print axioms SignedAmplitude.norm2_pos
#print axioms weightA_nonneg
#print axioms weights_normalized
#print axioms weightA_le_one
#print axioms weightA_sign_gauge_invariant
#print axioms weightB_sign_gauge_invariant
#print axioms toTwoBranchWeight_q
#print axioms toTwoBranchWeight_amplitudeEntanglement
#print axioms finiteSignedAmplitudeBorn_nonvacuous

end

end OperatorKO7.Meta.UUET
