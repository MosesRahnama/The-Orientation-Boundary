import OperatorKO7.Meta.UUET.HolographicConnection

set_option autoImplicit false

/-!
# UUET ε-N gating law (Section 53)

This module mechanizes the finite carrier behind UUET Section 53.
It records the core gating theorem (Theorem 53.1), four product-form rows
(UUET/Landauer, Fisher, Heisenberg, Hoeffding), the distinct
Margolus-Levitin rate row, the Cramér-Rao saturation proposition, the firing-rate
bound, the Bekenstein upper bound, the biconditional (below threshold
no durable commit), and a falsifier predicate.

Claim type: PROVEN-IN-LEAN for the finite rational/Nat bookkeeping surface.
The physical Heisenberg/Bekenstein readings are structural models.
-/

namespace OperatorKO7.Meta.UUET

/-- The five Section 53 frameworks. Four are product-form laws; the
Margolus-Levitin row is a rate law. -/
inductive GatingFrameworkKind where
  | uuetLandauer
  | cramerRao
  | heisenberg
  | hoeffding
  | margolusLevitin
  deriving DecidableEq

/-- The five-row gating universality registry. -/
def gatingFrameworkRegistry : List GatingFrameworkKind :=
  [.uuetLandauer, .cramerRao, .heisenberg, .hoeffding, .margolusLevitin]

/-- Section 53.8 has exactly five universality rows. -/
theorem gatingFrameworkRegistry_length :
    gatingFrameworkRegistry.length = 5 := rfl

/-- Rational critical-amplification threshold `ln2/(2 epsilon^2)`. -/
def criticalAmplification (epsilon : ℚ) : ℚ :=
  (693 / 1000 : ℚ) / (2 * epsilon * epsilon)

/-- Integer critical-amplification count, the natural ceiling of the rational
threshold. -/
def criticalAmplificationCount (epsilon : ℚ) : ℕ :=
  ⌈criticalAmplification epsilon⌉₊

/-- The integer count is the least natural number at or above the rational
threshold. -/
theorem criticalAmplification_le_count (epsilon : ℚ) :
    criticalAmplification epsilon ≤ (criticalAmplificationCount epsilon : ℚ) := by
  exact Nat.le_ceil (criticalAmplification epsilon)

/-- Minimum detectable signal: ε_min(N) = √(ln2/(2N)).
 Represented as the squared quantity ε_min²(N) = ln2/(2N) to stay rational. -/
def minSignalSquared (N : ℕ) : ℚ :=
  (693 / 1000 : ℚ) / (2 * (N : ℚ))

/-- A prospective B-event (ε, N, T) is gated when N ≥ N_c(ε). -/
def isGated (epsilon : ℚ) (N : ℕ) : Prop :=
  (N : ℚ) ≥ criticalAmplification epsilon

/-- Theorem 53.1 biconditional (forward): N < N_c → not gated. -/
theorem below_threshold_not_gated
    (epsilon : ℚ) (N : ℕ) (h : (N : ℚ) < criticalAmplification epsilon) :
    ¬ isGated epsilon N := by
  unfold isGated
  linarith

/-- Theorem 53.1 biconditional (backward): N ≥ N_c → gated. -/
theorem at_or_above_threshold_gated
    (epsilon : ℚ) (N : ℕ) (h : (N : ℚ) ≥ criticalAmplification epsilon) :
    isGated epsilon N := by
  unfold isGated
  exact h

/-- Section 53.1: the gating law is equivalent to ε²N ≥ ln2/2.
 Represented as: if N ≥ N_c(ε) then 2ε²N ≥ ln2 (up to ceiling rounding). -/
def gatingProduct (epsilon : ℚ) (N : ℕ) : ℚ :=
  2 * epsilon * epsilon * (N : ℚ)

/-- The gating threshold on the bare product ε²N, namely ln2/2 ≈ 693/2000.
 `gatingProduct` carries an explicit factor 2, so at threshold it equals
 ln2, that is twice this value; `gatingProduct_at_threshold` proves it. -/
def gatingThreshold : ℚ := 693 / 2000

/-- Fisher information at θ=0 for binary distinction P = (1/2+θ, 1/2-θ).
 I_F(0) = 4. -/
def binaryFisherInformation : ℚ := 4

/-- Proposition 53.3: Cramér-Rao saturation gives ε² ≥ 1/(4N).
 N_CR = 1/(4ε²), and N_c = 2·ln2 · N_CR (`criticalAmplification_eq_ratio_mul_cramerRao`). -/
def cramerRaoBound (N : ℕ) : ℚ :=
  1 / (4 * (N : ℚ))

/-- The Cramér-Rao minimum N for signal ε: N_CR = 1/(4ε²). -/
def cramerRaoMinimumN (epsilon : ℚ) : ℚ :=
  1 / (4 * epsilon * epsilon)

/-- The ratio N_c / N_CR, the bit/nat conversion.

`N_c(ε) = ln2/(2ε²)` and `N_CR(ε) = 1/(4ε²)`, so the ratio is
`(ln2/(2ε²)) · 4ε² = 2·ln2 ≈ 693/500`, proved for every nonzero `ε` by
`criticalAmplification_eq_ratio_mul_cramerRao` and
`bitNatConversionRatio_eq_quotient`.

CORRECTED 2026-08-24: this was `693/2000` (that is ln2/2, a factor of four
low) with a docstring asserting `N_c = (ln2/8)·N_CR`, which the two
definitions above do not satisfy. The value and both derivations are now
carried by theorems instead of by a comment. -/
def bitNatConversionRatio : ℚ := 693 / 500

/-- The critical amplification count is the Cramér-Rao minimum scaled by the
bit/nat conversion ratio: `N_c(ε) = 2·ln2 · N_CR(ε)` for every nonzero `ε`. -/
theorem criticalAmplification_eq_ratio_mul_cramerRao
    (epsilon : ℚ) (h : epsilon ≠ 0) :
    criticalAmplification epsilon
      = bitNatConversionRatio * cramerRaoMinimumN epsilon := by
  unfold criticalAmplification bitNatConversionRatio cramerRaoMinimumN
  field_simp
  ring

/-- The same fact as a quotient: `N_c(ε) / N_CR(ε) = 2·ln2`, independent of `ε`. -/
theorem bitNatConversionRatio_eq_quotient
    (epsilon : ℚ) (h : epsilon ≠ 0) :
    criticalAmplification epsilon / cramerRaoMinimumN epsilon
      = bitNatConversionRatio := by
  have hCR : cramerRaoMinimumN epsilon ≠ 0 := by
    unfold cramerRaoMinimumN
    field_simp
  rw [criticalAmplification_eq_ratio_mul_cramerRao epsilon h]
  field_simp

/-- At the critical count the factor-2 `gatingProduct` equals ln2, which is
twice `gatingThreshold`. This is the relation the two definitions' names
invite and it is stated here rather than assumed. -/
theorem gatingProduct_at_threshold (epsilon : ℚ) (h : epsilon ≠ 0) :
    2 * epsilon * epsilon * criticalAmplification epsilon
      = 2 * gatingThreshold := by
  unfold criticalAmplification gatingThreshold
  field_simp
  ring

/-- Hoeffding concentration: N ≥ (1/2ε²) ln(2/δ).
 For δ = 1/2 (one-bit confidence): N ≥ ln2/ε² two-sided. -/
def hoeffdingMinimumN (epsilon : ℚ) : ℚ :=
  (693 / 1000 : ℚ) / (epsilon * epsilon)

/-- Margolus-Levitin firing rate: at most 2E/(πℏ) ops/sec.
 With π ≈ 314/100. -/
def margolusLevitinRate (energy hbar : ℚ) : ℚ :=
  2 * energy / ((314 / 100) * hbar)

/-- Landauer power budget firing rate: P/(k_B T ln2). -/
def landauerFiringRate (power boltzmann temperature logTwo : ℚ) : ℚ :=
  power / (boltzmann * temperature * logTwo)

/-- Theorem 53.8: B-event firing rate is the minimum of ML and Landauer. -/
def boundaryFiringRate
    (energy hbar power boltzmann temperature logTwo : ℚ) : ℚ :=
  min (margolusLevitinRate energy hbar)
      (landauerFiringRate power boltzmann temperature logTwo)

/-- Bekenstein-holographic upper bound: N ≤ A/(4ℓ_P² ln2). -/
def bekensteinUpperBound (area planckLengthSquared logTwo : ℚ) : ℚ :=
  area / (4 * planckLengthSquared * logTwo)

/-- Corollary 53.11: ultimate minimum ε.
 ε_min^phys ≥ ℓ_P ln2 / √(A/2).
 Squared: (ε_min^phys)² ≥ ℓ_P² (ln2)² / (A/2). -/
def ultimateMinSignalSquared
    (planckLengthSquared area logTwo : ℚ) : ℚ :=
  planckLengthSquared * logTwo * logTwo / (area / 2)

/-- Product-form classification of the five-row registry. -/
def gatingFrameworkHasProduct (k : GatingFrameworkKind) : Bool :=
  match k with
  | .uuetLandauer => true
  | .cramerRao => true
  | .heisenberg => true
  | .hoeffding => true
  | .margolusLevitin => false

/-- Exactly the four non-Margolus-Levitin rows have product form. -/
theorem gating_framework_has_product
    (k : GatingFrameworkKind) :
    gatingFrameworkHasProduct k = true ↔ k ≠ .margolusLevitin := by
  cases k <;> simp [gatingFrameworkHasProduct]

theorem margolusLevitin_is_rate_not_product :
    gatingFrameworkHasProduct .margolusLevitin = false := rfl

theorem product_framework_count :
    (gatingFrameworkRegistry.filter gatingFrameworkHasProduct).length = 4 := rfl

/-- Each framework row carries its named product form value. -/
def gatingProductValue (k : GatingFrameworkKind) : ℚ :=
  match k with
  | .uuetLandauer => 693 / 2000  -- ε²N = ln2/2
  | .cramerRao => 1 / 4           -- ε²N = 1/4
  | .heisenberg => 1 / 4           -- Δx²·N ~ ℏ²/4 (normalized)
  | .hoeffding => 693 / 2000       -- ε²N ≥ ln2/2
  | .margolusLevitin => 0          -- rate-bounded, not product form

/-- ε-N gating falsifier record. -/
structure EpsilonNGatingFalsifierRecord where
  violatesThresholdLaw : Bool
  violatesFiveHatUniversality : Bool
  violatesBekensteinUpperBound : Bool

/-- The Section 53 falsifier fires when any named failure channel fires. -/
def epsilonNGatingFalsified (r : EpsilonNGatingFalsifierRecord) : Bool :=
  r.violatesThresholdLaw
    || r.violatesFiveHatUniversality
    || r.violatesBekensteinUpperBound

theorem epsilonNGatingFalsified_eq_true
    (r : EpsilonNGatingFalsifierRecord) :
    epsilonNGatingFalsified r = true ↔
      r.violatesThresholdLaw = true
        ∨ r.violatesFiveHatUniversality = true
        ∨ r.violatesBekensteinUpperBound = true := by
  cases r
  simp only [epsilonNGatingFalsified, Bool.or_eq_true_iff]
  tauto

/-- Canonical witness: N_c(1/2) = ln2/(2·1/4) = 2ln2 ≈ 693/500 = 1.386.
 So N=2 is the first integer above threshold, matching ⌈1.386⌉ = 2. -/
theorem canonical_critical_amplification_witness :
    criticalAmplification (1 / 2) = 693 / 500 := by
  unfold criticalAmplification
  norm_num

/-- The actual ceiling at epsilon one half is two. -/
theorem canonical_critical_amplification_count_witness :
    criticalAmplificationCount (1 / 2) = 2 := by
  unfold criticalAmplificationCount
  rw [canonical_critical_amplification_witness]
  rw [Nat.ceil_eq_iff (by decide : (2 : Nat) ≠ 0)]
  norm_num

/-- Canonical Cramér-Rao witness: N_CR(1/2) = 1/(4·1/4) = 1. -/
theorem canonical_cramer_rao_witness :
    cramerRaoMinimumN (1 / 2) = 1 := by
  unfold cramerRaoMinimumN
  norm_num

/-- Canonical Hoeffding witness: N_H(1/2) = ln2/(1/4) = 4ln2 ≈ 2.772. -/
theorem canonical_hoeffding_witness :
    hoeffdingMinimumN (1 / 2) = 693 / 250 := by
  unfold hoeffdingMinimumN
  norm_num

/-- Canonical Margolus-Levitin witness: rate(1,1) = 2/(π) ≈ 200/314. -/
theorem canonical_margolus_levitin_witness :
    margolusLevitinRate 1 1 = 200 / 314 := by
  unfold margolusLevitinRate
  norm_num

/-- Canonical Bekenstein upper bound witness: A=4, ℓ_P²=1, ln2=693/1000
 gives N ≤ 4/(4·1·693/1000) = 1000/693. -/
theorem canonical_bekenstein_upper_witness :
    bekensteinUpperBound 4 1 (693 / 1000) = 1000 / 693 := by
  unfold bekensteinUpperBound
  norm_num

/-- Non-vacuity package for the finite Section 53 ε-N gating carrier. -/
theorem epsilonNGating_nonvacuous :
    gatingFrameworkRegistry.length = 5
      ∧ criticalAmplification (1 / 2) = 693 / 500
      ∧ criticalAmplificationCount (1 / 2) = 2
      ∧ cramerRaoMinimumN (1 / 2) = 1
      ∧ hoeffdingMinimumN (1 / 2) = 693 / 250
      ∧ margolusLevitinRate 1 1 = 200 / 314
      ∧ bekensteinUpperBound 4 1 (693 / 1000) = 1000 / 693
      ∧ isGated (1 / 2) 3
      ∧ ¬ isGated (1 / 2) 1 := by
  refine ⟨gatingFrameworkRegistry_length,
    canonical_critical_amplification_witness,
    canonical_critical_amplification_count_witness,
    canonical_cramer_rao_witness,
    canonical_hoeffding_witness,
    canonical_margolus_levitin_witness,
    canonical_bekenstein_upper_witness, ?_, ?_⟩
  · unfold isGated criticalAmplification; norm_num
  · have h : (1 : ℚ) < criticalAmplification (1 / 2) := by
      unfold criticalAmplification; norm_num
    exact below_threshold_not_gated (1 / 2) 1 h

#print axioms gatingFrameworkRegistry_length
#print axioms gating_framework_has_product
#print axioms criticalAmplification_le_count
#print axioms canonical_critical_amplification_count_witness
#print axioms margolusLevitin_is_rate_not_product
#print axioms product_framework_count
#print axioms below_threshold_not_gated
#print axioms at_or_above_threshold_gated
#print axioms epsilonNGatingFalsified_eq_true
#print axioms canonical_critical_amplification_witness
#print axioms canonical_cramer_rao_witness
#print axioms canonical_hoeffding_witness
#print axioms canonical_margolus_levitin_witness
#print axioms canonical_bekenstein_upper_witness
#print axioms criticalAmplification_eq_ratio_mul_cramerRao
#print axioms bitNatConversionRatio_eq_quotient
#print axioms gatingProduct_at_threshold
#print axioms epsilonNGating_nonvacuous

end OperatorKO7.Meta.UUET
