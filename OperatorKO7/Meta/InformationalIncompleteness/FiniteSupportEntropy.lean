import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Shannon entropy below the finite Hartley envelope

For a nonempty finite alphabet and a nonnegative mass function summing to one,
Shannon entropy is at most the logarithm of the carrier cardinality.  The
uniform mass attains the bound.  This is the information-theoretic bridge used
by the distributional overproduction gap: a scheduler distribution on reachable
normal forms can never carry more Shannon uncertainty than the Hartley envelope
of the reachable terminal support.

Trust: kernel checked; no proof holes or user axioms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

noncomputable section

/-- Shannon entropy expressed in bits. -/
def HBits {α : Type} [Fintype α] (p : α → ℝ) : ℝ :=
  H p / Real.log 2

/-- Uniform mass on a nonempty finite carrier. -/
def uniformMass (α : Type) [Fintype α] : α → ℝ :=
  fun _ => 1 / (Fintype.card α : ℝ)

/-- The finite carrier cardinality is positive under `Nonempty`. -/
theorem card_cast_pos (α : Type) [Fintype α] [Nonempty α] :
    0 < (Fintype.card α : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- Uniform mass sums to one on a nonempty finite carrier. -/
theorem uniformMass_sum_one (α : Type) [Fintype α] [Nonempty α] :
    ∑ x : α, uniformMass α x = 1 := by
  simp [uniformMass, card_cast_pos α |>.ne']

/-- The entropy of the uniform distribution is the natural logarithm of the
carrier cardinality. -/
theorem H_uniformMass_eq_log_card (α : Type) [Fintype α] [Nonempty α] :
    H (uniformMass α) = Real.log (Fintype.card α : ℝ) := by
  unfold H uniformMass
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (Fintype.card α : ℝ) ≠ 0 := (card_cast_pos α).ne'
  have hlog : Real.log (1 / (Fintype.card α : ℝ)) =
      - Real.log (Fintype.card α : ℝ) := by
    rw [one_div, Real.log_inv]
  simp only [Real.negMulLog_def, hlog]
  field_simp

/-- The uniform distribution has base-two entropy equal to the base-two
logarithm of the carrier cardinality. -/
theorem HBits_uniformMass_eq_logb_card (α : Type) [Fintype α] [Nonempty α] :
    HBits (uniformMass α) = Real.logb 2 (Fintype.card α : ℝ) := by
  simp [HBits, H_uniformMass_eq_log_card, Real.logb]

/-- **Finite Shannon-Hartley envelope.** Any nonnegative probability mass on a
nonempty finite carrier has entropy at most `log(card α)`. -/
theorem H_le_log_card {α : Type} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    H p ≤ Real.log (Fintype.card α : ℝ) := by
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by
    dsimp [n]
    exact card_cast_pos α
  let w : α → ℝ := fun _ => 1 / n
  have hw0 : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ w i := by
    intro i hi
    exact le_of_lt (one_div_pos.mpr hn)
  have hw1 : ∑ i ∈ (Finset.univ : Finset α), w i = 1 := by
    simp [w, n, hn.ne']
  have hpMem : ∀ i ∈ (Finset.univ : Finset α), p i ∈ Set.Ici (0 : ℝ) := by
    intro i hi
    exact Set.mem_Ici.mpr (hp0 i)
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset α)) (w := w) (p := p)
    hw0 hw1 hpMem
  have havg : ∑ i : α, w i * p i = 1 / n := by
    simp only [w]
    rw [← Finset.mul_sum]
    rw [hsum, mul_one]
  have hscaled : (1 / n) * H p ≤ Real.negMulLog (1 / n) := by
    have hj' : (∑ i : α, w i * Real.negMulLog (p i)) ≤
        Real.negMulLog (∑ i : α, w i * p i) := by
      simpa [smul_eq_mul] using hj
    rw [havg] at hj'
    simpa [H, w, ← Finset.mul_sum] using hj'
  have hnnonneg : 0 ≤ n := le_of_lt hn
  have hmul := (mul_le_mul_of_nonneg_left hscaled hnnonneg)
  have hleft : n * ((1 / n) * H p) = H p := by
    field_simp
  have hright : n * Real.negMulLog (1 / n) = Real.log n := by
    change n * (-(1 / n) * Real.log (1 / n)) = Real.log n
    have hlog : Real.log (1 / n) = - Real.log n := by
      rw [one_div, Real.log_inv]
    rw [hlog]
    field_simp
  calc
    H p = n * ((1 / n) * H p) := hleft.symm
    _ ≤ n * Real.negMulLog (1 / n) := hmul
    _ = Real.log n := hright
    _ = Real.log (Fintype.card α : ℝ) := rfl

/-- Base-two form of the finite Shannon-Hartley envelope. -/
theorem HBits_le_logb_card {α : Type} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    HBits p ≤ Real.logb 2 (Fintype.card α : ℝ) := by
  unfold HBits Real.logb
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    (H_le_log_card p hp0 hsum)

/-- A point mass has zero Shannon entropy. -/
theorem H_dirac_eq_zero {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    H (fun x : α => if x = a then 1 else 0) = 0 := by
  unfold H
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h : x = a
  · simp [h, Real.negMulLog_one]
  · simp [h, Real.negMulLog_zero]

/-- Entropy is additive for independent product masses. -/
theorem H_product
    {α β : Type} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ)
    (hpSum : ∑ a, p a = 1) (hqSum : ∑ b, q b = 1) :
    H (fun z : α × β => p z.1 * q z.2) = H p + H q := by
  unfold H
  rw [Fintype.sum_prod_type]
  calc
    ∑ a, ∑ b, Real.negMulLog (p a * q b)
        = ∑ a, ∑ b, (q b * Real.negMulLog (p a) + p a * Real.negMulLog (q b)) := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            rw [Real.negMulLog_mul]
    _ = ∑ a, ((∑ b, q b) * Real.negMulLog (p a) + p a * (∑ b, Real.negMulLog (q b))) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.sum_mul]
          · rw [← Finset.mul_sum]
    _ = ∑ a, (Real.negMulLog (p a) + p a * (∑ b, Real.negMulLog (q b))) := by
          simp [hqSum]
    _ = (∑ a, Real.negMulLog (p a)) +
          (∑ a, p a) * (∑ b, Real.negMulLog (q b)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = (∑ a, Real.negMulLog (p a)) + (∑ b, Real.negMulLog (q b)) := by
          rw [hpSum, one_mul]

/-- Base-two entropy is additive for independent product masses. -/
theorem HBits_product
    {α β : Type} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ)
    (hpSum : ∑ a, p a = 1) (hqSum : ∑ b, q b = 1) :
    HBits (fun z : α × β => p z.1 * q z.2) = HBits p + HBits q := by
  unfold HBits
  rw [H_product p q hpSum hqSum]
  ring

end

end OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
