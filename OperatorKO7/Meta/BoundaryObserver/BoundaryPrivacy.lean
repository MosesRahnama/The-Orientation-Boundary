import OperatorKO7.Meta.BoundaryObserver.PairResolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-!
# Privacy at the observation boundary

Exact M6.14 obligations from BoundaryTheoremSpec.lean. The pointwise
likelihood-ratio bound controls triangular discrimination. The original
PairMenu cost theorem then controls every adaptive stopped protocol.
Proof status: source candidate until the supervisor's serial Lean checks.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy

open scoped BigOperators
open ProtocolResolution BoundarySingularity PairResolution

noncomputable section

/-- Exact M6.14 row assumption. -/
def IndistinguishableRows {Y : Type} (ε : ℝ) (P Q : Y → ℝ) : Prop :=
  ∀ y, P y ≤ Real.exp ε * Q y ∧ Q y ≤ Real.exp ε * P y

/-- Exact M6.14(i) obligation. -/
def PrivacyDiscriminationGoal : Prop :=
  ∀ (Y : Type) [Fintype Y] (P Q : FiniteLaw Y) (ε : ℝ), 0 ≤ ε →
    IndistinguishableRows ε P.mass Q.mass →
      discrimination P.mass Q.mass ≤ 2 * Real.tanh (ε / 2) ^ 2 ∧
        2 * Real.tanh (ε / 2) ^ 2 ≤ ε ^ 2 / 2

/-- Exact M6.14(ii) obligation. -/
def PrivacyCostGoal : Prop :=
  ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y) (ε c : ℝ), 0 < ε →
    (∀ h a, IndistinguishableRows ε (p.observation h a true).mass
      (p.observation h a false).mass) →
    (∀ h a, 1 ≤ p.cost h a) →
      ∀ n bank, HistoryBank n bank → c ≤ terminalMI p n bank →
        c * Real.log 2 / (2 * Real.tanh (ε / 2) ^ 2) ≤ expectedCost p n bank

/-- The zero-privacy ratio condition gives identical rows pointwise. -/
private theorem indistinguishable_zero_eq {Y : Type} (P Q : Y → ℝ)
    (h : IndistinguishableRows 0 P Q) : P = Q := by
  funext y
  obtain ⟨hl, hr⟩ := h y
  apply le_antisymm
  · simpa using hl
  · simpa using hr

/-- Ratio-bounded rows have a pointwise hyperbolic-tangent bound. -/
private theorem ratio_abs_le_tanh (a b ε : ℝ)
    (h : a ≤ Real.exp ε * b ∧ b ≤ Real.exp ε * a) :
    |a - b| ≤ Real.tanh (ε / 2) * (a + b) := by
  let x : ℝ := ε / 2
  have hshift : Real.exp ε * Real.exp (-x) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  have ha : a * Real.exp (-x) ≤ b * Real.exp x := by
    calc
      a * Real.exp (-x) ≤ (Real.exp ε * b) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h.1 (Real.exp_pos _).le
      _ = (Real.exp ε * Real.exp (-x)) * b := by ring
      _ = b * Real.exp x := by rw [hshift]; ring
  have hb : b * Real.exp (-x) ≤ a * Real.exp x := by
    calc
      b * Real.exp (-x) ≤ (Real.exp ε * a) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h.2 (Real.exp_pos _).le
      _ = (Real.exp ε * Real.exp (-x)) * a := by ring
      _ = a * Real.exp x := by rw [hshift]; ring
  rw [← Real.cosh_sub_sinh, ← Real.cosh_add_sinh] at ha hb
  have ha' : (a - b) * Real.cosh x ≤ (a + b) * Real.sinh x := by
    nlinarith [ha]
  have hb' : (b - a) * Real.cosh x ≤ (a + b) * Real.sinh x := by
    nlinarith [hb]
  have habs : |a - b| * Real.cosh x ≤ (a + b) * Real.sinh x := by
    rcases le_total b a with hba | hab
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      exact ha'
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      nlinarith [hb']
  have hdiv : |a - b| ≤ (a + b) * Real.sinh x / Real.cosh x :=
    (le_div_iff₀ (Real.cosh_pos x)).2 habs
  calc
    |a - b| ≤ (a + b) * Real.sinh x / Real.cosh x := hdiv
    _ = Real.tanh (ε / 2) * (a + b) := by
      change (a + b) * Real.sinh x / Real.cosh x = Real.tanh x * (a + b)
      rw [Real.tanh_eq_sinh_div_cosh]
      ring

/-- The actual local Mathlib derivative rules prove tanh x ≤ x, including x = 0. -/
private theorem tanh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.tanh x ≤ x := by
  have hd (u : ℝ) :
      HasDerivAt (fun v : ℝ => v * Real.cosh v - Real.sinh v)
        (u * Real.sinh u) u := by
    convert ((hasDerivAt_id' u).mul (Real.hasDerivAt_cosh u)).sub
      (Real.hasDerivAt_sinh u) using 1; ring
  have hp (u : ℝ) : 0 ≤ u * Real.sinh u := by
    by_cases hu : 0 ≤ u
    · exact mul_nonneg hu ((Real.sinh_nonneg_iff).2 hu)
    · have hu' : u ≤ 0 := le_of_lt (lt_of_not_ge hu)
      exact mul_nonneg_of_nonpos_of_nonpos hu' ((Real.sinh_nonpos_iff).2 hu')
  have hm : Monotone (fun v : ℝ => v * Real.cosh v - Real.sinh v) :=
    monotone_of_hasDerivAt_nonneg hd (fun u => hp u)
  have hnonneg : 0 ≤ x * Real.cosh x - Real.sinh x := by
    have h := hm hx
    simpa using h
  rw [Real.tanh_eq_sinh_div_cosh]
  exact (div_le_iff₀ (Real.cosh_pos x)).2 (by nlinarith [hnonneg])

/-- Each nonnegative row entry contributes at most its total mass times tanh squared. -/
private theorem discrimination_term_le_tanh (a b ε : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ Real.exp ε * b ∧ b ≤ Real.exp ε * a) :
    (a - b) ^ 2 / (a + b) ≤ (a + b) * Real.tanh (ε / 2) ^ 2 := by
  have hsum : 0 ≤ a + b := add_nonneg ha hb
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · have hpos : 0 < a + b := lt_of_le_of_ne hsum (Ne.symm hz)
    have habs := ratio_abs_le_tanh a b ε h
    have hsq : (a - b) ^ 2 ≤ (Real.tanh (ε / 2) * (a + b)) ^ 2 := by
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (a - b)) habs 2)
    calc
      (a - b) ^ 2 / (a + b) ≤
          (Real.tanh (ε / 2) * (a + b)) ^ 2 / (a + b) :=
        div_le_div_of_nonneg_right hsq hpos.le
      _ = (a + b) * Real.tanh (ε / 2) ^ 2 := by
        field_simp [ne_of_gt hpos]
        ring

/-- Exact M6.14(i), with no assumption of the target inequality. -/
theorem privacyDiscriminationGoal : PrivacyDiscriminationGoal := by
  intro Y _ P Q ε hε hrows
  by_cases hz : ε = 0
  · subst ε
    have heq : P.mass = Q.mass :=
      indistinguishable_zero_eq P.mass Q.mass hrows
    constructor
    · simp [heq, discrimination]
    · simp
  · constructor
    · unfold discrimination
      calc
        (∑ y, (P.mass y - Q.mass y) ^ 2 / (P.mass y + Q.mass y)) ≤
            ∑ y, (P.mass y + Q.mass y) * Real.tanh (ε / 2) ^ 2 :=
          Finset.sum_le_sum (fun y _ =>
            discrimination_term_le_tanh (P.mass y) (Q.mass y) ε
              (P.nonnegative y) (Q.nonnegative y) (hrows y))
        _ = 2 * Real.tanh (ε / 2) ^ 2 := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib, P.total, Q.total]
          ring
    · have hx : 0 ≤ ε / 2 := by linarith
      have ht : 0 ≤ Real.tanh (ε / 2) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg ((Real.sinh_nonneg_iff).2 hx) (Real.cosh_pos _).le
      have hle := tanh_le_self_of_nonneg hx
      have hsq : Real.tanh (ε / 2) ^ 2 ≤ (ε / 2) ^ 2 :=
        pow_le_pow_left₀ ht hle 2
      nlinarith [hsq]

/-- Exact M6.14(ii), applying the original adaptive pair-menu cost theorem. -/
theorem privacyCostGoal : PrivacyCostGoal := by
  intro A Y _ _ p ε c hε hrows hcost n bank hb hc
  let δ : ℝ := 2 * Real.tanh (ε / 2) ^ 2
  have hx : 0 < ε / 2 := by linarith
  have ht : 0 < Real.tanh (ε / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos ((Real.sinh_pos_iff).2 hx) (Real.cosh_pos _)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos ht 2)
  have menu : PairMenu p δ := {
    rows := by
      intro h a
      have hr := (privacyDiscriminationGoal Y
        (p.observation h a true) (p.observation h a false) ε hε.le (hrows h a)).1
      exact hr
    reading_cost := hcost
  }
  exact pairMenu_cost_lower_bound p δ c menu hδ n bank hb hc

end

end OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy
