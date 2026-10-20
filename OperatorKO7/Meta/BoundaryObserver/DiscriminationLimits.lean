import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.DiscriminationLimits

open scoped BigOperators
open Filter Topology

/-- Total variation is one half of the sum of the absolute row differences. -/
noncomputable def tv {Y : Type} [Fintype Y] (P Q : Y → ℝ) : ℝ :=
  (1 / 2) * ∑ y, |P y - Q y|

/-- Triangular discrimination is at most twice the total variation of nonnegative rows. -/
theorem discrimination_le_two_tv {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) :
    BoundarySingularity.discrimination P Q ≤ 2 * tv P Q := by
  calc
    BoundarySingularity.discrimination P Q ≤ ∑ y, |P y - Q y| :=
      BoundarySingularity.discrimination_le_sum_abs P Q hP hQ
    _ = 2 * tv P Q := by unfold tv; ring

/-- The square of total variation is controlled below by normalized triangular discrimination. -/
theorem two_tv_sq_le_discrimination {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) :
    2 * tv P Q ^ 2 ≤ BoundarySingularity.discrimination P Q := by
  have hterm (y : Y) :
      |P y - Q y| ^ 2 =
        ((P y - Q y) ^ 2 / (P y + Q y)) * (P y + Q y) := by
    by_cases hs : P y + Q y = 0
    · have hp : P y = 0 := by linarith [hP y, hQ y]
      have hq : Q y = 0 := by linarith [hP y, hQ y]
      simp [hp, hq]
    · rw [sq_abs, div_mul_cancel₀]
      exact hs
  have hcs :
      (∑ y, |P y - Q y|) ^ 2 ≤
        (∑ y, (P y - Q y) ^ 2 / (P y + Q y)) * (∑ y, (P y + Q y)) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro y _
      exact BoundarySingularity.discrimination_term_nonneg _ _ (hP y) (hQ y)
    · intro y _
      exact add_nonneg (hP y) (hQ y)
    · intro y _
      exact hterm y
  have hrows : (∑ y, (P y + Q y)) = (2 : ℝ) := by
    rw [Finset.sum_add_distrib, hP1, hQ1]
    norm_num
  have htv : 2 * tv P Q = ∑ y, |P y - Q y| := by
    unfold tv
    ring
  rw [hrows] at hcs
  change (∑ y, |P y - Q y|) ^ 2 ≤
    BoundarySingularity.discrimination P Q * 2 at hcs
  rw [← htv] at hcs
  nlinarith

/-- A point mass assigns all probability to the distinguished output. -/
def pointMass {Y : Type} [DecidableEq Y] (y₀ : Y) : Y → ℝ :=
  fun y => if y = y₀ then 1 else 0

/-- Point masses have nonnegative mass at every output. -/
private theorem pointMass_nonneg {Y : Type} [DecidableEq Y] (y₀ y : Y) :
    0 ≤ pointMass y₀ y := by
  by_cases h : y = y₀ <;> simp [pointMass, h]

/-- Discrimination converges term by term even at the zero-denominator corner. -/
private theorem discrimination_term_tendsto (a b : ℕ → ℝ) (u v : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (halim : Filter.Tendsto a Filter.atTop (nhds u))
    (hblim : Filter.Tendsto b Filter.atTop (nhds v)) :
    Filter.Tendsto (fun n => (a n - b n) ^ 2 / (a n + b n))
      Filter.atTop (nhds ((u - v) ^ 2 / (u + v))) := by
  by_cases hden : u + v = 0
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    have habs : Filter.Tendsto (fun n => |a n - b n|)
        Filter.atTop (nhds 0) := by
      simpa [hu0, hv0] using (halim.sub hblim).abs
    have hzero := squeeze_zero
      (fun n => BoundarySingularity.discrimination_term_nonneg _ _ (ha n) (hb n))
      (fun n => BoundarySingularity.discrimination_term_le_abs _ _ (ha n) (hb n))
      habs
    simpa [hu0, hv0] using hzero
  · simpa using ((halim.sub hblim).pow 2).div (halim.add hblim) hden

/-- Two point masses have zero discrimination at one output and two at distinct outputs. -/
private theorem discrimination_pointMass {Y : Type} [Fintype Y] [DecidableEq Y]
    (y₀ y₁ : Y) :
    BoundarySingularity.discrimination (pointMass y₀) (pointMass y₁) =
      if y₀ = y₁ then 0 else 2 := by
  have hrow (z : Y) :
      pointMass z = (StochasticGraph.deterministic (id : Y → Y)).prob z := by
    funext y
    simp [pointMass, StochasticGraph.deterministic, eq_comm]
  rw [hrow y₀, hrow y₁]
  exact BoundarySingularity.discrimination_deterministic (id : Y → Y) y₀ y₁

/-- Pointwise convergence to two point masses determines the discrimination limit. -/
private theorem discrimination_tendsto_pointMass {Y : Type} [Fintype Y] [DecidableEq Y]
    (P Q : ℕ → Y → ℝ) (y₀ y₁ : Y)
    (hP : ∀ n y, 0 ≤ P n y) (hQ : ∀ n y, 0 ≤ Q n y)
    (hPl : ∀ y, Filter.Tendsto (fun n => P n y) Filter.atTop (nhds (pointMass y₀ y)))
    (hQl : ∀ y, Filter.Tendsto (fun n => Q n y) Filter.atTop (nhds (pointMass y₁ y))) :
    Filter.Tendsto (fun n => BoundarySingularity.discrimination (P n) (Q n))
      Filter.atTop (nhds (if y₀ = y₁ then 0 else 2)) := by
  have hsum : Filter.Tendsto
      (fun n => ∑ y, (P n y - Q n y) ^ 2 / (P n y + Q n y))
      Filter.atTop
      (nhds (∑ y, (pointMass y₀ y - pointMass y₁ y) ^ 2 /
        (pointMass y₀ y + pointMass y₁ y))) := by
    refine tendsto_finset_sum Finset.univ (fun y _ => ?_)
    exact discrimination_term_tendsto
      (fun n => P n y) (fun n => Q n y)
      (pointMass y₀ y) (pointMass y₁ y)
      (fun n => hP n y) (fun n => hQ n y)
      (pointMass_nonneg y₀ y) (pointMass_nonneg y₁ y)
      (hPl y) (hQl y)
  rw [← discrimination_pointMass y₀ y₁]
  change Filter.Tendsto
    (fun n => ∑ y, (P n y - Q n y) ^ 2 / (P n y + Q n y))
    Filter.atTop
    (nhds (∑ y, (pointMass y₀ y - pointMass y₁ y) ^ 2 /
      (pointMass y₀ y + pointMass y₁ y)))
  exact hsum

/-- Rows approaching the same deterministic point mass have discrimination tending to zero. -/
theorem discrimination_tendsto_merged {Y : Type} [Fintype Y] [DecidableEq Y]
    (P Q : ℕ → Y → ℝ) (y₀ : Y) (hP : ∀ n y, 0 ≤ P n y)
    (hQ : ∀ n y, 0 ≤ Q n y)
    (hPl : ∀ y, Filter.Tendsto (fun n => P n y) Filter.atTop (nhds (pointMass y₀ y)))
    (hQl : ∀ y, Filter.Tendsto (fun n => Q n y) Filter.atTop (nhds (pointMass y₀ y))) :
    Filter.Tendsto (fun n => BoundarySingularity.discrimination (P n) (Q n))
      Filter.atTop (nhds 0) := by
  simpa using discrimination_tendsto_pointMass P Q y₀ y₀ hP hQ hPl hQl

/-- Rows approaching distinct deterministic point masses have discrimination tending to two. -/
theorem discrimination_tendsto_split {Y : Type} [Fintype Y] [DecidableEq Y]
    (P Q : ℕ → Y → ℝ) (y₀ y₁ : Y) (hne : y₀ ≠ y₁)
    (hP : ∀ n y, 0 ≤ P n y) (hQ : ∀ n y, 0 ≤ Q n y)
    (hPl : ∀ y, Filter.Tendsto (fun n => P n y) Filter.atTop (nhds (pointMass y₀ y)))
    (hQl : ∀ y, Filter.Tendsto (fun n => Q n y) Filter.atTop (nhds (pointMass y₁ y))) :
    Filter.Tendsto (fun n => BoundarySingularity.discrimination (P n) (Q n))
      Filter.atTop (nhds 2) := by
  simpa [hne] using discrimination_tendsto_pointMass P Q y₀ y₁ hP hQ hPl hQl

/-- Readings converging pointwise to deterministic rows have discrimination zero or two. -/
theorem reading_discrimination_tendsto {X Y : Type} [Fintype Y] [DecidableEq Y]
    (q : X → Y) (K : ℕ → BoundaryPole.Reading X Y) (x x' : X)
    (hx : ∀ y, Filter.Tendsto (fun n => (K n x).mass y) Filter.atTop
      (nhds (pointMass (q x) y)))
    (hx' : ∀ y, Filter.Tendsto (fun n => (K n x').mass y) Filter.atTop
      (nhds (pointMass (q x') y))) :
    Filter.Tendsto (fun n => BoundaryPole.readingDiscrimination (K n) x x')
      Filter.atTop (nhds (if q x = q x' then 0 else 2)) := by
  have hP : ∀ n y, 0 ≤ (K n x).mass y :=
    fun n y => (K n x).nonnegative y
  have hQ : ∀ n y, 0 ≤ (K n x').mass y :=
    fun n y => (K n x').nonnegative y
  by_cases h : q x = q x'
  · have hx'' : ∀ y, Filter.Tendsto (fun n => (K n x').mass y)
        Filter.atTop (nhds (pointMass (q x) y)) := by
      intro y
      simpa [h] using hx' y
    have hmerge := discrimination_tendsto_merged
      (fun n => (K n x).mass) (fun n => (K n x').mass)
      (q x) hP hQ hx hx''
    simpa [BoundaryPole.readingDiscrimination, h] using hmerge
  · have hsplit := discrimination_tendsto_split
      (fun n => (K n x).mass) (fun n => (K n x').mass)
      (q x) (q x') h hP hQ hx hx'
    simpa [BoundaryPole.readingDiscrimination, h] using hsplit

/-- Positive discrimination tending to zero makes a positive information cost diverge. -/
theorem cost_lower_bound_tendsto_atTop (Δ : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hpos : ∀ n, 0 < Δ n)
    (hlim : Filter.Tendsto Δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => c * Real.log 2 / Δ n)
      Filter.atTop Filter.atTop := by
  have hwithin : Filter.Tendsto Δ Filter.atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within Δ hlim
      (Filter.Eventually.of_forall hpos)
  have hpositive : 0 < c * Real.log 2 :=
    mul_pos hc (Real.log_pos (by norm_num))
  have hinv : Filter.Tendsto (fun n => (Δ n)⁻¹)
      Filter.atTop Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp hwithin
  simpa [div_eq_mul_inv, mul_comm] using hinv.atTop_mul_const hpositive

/-- The boundary pole has zero limiting discrimination and divergent positive cost at
merged pairs, while split pairs have limiting discrimination two. -/
theorem boundary_singularity_limits {X Y : Type} [Fintype Y] [DecidableEq Y]
    (q : X → Y) (K : ℕ → BoundaryPole.Reading X Y) (x x' : X)
    (hx : ∀ y, Filter.Tendsto (fun n => (K n x).mass y) Filter.atTop
      (nhds (pointMass (q x) y)))
    (hx' : ∀ y, Filter.Tendsto (fun n => (K n x').mass y) Filter.atTop
      (nhds (pointMass (q x') y))) :
    (q x = q x' →
      Filter.Tendsto (fun n => BoundaryPole.readingDiscrimination (K n) x x')
        Filter.atTop (nhds 0) ∧
      ∀ (c : ℝ), 0 < c →
        (∀ n, 0 < BoundaryPole.readingDiscrimination (K n) x x') →
        Filter.Tendsto
          (fun n => c * Real.log 2 / BoundaryPole.readingDiscrimination (K n) x x')
          Filter.atTop Filter.atTop) ∧
    (q x ≠ q x' →
      Filter.Tendsto (fun n => BoundaryPole.readingDiscrimination (K n) x x')
        Filter.atTop (nhds 2)) := by
  have hdisc := reading_discrimination_tendsto q K x x' hx hx'
  constructor
  · intro heq
    have hzero : Filter.Tendsto
        (fun n => BoundaryPole.readingDiscrimination (K n) x x')
        Filter.atTop (nhds 0) := by
      simpa [heq] using hdisc
    exact ⟨hzero, fun c hc hpos =>
      cost_lower_bound_tendsto_atTop
        (fun n => BoundaryPole.readingDiscrimination (K n) x x') c hc hpos hzero⟩
  · intro hne
    simpa [hne] using hdisc


/-! Audit A4: the inverse information price as an extended nonnegative value. -/

open scoped ENNReal

/-- The lower information price in extended nonnegative reals. A positive
information target has infinite price at zero discrimination. -/
noncomputable def extendedInformationPrice (c δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c * Real.log 2) / ENNReal.ofReal δ

/-- At positive discrimination the extended price agrees with the real formula. -/
theorem extendedInformationPrice_eq_of_pos (c δ : ℝ) (hδ : 0 < δ) :
    extendedInformationPrice c δ = ENNReal.ofReal (c * Real.log 2 / δ) := by
  exact (ENNReal.ofReal_div_of_pos hδ).symm

/-- Acquiring zero information has zero lower price, including at the boundary. -/
theorem extendedInformationPrice_zero_target (δ : ℝ) :
    extendedInformationPrice 0 δ = 0 := by
  simp [extendedInformationPrice]

/-- A positive target has infinite lower price at zero discrimination. -/
theorem extendedInformationPrice_zero (c : ℝ) (hc : 0 < c) :
    extendedInformationPrice c 0 = ⊤ := by
  apply ENNReal.div_eq_top.mpr
  exact Or.inl ⟨(ENNReal.ofReal_pos.mpr
    (mul_pos hc (Real.log_pos one_lt_two))).ne', ENNReal.ofReal_zero⟩

/-- For a positive target and nonnegative discrimination, the boundary is
exactly the infinite-price set. -/
theorem extendedInformationPrice_eq_top_iff (c δ : ℝ) (hc : 0 < c)
    (hδ : 0 ≤ δ) : extendedInformationPrice c δ = ⊤ ↔ δ = 0 := by
  constructor
  · intro h
    rcases ENNReal.div_eq_top.mp h with hzero | hinf
    · exact le_antisymm (ENNReal.ofReal_eq_zero.mp hzero.2) hδ
    · exact (ENNReal.ofReal_ne_top hinf.1).elim
  · intro h
    rw [h]
    exact extendedInformationPrice_zero c hc

/-- A finite price is equivalent to positive discrimination for a positive target. -/
theorem extendedInformationPrice_ne_top_iff (c δ : ℝ) (hc : 0 < c)
    (hδ : 0 ≤ δ) : extendedInformationPrice c δ ≠ ⊤ ↔ 0 < δ := by
  rw [ne_eq, extendedInformationPrice_eq_top_iff c δ hc hδ]
  exact ⟨fun h => lt_of_le_of_ne hδ (Ne.symm h), fun h => h.ne'⟩

/-- The extended inverse price tends to infinity whenever discrimination tends
to zero. Terms equal to zero are permitted; no punctured-domain premise is used. -/
theorem extendedInformationPrice_tendsto_top (δ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hlim : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => extendedInformationPrice c (δ n))
      Filter.atTop (nhds (⊤ : ℝ≥0∞)) := by
  have hδ : Filter.Tendsto (fun n => ENNReal.ofReal (δ n))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlim
  have hnum : ENNReal.ofReal (c * Real.log 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (mul_pos hc (Real.log_pos one_lt_two))).ne'
  have htop : ENNReal.ofReal (c * Real.log 2) / (0 : ℝ≥0∞) = ⊤ :=
    ENNReal.div_eq_top.mpr (Or.inl ⟨hnum, rfl⟩)
  have h := ENNReal.Tendsto.const_div (a := ENNReal.ofReal (c * Real.log 2))
    hδ (Or.inl ENNReal.zero_ne_top)
  simpa only [extendedInformationPrice, htop] using h

/-- Converting the infinite endpoint to a real number discards infinity. -/
theorem extendedInformationPrice_boundary_toReal (c : ℝ) (hc : 0 < c) :
    extendedInformationPrice c 0 = ⊤ ∧
      (extendedInformationPrice c 0).toReal = 0 := by
  rw [extendedInformationPrice_zero c hc]
  exact ⟨rfl, ENNReal.toReal_top⟩

/-- Every finite stopped pair-menu protocol acquiring a positive target pays
at least the extended price. At zero discrimination acquisition is impossible. -/
theorem pairMenu_extendedPrice_lower_bound {A Y : Type} [Fintype A] [Fintype Y]
    (p : ProtocolResolution.FiniteProtocol Bool A Y) (δ c : ℝ)
    (menu : BoundarySingularity.PairMenu p δ) (hδ : 0 ≤ δ) (hc : 0 < c)
    (n : ℕ) (bank : List (List (A × Y))) (hb : ProtocolResolution.HistoryBank n bank)
    (htarget : c ≤ ProtocolResolution.terminalMI p n bank) :
    extendedInformationPrice c δ ≤
      ENNReal.ofReal (ProtocolResolution.expectedCost p n bank) := by
  rcases hδ.eq_or_lt with hzero | hpos
  · subst δ
    have hz := BoundarySingularity.pairMenu_zero_discrimination p menu n bank hb
    exact (not_le_of_gt hc (by simpa only [hz] using htarget)).elim
  · rw [extendedInformationPrice_eq_of_pos c δ hpos]
    exact ENNReal.ofReal_le_ofReal
      (BoundarySingularity.pairMenu_cost_lower_bound p δ c menu hpos n bank hb htarget)

/-- The same extended price bounds actual unbounded expected cost when the
limiting information reaches the target. Infinite-cost protocols are included. -/
theorem pairMenu_extendedPrice_limit_lower_bound {A Y : Type} [Fintype A] [Fintype Y]
    (p : ProtocolResolution.FiniteProtocol Bool A Y) (δ c : ℝ)
    (menu : BoundarySingularity.PairMenu p δ) (hδ : 0 ≤ δ) (hc : 0 < c)
    (htarget : c ≤ ProtocolResolution.informationLimit p) :
    extendedInformationPrice c δ ≤ ProtocolResolution.extendedCost p := by
  rcases hδ.eq_or_lt with hzero | hpos
  · subst δ
    have hz := BoundarySingularity.pairMenu_limit_zero p menu
    exact (not_le_of_gt hc (by simpa only [hz] using htarget)).elim
  · by_cases hinf : ProtocolResolution.extendedCost p = ⊤
    · rw [hinf]
      exact le_top
    · have hfinite : ENNReal.ofReal (ProtocolResolution.extendedCost p).toReal =
          ProtocolResolution.extendedCost p := ENNReal.ofReal_toReal hinf
      have hlower := BoundarySingularity.pairMenu_limit_cost_lower p δ c
        (ProtocolResolution.extendedCost p).toReal menu hpos ENNReal.toReal_nonneg
        htarget (le_of_eq hfinite.symm)
      rw [extendedInformationPrice_eq_of_pos c δ hpos, ← hfinite]
      exact ENNReal.ofReal_le_ofReal hlower

/-! ## Audit node A10: discrimination two at disjoint supports

For two laws the discrimination is two minus the overlap term `∑ 4 P(y) Q(y) / (P(y) + Q(y))`, so it is
two if and only if no output has positive chance under both rows, which is the condition for one
reading to decode the binary label with zero error. Rows with two positive entries attain it. -/

/-- For two laws, the discrimination is two minus the overlap term. -/
theorem discrimination_eq_two_sub_overlap {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y) (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) :
    BoundarySingularity.discrimination P Q = 2 - ∑ y, 4 * (P y * Q y) / (P y + Q y) := by
  have hterm : ∀ y, (P y - Q y) ^ 2 / (P y + Q y) =
      (P y + Q y) - 4 * (P y * Q y) / (P y + Q y) := by
    intro y
    rcases (add_nonneg (hP0 y) (hQ0 y)).eq_or_lt with h0 | hpos
    · have hp : P y = 0 := by linarith [hP0 y, hQ0 y]
      have hq : Q y = 0 := by linarith [hP0 y, hQ0 y]
      simp [hp, hq]
    · have hne : P y + Q y ≠ 0 := hpos.ne'
      field_simp
      ring
  unfold BoundarySingularity.discrimination
  rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hP1, hQ1]
  norm_num

/-- For two laws, the discrimination is two if and only if no output has positive chance under both. -/
theorem discrimination_eq_two_iff_disjoint {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y) (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) :
    BoundarySingularity.discrimination P Q = 2 ↔ ∀ y, P y = 0 ∨ Q y = 0 := by
  rw [discrimination_eq_two_sub_overlap P Q hP0 hQ0 hP1 hQ1]
  have hnn : ∀ y, 0 ≤ 4 * (P y * Q y) / (P y + Q y) := by
    intro y
    have h1 := hP0 y
    have h2 := hQ0 y
    positivity
  constructor
  · intro h
    have hsum : ∑ y, 4 * (P y * Q y) / (P y + Q y) = 0 := by linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn y)).mp hsum
    intro y
    have hy := hz y (Finset.mem_univ y)
    rcases (add_nonneg (hP0 y) (hQ0 y)).eq_or_lt with h0 | hpos
    · left
      linarith [hP0 y, hQ0 y]
    · have hprod : P y * Q y = 0 := by
        rcases div_eq_zero_iff.mp hy with h4 | h4
        · linarith
        · linarith
      exact mul_eq_zero.mp hprod
  · intro h
    have hsum : ∑ y, 4 * (P y * Q y) / (P y + Q y) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      rcases h y with h' | h' <;> simp [h']
    linarith

/-- For two laws, one reading decodes the binary label with zero error if and only if the
discrimination is two. -/
theorem exists_zero_error_decoder_iff_discrimination_eq_two {Y : Type} [Fintype Y]
    (P Q : Y → ℝ) (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y) (hP1 : ∑ y, P y = 1)
    (hQ1 : ∑ y, Q y = 1) :
    (∃ d : Y → Bool, (∀ y, 0 < P y → d y = true) ∧ (∀ y, 0 < Q y → d y = false)) ↔
      BoundarySingularity.discrimination P Q = 2 := by
  rw [discrimination_eq_two_iff_disjoint P Q hP0 hQ0 hP1 hQ1]
  constructor
  · rintro ⟨d, hd1, hd0⟩ y
    by_contra hne
    push_neg at hne
    have hp : 0 < P y := lt_of_le_of_ne (hP0 y) (Ne.symm hne.1)
    have hq : 0 < Q y := lt_of_le_of_ne (hQ0 y) (Ne.symm hne.2)
    have h1 := hd1 y hp
    have h2 := hd0 y hq
    rw [h1] at h2
    simp at h2
  · intro h
    refine ⟨fun y => decide (0 < P y), fun y hy => by simp [hy], fun y hy => ?_⟩
    rcases h y with h' | h'
    · simp [h']
    · exact absurd h' hy.ne'

/-- Two rows with two positive entries each and disjoint supports have discrimination two. -/
theorem discrimination_two_positive_entries :
    BoundarySingularity.discrimination (fun i : Fin 4 => if i.val < 2 then (1 : ℝ) / 2 else 0)
      (fun i : Fin 4 => if i.val < 2 then 0 else (1 : ℝ) / 2) = 2 := by
  norm_num [BoundarySingularity.discrimination, Fin.sum_univ_four]

end OperatorKO7.Meta.BoundaryObserver.DiscriminationLimits

