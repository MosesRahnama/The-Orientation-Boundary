import OperatorKO7.Meta.BoundaryObserver.FisherDiscrimination
import OperatorKO7.Meta.BoundaryObserver.PairResolution

set_option autoImplicit false

/-!
# The Fisher remark of the Boundary-Observation Principle

The sentences of Remark `rem:fisher` that no earlier declaration states: the discrimination as the
`f`-divergence of `f(u) = (u - 1)² / (u + 1)` with `f''(1) = 1`; the closed form `2t² / (2 - t²)`
of the boundary law and the failure of the bound `o(t²)` there; the two forms of the reciprocal
cost bound; the cost beyond every multiple of `δθ⁻²` at zero Fisher information; the repetition of
the two rows within the inverse-square cost; and the quadratic term of an arbitrary twice
differentiable `f`-divergence as `f''(1) / 2` times the Fisher form.

Relation: none beyond the discrimination, the Fisher information and the protocols of the imported
modules.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleFisher

open Filter Asymptotics Topology
open OperatorKO7.Meta.BoundaryObserver.FisherDiscrimination
open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

/-! ## The `f`-divergence form -/

/-- The generator `f(u) = (u - 1)² / (u + 1)` of the discrimination. -/
noncomputable def discriminationGenerator (u : ℝ) : ℝ := (u - 1) ^ 2 / (u + 1)

/-- The discrimination is the `f`-divergence of `discriminationGenerator`: for a positive second
row, each term `(P - Q)² / (P + Q)` is `Q f(P / Q)`. -/
theorem discrimination_eq_fDivergence {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hQ : ∀ y, 0 < Q y) :
    discrimination P Q = ∑ y, Q y * discriminationGenerator (P y / Q y) := by
  unfold discrimination discriminationGenerator
  apply Finset.sum_congr rfl
  intro y _
  have hq : Q y ≠ 0 := (hQ y).ne'
  by_cases hs : P y + Q y = 0
  · have hpq : P y / Q y + 1 = 0 := by
      rw [div_add_one hq, hs, zero_div]
    rw [hs, hpq, div_zero, div_zero, mul_zero]
  · have hpq : P y / Q y + 1 ≠ 0 := by
      rw [div_add_one hq]
      exact div_ne_zero hs hq
    field_simp
    ring

/-- The derivative of the generator off `u = -1`. -/
theorem hasDerivAt_discriminationGenerator (u : ℝ) (hu : u + 1 ≠ 0) :
    HasDerivAt discriminationGenerator ((u - 1) * (u + 3) / (u + 1) ^ 2) u := by
  have hc : HasDerivAt (fun v : ℝ => (v - 1) ^ 2) (2 * (u - 1)) u := by
    simpa using ((hasDerivAt_id u).sub_const 1).pow 2
  have hd : HasDerivAt (fun v : ℝ => v + 1) 1 u := (hasDerivAt_id u).add_const 1
  have h := hc.div hd hu
  convert h using 1
  field_simp
  ring

/-- The generator vanishes at one and its second derivative there is one. -/
theorem discriminationGenerator_second_derivative :
    discriminationGenerator 1 = 0 ∧ deriv (deriv discriminationGenerator) 1 = 1 := by
  refine ⟨by norm_num [discriminationGenerator], ?_⟩
  have heq : deriv discriminationGenerator =ᶠ[𝓝 1]
      (fun u : ℝ => (u - 1) * (u + 3) / (u + 1) ^ 2) := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num)] with u hu
    exact (hasDerivAt_discriminationGenerator u (by
      have : (-1 : ℝ) < u := hu
      linarith)).deriv
  rw [heq.deriv_eq]
  have hc : HasDerivAt (fun v : ℝ => (v - 1) * (v + 3)) ((1 + 3) + (1 - 1)) 1 := by
    have := ((hasDerivAt_id (1 : ℝ)).sub_const 1).mul ((hasDerivAt_id (1 : ℝ)).add_const 3)
    simpa using this
  have hd : HasDerivAt (fun v : ℝ => (v + 1) ^ 2) (2 * (1 + 1)) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).add_const 1).pow 2
  have h : HasDerivAt (fun u : ℝ => (u - 1) * (u + 3) / (u + 1) ^ 2)
      (((1 + 3 + (1 - 1)) * (1 + 1) ^ 2 - (1 - 1) * (1 + 3) * (2 * (1 + 1))) / ((1 + 1) ^ 2) ^ 2)
      1 := hc.div hd (by norm_num)
  rw [h.deriv]
  norm_num

/-! ## Part (b): the support boundary -/

/-- The boundary law has discrimination `2t² / (2 - t²)` from `Q₀ = (1, 0)` for `t² ≤ 1`. -/
theorem quadraticLaw_discrimination_closed (t : ℝ) (ht : t ^ 2 ≤ 1) :
    discrimination (quadraticLaw 0) (quadraticLaw t) = 2 * t ^ 2 / (2 - t ^ 2) := by
  have h2 : (2 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  unfold discrimination
  rw [Fintype.sum_bool]
  have e1 : (quadraticLaw 0 true - quadraticLaw t true) ^ 2 /
      (quadraticLaw 0 true + quadraticLaw t true) = t ^ 2 := by
    simp only [quadraticLaw, if_true]
    have h : ((0 : ℝ) ^ 2 - t ^ 2) ^ 2 / ((0 : ℝ) ^ 2 + t ^ 2) = (t ^ 2) ^ 2 / t ^ 2 := by ring
    rw [h]
    by_cases h0 : t ^ 2 = 0
    · rw [h0]
      norm_num
    · field_simp
      ring
  have e2 : (quadraticLaw 0 false - quadraticLaw t false) ^ 2 /
      (quadraticLaw 0 false + quadraticLaw t false) = t ^ 4 / (2 - t ^ 2) := by
    simp only [quadraticLaw, Bool.false_eq_true, if_false]
    ring
  rw [e1, e2]
  field_simp
  ring

/-- At the support boundary the discrimination is not `o(t²)`, although the Fisher information of
the boundary law vanishes at `t = 0`. -/
theorem quadraticLaw_not_littleO :
    ¬ (fun t : ℝ => discrimination (quadraticLaw 0) (quadraticLaw t)) =o[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  intro h
  have hb := h.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 ≤ 1 := by
    have : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ))
    exact this (Iic_mem_nhds (by norm_num))
  have hzero : ∀ᶠ t : ℝ in 𝓝 0, t = 0 := by
    filter_upwards [hb, hsmall] with t hbt hst
    have hlow := quadraticLaw_boundary_lower t hst
    have hΔ0 : 0 ≤ discrimination (quadraticLaw 0) (quadraticLaw t) :=
      le_trans (by positivity) hlow
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΔ0,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2)] at hbt
    have : t ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (by positivity))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hzero
  have := hball (y := ε / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith)
  linarith

/-! ## Part (c): the two forms of the reciprocal bound -/

/-- At positive Fisher information the reciprocal bound reads `2c log 2 / (I δθ²)` times
`(1 + 2ζ / I)⁻¹`; at zero Fisher information it reads `c log 2 / (ζ δθ²)`. -/
theorem fisher_cost_value_forms (c I ζ δθ : ℝ) (hζ : 0 < ζ) (hδ : δθ ≠ 0) :
    (0 < I → c * Real.log 2 / ((I / 2 + ζ) * δθ ^ 2) =
        2 * c * Real.log 2 / (I * δθ ^ 2) * (1 + 2 * ζ / I)⁻¹) ∧
      (I = 0 → c * Real.log 2 / ((I / 2 + ζ) * δθ ^ 2) = c * Real.log 2 / (ζ * δθ ^ 2)) := by
  refine ⟨fun hI => ?_, fun hI => by rw [hI]; ring_nf⟩
  have hI' : I ≠ 0 := hI.ne'
  have hδ2 : δθ ^ 2 ≠ 0 := pow_ne_zero 2 hδ
  have h1 : 1 + 2 * ζ / I ≠ 0 := by positivity
  have h2 : I / 2 + ζ ≠ 0 := by positivity
  field_simp
  ring

/-- At zero Fisher information the cost of `c > 0` bits exceeds every multiple `M / δθ²`: for
every `M > 0`, at every parameter near enough to `θ`, every protocol whose readings have rows of
discrimination at most `Δ(P_θ, P_t)` and cost at least one pays at least `M / (t - θ)²`. -/
theorem zero_fisher_cost_exceeds_every_multiple {H0 A Y : Type} [Fintype H0] [Fintype A]
    [Fintype Y] (P : ℝ → Y → ℝ) (θ : ℝ) (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) (hI : fisherInformation P θ = 0) (c M : ℝ) (hc : 0 < c)
    (hM : 0 < M) :
    ∀ᶠ t in 𝓝 θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : ConditionalPairMenu p (discrimination (P θ) (P t)))
      (n : ℕ) (bank : List (List (A × Y))),
      ProtocolResolution.HistoryBank n bank →
      c ≤ ProtocolResolution.conditionalJointInfo p n bank → t ≠ θ →
        M / (t - θ) ^ 2 ≤ ProtocolResolution.conditionalExpectedCost p n bank := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hζ : 0 < c * Real.log 2 / M := by positivity
  filter_upwards [fisher_local_conditional_cost_reciprocal_at (H0 := H0) (A := A) P θ
      (c * Real.log 2 / M) hP hpos hζ] with t ht p menu n bank hb hcinfo htn
  have h := ht p menu n bank hb c hcinfo htn
  rw [hI, zero_div, zero_add] at h
  have hδ : (t - θ) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 htn)
  have he : c * Real.log 2 / (c * Real.log 2 / M * (t - θ) ^ 2) = M / (t - θ) ^ 2 := by
    field_simp
    ring
  rwa [he] at h

/-! ## The repetition of the two rows within the inverse-square cost -/

open PairResolution ProtocolResolution

/-- The law `P t` of a family of laws, as a finite law. -/
noncomputable def lawAt {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ)
    (hlaw : ∀ t, (∀ y, 0 ≤ P t y) ∧ ∑ y, P t y = 1) (t : ℝ) : FiniteLaw Y where
  mass := P t
  nonnegative := (hlaw t).1
  total := (hlaw t).2

/-- For a family of laws with positive support and `0 < ζ < I(θ)/2`, at every parameter `t ≠ θ`
near enough to `θ` the repeated reading of the two rows `P_θ, P_t` acquires `1 - h(η)` bits of a
fair label within `4 log(1/(2η)) / ((I(θ)/2 - ζ) (t - θ)²) + 1` readings. -/
theorem fisher_repetition_attains {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ ζ : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ) (hpos : ∀ y, 0 < P θ y)
    (hlaw : ∀ t, (∀ y, 0 ≤ P t y) ∧ ∑ y, P t y = 1) (hζ : 0 < ζ)
    (hζI : ζ < fisherInformation P θ / 2) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∀ᶠ t in 𝓝 θ, t ≠ θ → ∃ N : ℕ,
      1 - Real.binEntropy η / Real.log 2 ≤
          terminalMI (repeatProtocol (lawAt P hlaw θ) (lawAt P hlaw t) N) N
            (historyBank Unit Y N) ∧
        expectedCost (repeatProtocol (lawAt P hlaw θ) (lawAt P hlaw t) N) N
            (historyBank Unit Y N) = N ∧
        (N : ℝ) ≤ 4 * Real.log (1 / (2 * η)) / ((fisherInformation P θ / 2 - ζ) * (t - θ) ^ 2)
          + 1 := by
  filter_upwards [discrimination_local_quadratic_band_at P θ ζ hP hpos hζ] with t ht htn
  have hcoef : 0 < fisherInformation P θ / 2 - ζ := by linarith
  have hδ : 0 < (t - θ) ^ 2 := by
    have : t - θ ≠ 0 := sub_ne_zero.2 htn
    positivity
  have hlow : 0 < (fisherInformation P θ / 2 - ζ) * (t - θ) ^ 2 := mul_pos hcoef hδ
  have hΔ : 0 < discrimination (lawAt P hlaw θ).mass (lawAt P hlaw t).mass :=
    lt_of_lt_of_le hlow ht.1
  obtain ⟨N, h1, h2, h3⟩ := (pair_resolution_two_sided _ _ hΔ).2 η hη0 hη1
  refine ⟨N, h1, h2, h3.trans ?_⟩
  have hlogη : 0 ≤ Real.log (1 / (2 * η)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    linarith
  have := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hlogη) hlow ht.1
  have hmass : discrimination (lawAt P hlaw θ).mass (lawAt P hlaw t).mass =
      discrimination (P θ) (P t) := rfl
  rw [hmass]
  linarith

/-! ## The quadratic term of a twice differentiable `f`-divergence -/

/-- At positive support, for a family of laws with coordinates differentiable at `θ` and a
generator `f` with `f 1 = 0` twice differentiable at `1`, the `f`-divergence
`∑_y P_θ(y) f(P_t(y) / P_θ(y))` is `f''(1) / 2` times the Fisher form `I(θ)(t - θ)²` up to
`o((t - θ)²)`: the quadratic term of the `f`-divergence is proportional to the Fisher form. -/
theorem fDivergence_quadratic_fisher {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ) (hpos : ∀ y, 0 < P θ y)
    (hsum : ∀ t, ∑ y, P t y = 1) (f : ℝ → ℝ) (hf1 : f 1 = 0) (hf : TwiceDifferentiableAt f 1) :
    (fun t => ∑ y, P θ y * f (P t y / P θ y) -
        (1 / 2 : ℝ) * deriv (deriv f) 1 * fisherInformation P θ * (t - θ) ^ 2) =o[𝓝 θ]
      (fun t => (t - θ) ^ 2) := by
  set f1 := deriv f 1
  set f2 := deriv (deriv f) 1
  let g : ℝ → ℝ := fun u => f u - f 1 - f1 * (u - 1) - (1 / 2 : ℝ) * f2 * (u - 1) ^ 2
  have hg : g =o[𝓝 1] (fun u => (u - 1) ^ 2) := taylor_two_littleO_at f 1 hf
  -- the identity of the target with the sum of the remainders
  have hident : ∀ t, ∑ y, P θ y * f (P t y / P θ y) -
      (1 / 2 : ℝ) * f2 * fisherInformation P θ * (t - θ) ^ 2 =
      ∑ y, (P θ y * g (P t y / P θ y) + (1 / 2 : ℝ) * f2 / P θ y *
        ((P t y - P θ y) ^ 2 - (deriv (fun s => P s y) θ * (t - θ)) ^ 2)) := by
    intro t
    have hfirst : ∑ y, f1 * (P t y - P θ y) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum, hsum, sub_self, mul_zero]
    have hterm : ∀ y, P θ y * f (P t y / P θ y) =
        P θ y * g (P t y / P θ y) + f1 * (P t y - P θ y) +
          (1 / 2 : ℝ) * f2 / P θ y * (P t y - P θ y) ^ 2 := by
      intro y
      have hp : P θ y ≠ 0 := (hpos y).ne'
      simp only [g, hf1]
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_add_distrib,
      Finset.sum_add_distrib, hfirst, add_zero, fisherInformation, Finset.mul_sum,
      Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    have hp : P θ y ≠ 0 := (hpos y).ne'
    field_simp
    ring
  refine IsLittleO.congr' ?_ (Eventually.of_forall fun t => (hident t).symm) EventuallyEq.rfl
  apply IsLittleO.sum
  intro y _
  have hp : P θ y ≠ 0 := (hpos y).ne'
  have hd := (hP y).hasDerivAt
  -- the first-order increment of the coordinate is `O(t - θ)`
  have hbig : (fun t => P t y - P θ y) =O[𝓝 θ] (fun t => t - θ) := hd.isBigO_sub
  have hlin : (fun t => P t y - P θ y - (t - θ) • deriv (fun s => P s y) θ) =o[𝓝 θ]
      (fun t => t - θ) := hasDerivAt_iff_isLittleO.1 hd
  -- the ratio tends to one
  have hcont : Tendsto (fun t => P t y / P θ y) (𝓝 θ) (𝓝 1) := by
    have h := ((hP y).continuousAt.div_const (P θ y)).tendsto
    simpa [div_self hp] using h
  -- the Taylor remainder along the ratio
  have hg' : (fun t => g (P t y / P θ y)) =o[𝓝 θ] (fun t => (P t y / P θ y - 1) ^ 2) :=
    hg.comp_tendsto hcont
  have hratio : (fun t => (P t y / P θ y - 1) ^ 2) =O[𝓝 θ] (fun t => (t - θ) ^ 2) := by
    have h1 : (fun t => P t y / P θ y - 1) =O[𝓝 θ] (fun t => t - θ) := by
      have : (fun t => P t y / P θ y - 1) = fun t => (P θ y)⁻¹ * (P t y - P θ y) := by
        funext t
        field_simp
      rw [this]
      exact hbig.const_mul_left _
    simpa [pow_two] using h1.mul h1
  have hA : (fun t => P θ y * g (P t y / P θ y)) =o[𝓝 θ] (fun t => (t - θ) ^ 2) :=
    (hg'.trans_isBigO hratio).const_mul_left _
  -- the difference of squares is `o((t - θ)²)`
  have hdiff : (fun t => P t y - P θ y - deriv (fun s => P s y) θ * (t - θ)) =o[𝓝 θ]
      (fun t => t - θ) := by
    refine hlin.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp [smul_eq_mul, mul_comm]
  have hsumO : (fun t => P t y - P θ y + deriv (fun s => P s y) θ * (t - θ)) =O[𝓝 θ]
      (fun t => t - θ) :=
    hbig.add ((isBigO_refl (fun t : ℝ => t - θ) (𝓝 θ)).const_mul_left _)
  have hsq : (fun t => (P t y - P θ y) ^ 2 - (deriv (fun s => P s y) θ * (t - θ)) ^ 2) =o[𝓝 θ]
      (fun t => (t - θ) ^ 2) := by
    have h := hdiff.mul_isBigO hsumO
    refine h.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · ring
    · ring
  exact hA.add (hsq.const_mul_left _)

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleFisher
