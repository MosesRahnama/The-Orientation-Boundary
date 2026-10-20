import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false

/-!
# Local Fisher information and triangular discrimination

The N11 expansion relates triangular discrimination to one half of the Fisher information.
The Bernoulli example fixes the binary symmetric constant. The support boundary is handled separately.

Node N34 states every expansion at pointwise smoothness. With positive masses at `θ`,
coordinates differentiable at `θ` give the first-order form with remainder `o((t - θ)²)`,
the two-sided band, the zero-Fisher statement and the conditional information and cost
bounds; coordinates twice differentiable at `θ` (`TwiceDifferentiableAt`) give the cubic
remainder. Each form under `ContDiff ℝ 2` on the real line is a corollary.
-/

namespace OperatorKO7.Meta.BoundaryObserver.FisherDiscrimination

open scoped BigOperators
open Asymptotics

/-- Fisher information sums squared parameter derivatives over the coordinate masses
of a finite family, using total real division at zero. -/
noncomputable def fisherInformation {Y : Type} [Fintype Y]
    (P : ℝ → Y → ℝ) (θ : ℝ) : ℝ :=
  ∑ y, (deriv (fun t => P t y) θ) ^ 2 / P θ y

/-- A real curve is twice differentiable at `θ`: it is differentiable at every point
of a neighborhood of `θ`, and its derivative is differentiable at `θ`. Nothing is
required away from that neighborhood, and the second derivative need not be continuous. -/
def TwiceDifferentiableAt (f : ℝ → ℝ) (θ : ℝ) : Prop :=
  (∀ᶠ t in nhds θ, DifferentiableAt ℝ f t) ∧ DifferentiableAt ℝ (deriv f) θ

/-- A curve of class `C²` on the real line is twice differentiable at every point. -/
theorem twiceDifferentiableAt_of_contDiff (f : ℝ → ℝ) (θ : ℝ) (hf : ContDiff ℝ 2 f) :
    TwiceDifferentiableAt f θ :=
  ⟨Filter.Eventually.of_forall (fun _ => (hf.differentiable (by norm_num)).differentiableAt),
    hf.differentiable_deriv_two.differentiableAt⟩

/-- Twice differentiability at `θ` gives differentiability at `θ`. -/
theorem TwiceDifferentiableAt.differentiableAt {f : ℝ → ℝ} {θ : ℝ}
    (hf : TwiceDifferentiableAt f θ) : DifferentiableAt ℝ f θ :=
  hf.1.self_of_nhds

/-- The pointwise hypothesis is strictly weaker than class `C²` on the real line: the
curve `t ↦ 1 + |t|` is twice differentiable at `1`, where its value is positive, and it
is not of class `C²`, since it has no derivative at `0`. -/
theorem twiceDifferentiableAt_strictly_weaker :
    TwiceDifferentiableAt (fun t : ℝ => 1 + |t|) 1 ∧
      ¬ ContDiff ℝ 2 (fun t : ℝ => 1 + |t|) := by
  have hloc : ∀ x : ℝ, 0 < x →
      (fun t : ℝ => 1 + |t|) =ᶠ[nhds x] (fun t => 1 + t) := by
    intro x hx
    filter_upwards [Ioi_mem_nhds hx] with t ht
    rw [abs_of_pos ht]
  have hdiff : ∀ x : ℝ, 0 < x → HasDerivAt (fun t : ℝ => 1 + |t|) 1 x := by
    intro x hx
    have h : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    exact h.congr_of_eventuallyEq (hloc x hx)
  have hnear : Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) := Ioi_mem_nhds one_pos
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · filter_upwards [hnear] with t ht
    exact (hdiff t ht).differentiableAt
  · have hd : deriv (fun t : ℝ => 1 + |t|) =ᶠ[nhds (1 : ℝ)] (fun _ => (1 : ℝ)) := by
      filter_upwards [hnear] with t ht
      exact (hdiff t ht).deriv
    exact (differentiableAt_const (1 : ℝ)).congr_of_eventuallyEq hd
  · intro hc
    apply not_differentiableAt_abs_zero
    have h0 : DifferentiableAt ℝ (fun t : ℝ => 1 + |t|) 0 :=
      (hc.differentiable (by norm_num)).differentiableAt
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (1 + |t|) - 1) 0 := h0.sub_const 1
    have heq : (fun t : ℝ => (1 + |t|) - 1) = (abs : ℝ → ℝ) := by
      funext t
      simp
    rwa [heq] at h1

/-- Second-order Taylor expansion with Peano remainder at one point: a curve twice
differentiable at `θ` agrees with its quadratic Taylor polynomial at `θ` up to
`o((t - θ)²)`. The remainder vanishes at `θ`, and on a ball around `θ` its derivative is
`o(t - θ)` by the differentiability of the derivative at `θ`; the mean value inequality
of `Convex.isLittleO_pow_succ_real` then bounds the remainder. -/
theorem taylor_two_littleO_at (f : ℝ → ℝ) (θ : ℝ) (hf : TwiceDifferentiableAt f θ) :
    (fun t => f t - f θ - deriv f θ * (t - θ) -
        (1 / 2 : ℝ) * deriv (deriv f) θ * (t - θ) ^ 2) =o[nhds θ]
      (fun t => (t - θ) ^ 2) := by
  obtain ⟨hd, hd2⟩ := hf
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hd
  have hs : Convex ℝ (Metric.ball θ r) := convex_ball θ r
  have hθs : θ ∈ Metric.ball θ r := Metric.mem_ball_self hr
  have hsn : Metric.ball θ r ∈ nhds θ := Metric.ball_mem_nhds θ hr
  have hg : ∀ x ∈ Metric.ball θ r,
      HasDerivWithinAt (fun t => f t - f θ - deriv f θ * (t - θ) -
        (1 / 2 : ℝ) * deriv (deriv f) θ * (t - θ) ^ 2)
        (deriv f x - deriv f θ - deriv (deriv f) θ * (x - θ)) (Metric.ball θ r) x := by
    intro x hx
    have h1 : HasDerivAt f (deriv f x) x := (hball x hx).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => deriv f θ * (t - θ)) (deriv f θ) x := by
      simpa using ((hasDerivAt_id x).sub_const θ).const_mul (deriv f θ)
    have h3 : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * deriv (deriv f) θ * (t - θ) ^ 2)
        (deriv (deriv f) θ * (x - θ)) x := by
      have h := (((hasDerivAt_id x).sub_const θ).pow 2).const_mul
        ((1 / 2 : ℝ) * deriv (deriv f) θ)
      convert h using 1
      simp
      ring
    exact (((h1.sub_const (f θ)).sub h2).sub h3).hasDerivWithinAt
  have hg' : (fun x => deriv f x - deriv f θ - deriv (deriv f) θ * (x - θ))
      =o[nhdsWithin θ (Metric.ball θ r)] (fun x => (x - θ) ^ 1) := by
    have h := hasDerivAt_iff_isLittleO.mp hd2.hasDerivAt
    refine ((h.mono nhdsWithin_le_nhds).congr_left ?_).congr_right ?_
    · intro x
      simp only [smul_eq_mul]
      ring
    · intro x
      simp
  have key := hs.isLittleO_pow_succ_real hθs hg hg'
  rw [nhdsWithin_eq_nhds.mpr hsn] at key
  simpa using key

/-- A curve twice differentiable at `θ` has a quadratic error after its linear term. -/
private theorem first_order_remainder_bigO (f : ℝ → ℝ) (θ : ℝ)
    (hf : TwiceDifferentiableAt f θ) :
    (fun t => f t - f θ - deriv f θ * (t - θ)) =O[nhds θ]
      (fun t => (t - θ) ^ 2) := by
  have ht := taylor_two_littleO_at f θ hf
  have hquad :
      (fun t : ℝ => ((1 / 2 : ℝ) * deriv (deriv f) θ) * (t - θ) ^ 2)
        =O[nhds θ] (fun t => (t - θ) ^ 2) :=
    isBigO_const_mul_self _ _ _
  refine (ht.isBigO.add hquad).congr_left ?_
  intro t
  ring

/-- A positive coordinate twice differentiable at the parameter contributes its
Fisher quadratic term with a cubic error to triangular discrimination. -/
private theorem discrimination_term_second_order (f : ℝ → ℝ) (θ : ℝ)
    (hf : TwiceDifferentiableAt f θ) (hpos : 0 < f θ) :
    (fun t => (f θ - f t) ^ 2 / (f θ + f t) -
        ((deriv f θ) ^ 2 / (2 * f θ)) * (t - θ) ^ 2) =O[nhds θ]
      (fun t => (t - θ) ^ 3) := by
  have hcont : ContinuousAt (fun t : ℝ => f θ + f t) θ :=
    continuousAt_const.add hf.differentiableAt.continuousAt
  have hden : f θ + f θ ≠ 0 := by linarith
  have hne : ∀ᶠ t in nhds θ, f θ + f t ≠ 0 :=
    hcont.eventually_ne hden
  have hInv :
      (fun t : ℝ => (f θ + f t)⁻¹) =O[nhds θ] (fun _ : ℝ => (1 : ℝ)) :=
    (hcont.inv₀ hden).tendsto.isBigO_one ℝ
  have hderiv : HasDerivAt f (deriv f θ) θ :=
    hf.differentiableAt.hasDerivAt
  have hu :
      (fun t : ℝ => f t - f θ) =O[nhds θ] (fun t => t - θ) :=
    hderiv.isBigO_sub
  have hlin :
      (fun t : ℝ => deriv f θ * (t - θ)) =O[nhds θ]
        (fun t => t - θ) :=
    isBigO_const_mul_self _ _ _
  have hrem := first_order_remainder_bigO f θ hf
  have hprod1 :
      (fun t : ℝ => ((f t - f θ - deriv f θ * (t - θ)) *
          ((f t - f θ) + deriv f θ * (t - θ))) * (f θ + f t)⁻¹)
        =O[nhds θ] (fun t => (t - θ) ^ 3) := by
    convert ((hrem.mul (hu.add hlin)).mul hInv) using 1
    ext t
    ring
  have hquad :
      (fun t : ℝ => ((deriv f θ) ^ 2 / (2 * f θ)) * (t - θ) ^ 2)
        =O[nhds θ] (fun t => (t - θ) ^ 2) :=
    isBigO_const_mul_self _ _ _
  have hprod2 :
      (fun t : ℝ => (((deriv f θ) ^ 2 / (2 * f θ)) * (t - θ) ^ 2 *
        (f t - f θ)) * (f θ + f t)⁻¹)
        =O[nhds θ] (fun t => (t - θ) ^ 3) := by
    convert ((hquad.mul hu).mul hInv) using 1
    ext t
    ring
  refine (hprod1.sub hprod2).congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hne] with t ht
  have ha : f θ ≠ 0 := ne_of_gt hpos
  field_simp [ha, ht]
  ring

/-- The triangular discrimination of a finite family with positive masses at `θ`, each
coordinate twice differentiable at `θ` only, has one half of its Fisher information as
quadratic coefficient and a cubic remainder. -/
theorem discrimination_second_order_at {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ)
    (θ : ℝ) (hP : ∀ y, TwiceDifferentiableAt (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) :
    (fun t => BoundarySingularity.discrimination (P θ) (P t) -
      (1 / 2 : ℝ) * fisherInformation P θ * (t - θ) ^ 2)
      =O[nhds θ] (fun t => (t - θ) ^ 3) := by
  have hcoeff :
      (∑ y : Y, (deriv (fun t => P t y) θ) ^ 2 / (2 * P θ y)) =
        (1 / 2 : ℝ) * fisherInformation P θ := by
    rw [fisherInformation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hp : P θ y ≠ 0 := ne_of_gt (hpos y)
    field_simp [hp]
  have hsum :
      (fun t : ℝ =>
        ∑ y : Y, ((P θ y - P t y) ^ 2 / (P θ y + P t y) -
          ((deriv (fun u => P u y) θ) ^ 2 / (2 * P θ y)) * (t - θ) ^ 2))
        =O[nhds θ] (fun t => (t - θ) ^ 3) := by
    simpa using
      (IsBigO.sum (s := Finset.univ) (fun y _ =>
        discrimination_term_second_order (fun t => P t y) θ (hP y) (hpos y)))
  convert hsum using 1
  funext t
  simp only [BoundarySingularity.discrimination, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hcoeff, mul_assoc]

/-- The triangular discrimination of a finite smooth positive family has
one half its Fisher information as quadratic coefficient and a cubic error. -/
theorem discrimination_second_order {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ)
    (θ : ℝ) (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) :
    (fun t => BoundarySingularity.discrimination (P θ) (P t) -
      (1 / 2 : ℝ) * fisherInformation P θ * (t - θ) ^ 2)
      =O[nhds θ] (fun t => (t - θ) ^ 3) :=
  discrimination_second_order_at P θ
    (fun y => twiceDifferentiableAt_of_contDiff _ θ (hP y)) hpos

/-- The Bernoulli family has Fisher information four at its fair parameter. -/
theorem bernoulli_fisher_half :
    fisherInformation (fun (t : ℝ) (b : Bool) => if b then t else 1 - t)
      (1 / 2 : ℝ) = 4 := by
  have hderiv : deriv (fun t : ℝ => 1 - t) (1 / 2 : ℝ) = -1 := by
    simpa [deriv_id] using
      (deriv_const_sub (f := (id : ℝ → ℝ)) (x := (1 / 2 : ℝ)) (1 : ℝ))
  norm_num [fisherInformation, Fintype.sum_bool, deriv_id, hderiv]

/-- The binary-channel discrimination equals the Fisher quadratic term at distance
two times the channel bias. -/
theorem binary_check_constant (ε : ℝ) :
    (1 / 2 : ℝ) * 4 * (2 * ε) ^ 2 = 8 * ε ^ 2 ∧
      BoundarySingularity.discrimination
        (ProtocolResolution.binaryKernel ε true)
        (ProtocolResolution.binaryKernel ε false) =
          (1 / 2 : ℝ) * 4 * (2 * ε) ^ 2 := by
  constructor
  · ring
  · rw [BoundarySingularity.discrimination_binaryKernel]
    ring

theorem zero_coordinate_discrimination_term (b : ℝ) :
    (b ^ 2) / b = b := by
  by_cases h : b = 0
  · simp [h]
  · field_simp [h]
    ring

/-- Any missing initial coordinate contributes its new mass to discrimination. -/
theorem discrimination_ge_new_support_mass {Y : Type} [Fintype Y]
    (P Q : Y → ℝ) (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (y : Y) (hz : P y = 0) :
    Q y ≤ BoundarySingularity.discrimination P Q := by
  calc
    Q y = (P y - Q y) ^ 2 / (P y + Q y) := by
      simpa [hz] using (zero_coordinate_discrimination_term (Q y)).symm
    _ ≤ BoundarySingularity.discrimination P Q := by
      unfold BoundarySingularity.discrimination
      exact Finset.single_le_sum
        (fun a _ => BoundarySingularity.discrimination_term_nonneg
          (P a) (Q a) (hP a) (hQ a))
        (Finset.mem_univ y)

/-- Positive base masses give a nonnegative Fisher coefficient. -/
theorem fisherInformation_nonnegative {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ)
    (θ : ℝ) (hpos : ∀ y, 0 < P θ y) : 0 ≤ fisherInformation P θ := by
  unfold fisherInformation
  exact Finset.sum_nonneg (fun y _ => div_nonneg (sq_nonneg _) (hpos y).le)

theorem fisher_zero_of_deriv_zero {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ : ℝ)
    (hzero : ∀ y, deriv (fun t => P t y) θ = 0) : fisherInformation P θ = 0 := by
  simp [fisherInformation, hzero]

/-- At positive support, Fisher information is zero exactly when every
coordinate has zero first parameter derivative. -/
theorem fisherInformation_eq_zero_iff_deriv_zero {Y : Type} [Fintype Y]
    (P : ℝ → Y → ℝ) (θ : ℝ) (hpos : ∀ y, 0 < P θ y) :
    fisherInformation P θ = 0 ↔ ∀ y, deriv (fun t => P t y) θ = 0 := by
  constructor
  · intro h y
    have hs : (∑ a : Y, (deriv (fun t => P t a) θ) ^ 2 / P θ a) = 0 := by
      simpa only [fisherInformation] using h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => div_nonneg (sq_nonneg _) (hpos a).le)).mp hs
    have ht := hz y (Finset.mem_univ y)
    have hsq : (deriv (fun t => P t y) θ) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp ht with he | hd
      · exact he
      · exact False.elim ((ne_of_gt (hpos y)) hd)
    exact (pow_eq_zero_iff two_ne_zero).mp hsq
  · exact fisher_zero_of_deriv_zero P θ

def quadraticLaw (t : ℝ) (b : Bool) : ℝ := if b then t ^ 2 else 1 - t ^ 2

theorem quadraticLaw_sum (t : ℝ) : quadraticLaw t false + quadraticLaw t true = 1 := by
  simp [quadraticLaw]


/-- These polynomial coordinates form a probability law whenever their
squared parameter lies in the unit interval. -/
theorem quadraticLaw_nonnegative (t : ℝ) (ht : t ^ 2 ≤ 1) (b : Bool) :
    0 ≤ quadraticLaw t b := by
  cases b
  · change 0 ≤ 1 - t ^ 2
    linarith
  · change 0 ≤ t ^ 2
    exact sq_nonneg t

/-- An actual finite probability law, not just two symbolic row formulas. -/
noncomputable def quadraticFiniteLaw (t : ℝ) (ht : t ^ 2 ≤ 1) :
    ProtocolResolution.FiniteLaw Bool where
  mass := quadraticLaw t
  nonnegative := quadraticLaw_nonnegative t ht
  total := by
    simpa only [Fintype.sum_bool, add_comm] using quadraticLaw_sum t

theorem quadraticLaw_fisher_zero : fisherInformation quadraticLaw 0 = 0 := by
  apply fisher_zero_of_deriv_zero
  intro b
  cases b
  · change deriv (fun t : ℝ => 1 - t ^ 2) 0 = 0
    have h := deriv_const_sub (f := fun t : ℝ => t ^ 2) (x := 0) (1 : ℝ)
    rw [h, deriv_pow_field]
    norm_num
  · change deriv (fun t : ℝ => t ^ 2) 0 = 0
    rw [deriv_pow_field]
    norm_num

theorem quadraticLaw_half_discrimination :
    BoundarySingularity.discrimination (quadraticLaw 0) (quadraticLaw (1 / 2)) = 2 / 7 := by
  norm_num [BoundarySingularity.discrimination, quadraticLaw, Fintype.sum_bool]

/-- The new output support contributes at least a quadratic term even though
the Fisher coefficient at the boundary vanishes. -/
theorem quadraticLaw_boundary_lower (t : ℝ) (ht : t ^ 2 ≤ 1) :
    t ^ 2 ≤ BoundarySingularity.discrimination (quadraticLaw 0) (quadraticLaw t) := by
  have hbase : quadraticLaw 0 true = 0 := by norm_num [quadraticLaw]
  have h := discrimination_ge_new_support_mass (quadraticLaw 0) (quadraticLaw t)
    (quadraticLaw_nonnegative 0 (by norm_num))
    (quadraticLaw_nonnegative t ht) true hbase
  simpa [quadraticLaw] using h

private theorem cube_small (θ : ℝ) :
    (fun t : ℝ => (t - θ) ^ 3) =o[nhds θ] (fun t => (t - θ) ^ 2) := by
  apply (isLittleO_pow_pow (𝕜 := ℝ) (by norm_num : 2 < 3)).comp_tendsto
  have hid : Filter.Tendsto (fun t : ℝ => t) (nhds θ) (nhds θ) := Filter.tendsto_id
  have hc : Filter.Tendsto (fun _ : ℝ => θ) (nhds θ) (nhds θ) := tendsto_const_nhds
  simpa using hid.sub hc

/-- A positive coordinate differentiable at the parameter contributes its Fisher
quadratic term to triangular discrimination with an error `o((t - θ)²)`; no second
derivative enters. -/
private theorem discrimination_term_first_order (f : ℝ → ℝ) (θ : ℝ)
    (hf : DifferentiableAt ℝ f θ) (hpos : 0 < f θ) :
    (fun t => (f θ - f t) ^ 2 / (f θ + f t) -
        ((deriv f θ) ^ 2 / (2 * f θ)) * (t - θ) ^ 2) =o[nhds θ]
      (fun t => (t - θ) ^ 2) := by
  have hcont : ContinuousAt (fun t : ℝ => f θ + f t) θ :=
    continuousAt_const.add hf.continuousAt
  have hden : f θ + f θ ≠ 0 := by linarith
  have hne : ∀ᶠ t in nhds θ, f θ + f t ≠ 0 :=
    hcont.eventually_ne hden
  have hInv :
      (fun t : ℝ => (f θ + f t)⁻¹) =O[nhds θ] (fun _ : ℝ => (1 : ℝ)) :=
    (hcont.inv₀ hden).tendsto.isBigO_one ℝ
  have hderiv : HasDerivAt f (deriv f θ) θ := hf.hasDerivAt
  have hu :
      (fun t : ℝ => f t - f θ) =O[nhds θ] (fun t => t - θ) :=
    hderiv.isBigO_sub
  have hlin :
      (fun t : ℝ => deriv f θ * (t - θ)) =O[nhds θ]
        (fun t => t - θ) :=
    isBigO_const_mul_self _ _ _
  have hrem :
      (fun t : ℝ => f t - f θ - deriv f θ * (t - θ)) =o[nhds θ]
        (fun t => t - θ) := by
    refine (hasDerivAt_iff_isLittleO.mp hderiv).congr_left ?_
    intro t
    simp only [smul_eq_mul]
    ring
  have hprod1 :
      (fun t : ℝ => ((f t - f θ - deriv f θ * (t - θ)) *
          ((f t - f θ) + deriv f θ * (t - θ))) * (f θ + f t)⁻¹)
        =o[nhds θ] (fun t => (t - θ) ^ 2) := by
    refine ((hrem.mul_isBigO (hu.add hlin)).mul_isBigO hInv).congr_right ?_
    intro t
    ring
  have hquad :
      (fun t : ℝ => ((deriv f θ) ^ 2 / (2 * f θ)) * (t - θ) ^ 2)
        =O[nhds θ] (fun t => (t - θ) ^ 2) :=
    isBigO_const_mul_self _ _ _
  have hprod2 :
      (fun t : ℝ => (((deriv f θ) ^ 2 / (2 * f θ)) * (t - θ) ^ 2 *
        (f t - f θ)) * (f θ + f t)⁻¹)
        =o[nhds θ] (fun t => (t - θ) ^ 2) := by
    have h3 :
        (fun t : ℝ => (((deriv f θ) ^ 2 / (2 * f θ)) * (t - θ) ^ 2 *
          (f t - f θ)) * (f θ + f t)⁻¹)
          =O[nhds θ] (fun t => (t - θ) ^ 3) := by
      refine ((hquad.mul hu).mul hInv).congr_right ?_
      intro t
      ring
    exact h3.trans_isLittleO (cube_small θ)
  refine (hprod1.sub hprod2).congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hne] with t ht
  have ha : f θ ≠ 0 := ne_of_gt hpos
  field_simp [ha, ht]
  ring

/-- First-order form of the expansion: for a finite family with positive masses at
`θ` and each coordinate differentiable at `θ` only, the discrimination is one half of
the Fisher information times `(t - θ)²` up to `o((t - θ)²)`. -/
theorem discrimination_remainder_littleO_at {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ) (hpos : ∀ y, 0 < P θ y) :
    (fun t => BoundarySingularity.discrimination (P θ) (P t) -
      (1 / 2 : ℝ) * fisherInformation P θ * (t - θ) ^ 2)
      =o[nhds θ] (fun t => (t - θ) ^ 2) := by
  have hcoeff :
      (∑ y : Y, (deriv (fun t => P t y) θ) ^ 2 / (2 * P θ y)) =
        (1 / 2 : ℝ) * fisherInformation P θ := by
    rw [fisherInformation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hp : P θ y ≠ 0 := ne_of_gt (hpos y)
    field_simp [hp]
  have hsum :
      (fun t : ℝ =>
        ∑ y : Y, ((P θ y - P t y) ^ 2 / (P θ y + P t y) -
          ((deriv (fun u => P u y) θ) ^ 2 / (2 * P θ y)) * (t - θ) ^ 2))
        =o[nhds θ] (fun t => (t - θ) ^ 2) := by
    simpa using
      (IsLittleO.sum (s := Finset.univ) (fun y _ =>
        discrimination_term_first_order (fun t => P t y) θ (hP y) (hpos y)))
  convert hsum using 1
  funext t
  simp only [BoundarySingularity.discrimination, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hcoeff, mul_assoc]

theorem discrimination_remainder_littleO {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y)) (hpos : ∀ y, 0 < P θ y) :
    (fun t => BoundarySingularity.discrimination (P θ) (P t) -
      (1 / 2 : ℝ) * fisherInformation P θ * (t - θ) ^ 2)
      =o[nhds θ] (fun t => (t - θ) ^ 2) :=
  discrimination_remainder_littleO_at P θ
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos

/-- At zero Fisher information, positive masses at `θ` and coordinates differentiable
at `θ` give a discrimination of order `o((t - θ)²)`. -/
theorem zero_fisher_discrimination_littleO_at {Y : Type} [Fintype Y]
    (P : ℝ → Y → ℝ) (θ : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ) (hpos : ∀ y, 0 < P θ y)
    (hz : fisherInformation P θ = 0) :
    (fun t => BoundarySingularity.discrimination (P θ) (P t))
      =o[nhds θ] (fun t => (t - θ) ^ 2) := by
  simpa [hz] using discrimination_remainder_littleO_at P θ hP hpos

theorem zero_fisher_discrimination_littleO {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y)) (hpos : ∀ y, 0 < P θ y)
    (hz : fisherInformation P θ = 0) :
    (fun t => BoundarySingularity.discrimination (P θ) (P t))
      =o[nhds θ] (fun t => (t - θ) ^ 2) :=
  zero_fisher_discrimination_littleO_at P θ
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hz

/-- The local upper band of the discrimination for coordinates differentiable at `θ`
with positive masses at `θ`. -/
theorem discrimination_local_upper_at {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ) (hpos : ∀ y, 0 < P θ y)
    (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, BoundarySingularity.discrimination (P θ) (P t) ≤
      (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 := by
  have hs := (discrimination_remainder_littleO_at P θ hP hpos).bound hε
  filter_upwards [hs] with t ht
  have ha : |BoundarySingularity.discrimination (P θ) (P t) -
      (1 / 2 : ℝ) * fisherInformation P θ * (t - θ) ^ 2| ≤ ε * (t - θ) ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (t - θ))] using ht
  nlinarith [(abs_le.mp ha).2]

theorem discrimination_local_upper {Y : Type} [Fintype Y] (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y)) (hpos : ∀ y, 0 < P θ y)
    (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, BoundarySingularity.discrimination (P θ) (P t) ≤
      (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 :=
  discrimination_local_upper_at P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

/-- Both sides of the local quadratic band for coordinates differentiable at `θ` with
positive masses at `θ`, from the first-order remainder `o((t - θ)²)`, with no
assumption that the Fisher information is nonzero. -/
theorem discrimination_local_quadratic_band_at {Y : Type} [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ,
      (fisherInformation P θ / 2 - ε) * (t - θ) ^ 2 ≤
        BoundarySingularity.discrimination (P θ) (P t) ∧
      BoundarySingularity.discrimination (P θ) (P t) ≤
        (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 := by
  have hs := (discrimination_remainder_littleO_at P θ hP hpos).bound hε
  filter_upwards [hs] with t ht
  have ha : |BoundarySingularity.discrimination (P θ) (P t) -
      (1 / 2 : ℝ) * fisherInformation P θ * (t - θ) ^ 2| ≤
      ε * (t - θ) ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (t - θ))] using ht
  rcases abs_le.mp ha with ⟨hl, hu⟩
  constructor <;> nlinarith

/-- Both sides of the local quadratic discrimination approximation for a family of
class `C²`, as a corollary of `discrimination_local_quadratic_band_at`, with no
assumption that Fisher is nonzero. -/
theorem discrimination_local_quadratic_band {Y : Type} [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ,
      (fisherInformation P θ / 2 - ε) * (t - θ) ^ 2 ≤
        BoundarySingularity.discrimination (P θ) (P t) ∧
      BoundarySingularity.discrimination (P θ) (P t) ≤
        (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 :=
  discrimination_local_quadratic_band_at P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

theorem pairMenu_capacity_upper {A Y : Type} [Fintype A] [Fintype Y]
    (p : ProtocolResolution.FiniteProtocol Bool A Y) (δ B : ℝ)
    (menu : BoundarySingularity.PairMenu p δ) (hδB : δ ≤ B) (hB : 0 ≤ B) :
    ProtocolResolution.LocalCapacityBound p (B / Real.log 2) := by
  intro h a hw _ _
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    ProtocolResolution.localGain p h a ≤ δ / Real.log 2 :=
      BoundarySingularity.pairMenu_localGain_le p δ menu h a hw
    _ ≤ B / Real.log 2 := div_le_div_of_nonneg_right hδB hlog.le
    _ ≤ (B / Real.log 2) * p.cost h a :=
      le_mul_of_one_le_right (div_nonneg hB hlog.le) (menu.reading_cost h a)

theorem conditionalPairMenu_capacity_upper {H0 A Y : Type} [Fintype H0] [Fintype A] [Fintype Y]
    (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y) (δ B : ℝ)
    (menu : BoundarySingularity.ConditionalPairMenu p δ) (hδB : δ ≤ B) (hB : 0 ≤ B) :
    ∀ u, 0 < p.initialRecord.mass u → ProtocolResolution.LocalCapacityBound (p.given u) (B / Real.log 2) := by
  intro u hu
  exact pairMenu_capacity_upper (p.given u) δ B (menu.atRecord u hu) hδB hB

/-- For coordinates differentiable at `θ` with positive masses at `θ`: near `θ`, every
conditional protocol whose permitted readings stay within the discrimination of the two
laws acquires at every horizon at most `(I(θ)/2 + ε)(t - θ)² / ln 2` times its expected
cost. -/
theorem fisher_local_conditional_information_bound_at {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ) (hpos : ∀ y, 0 < P θ y)
    (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t))) (n : ℕ)
      (bank : List (List (A × Y))), ProtocolResolution.HistoryBank n bank →
      ProtocolResolution.conditionalJointInfo p n bank ≤
      ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 / Real.log 2) *
        ProtocolResolution.conditionalExpectedCost p n bank := by
  filter_upwards [discrimination_local_upper_at P θ ε hP hpos hε] with t ht p menu n bank hb
  have hcoeff : 0 ≤ fisherInformation P θ / 2 + ε :=
    add_nonneg (div_nonneg (fisherInformation_nonnegative P θ hpos) (by norm_num)) hε.le
  have hB : 0 ≤ (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 :=
    mul_nonneg hcoeff (sq_nonneg _)
  exact (ProtocolResolution.conditionalJointInfo_bounds p n bank hb _
    (conditionalPairMenu_capacity_upper p _ _ menu ht hB)).2.2.2.2

/-- The conditional cost lower bound at every horizon for coordinates differentiable at
`θ` with positive masses at `θ`, without assuming a capacity or cost inequality as a
premise. -/
theorem fisher_local_conditional_cost_lower_at {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t)))
      (n : ℕ) (bank : List (List (A × Y))),
      ProtocolResolution.HistoryBank n bank →
      ∀ c, c ≤ ProtocolResolution.conditionalJointInfo p n bank →
        c * Real.log 2 ≤ ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) *
          ProtocolResolution.conditionalExpectedCost p n bank := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  filter_upwards [fisher_local_conditional_information_bound_at (H0 := H0) (A := A)
      P θ ε hP hpos hε]
    with t ht p menu n bank hb c hc
  have hi := hc.trans (ht p menu n bank hb)
  calc
    c * Real.log 2 ≤
        (((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 / Real.log 2) *
          ProtocolResolution.conditionalExpectedCost p n bank) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hi hlog.le
    _ = ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) *
          ProtocolResolution.conditionalExpectedCost p n bank := by
      field_simp [(ne_of_gt hlog)]
      ring

/-- The local Fisher bound on the information limit for coordinates differentiable at
`θ` with positive masses at `θ`, even if the stopped protocol has infinite total expected
cost. -/
theorem fisher_local_conditional_limit_bound_at {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t))),
      ENNReal.ofReal (ProtocolResolution.conditionalInformationLimit p) ≤
        ENNReal.ofReal (((fisherInformation P θ / 2 + ε) *
          (t - θ) ^ 2) / Real.log 2) *
          ProtocolResolution.conditionalExtendedCost p := by
  filter_upwards [discrimination_local_upper_at P θ ε hP hpos hε] with t ht p menu
  have hcoeff : 0 ≤ fisherInformation P θ / 2 + ε :=
    add_nonneg (div_nonneg (fisherInformation_nonnegative P θ hpos) (by norm_num)) hε.le
  have hB : 0 ≤ (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 :=
    mul_nonneg hcoeff (sq_nonneg _)
  exact ProtocolResolution.conditionalInformationLimit_le_extendedCost p _
    (div_nonneg hB (Real.log_pos one_lt_two).le)
    (conditionalPairMenu_capacity_upper p _ _ menu ht hB)

/-- A finite total-cost budget bounds the conditional information limit for
coordinates differentiable at `θ` with positive masses at `θ`; the coefficient also
covers Fisher information zero. -/
theorem fisher_local_conditional_budget_lower_at {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t)))
      (c budget : ℝ), 0 ≤ budget →
      c ≤ ProtocolResolution.conditionalInformationLimit p →
      ProtocolResolution.conditionalExtendedCost p ≤ ENNReal.ofReal budget →
      c * Real.log 2 ≤ ((fisherInformation P θ / 2 + ε) *
        (t - θ) ^ 2) * budget := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  filter_upwards [discrimination_local_upper_at P θ ε hP hpos hε]
    with t ht p menu c budget hb hc hcost
  have hcoeff : 0 ≤ fisherInformation P θ / 2 + ε :=
    add_nonneg (div_nonneg (fisherInformation_nonnegative P θ hpos) (by norm_num)) hε.le
  have hB : 0 ≤ (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 :=
    mul_nonneg hcoeff (sq_nonneg _)
  have hi := ProtocolResolution.conditionalInformationLimit_le_budget p
    (((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) / Real.log 2) budget
    (div_nonneg hB hlog.le) hb
    (conditionalPairMenu_capacity_upper p _ _ menu ht hB) hcost
  calc
    c * Real.log 2 ≤
        ((((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) / Real.log 2) *
          budget) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (hc.trans hi) hlog.le
    _ = ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) * budget := by
      field_simp [(ne_of_gt hlog)]
      ring

/-- Away from the base parameter, every qualifying conditional strategy pays at least
the reciprocal quadratic Fisher-envelope price, for coordinates differentiable at `θ`
with positive masses at `θ`, with no need for `I(θ) > 0`. -/
theorem fisher_local_conditional_cost_reciprocal_at {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
        (BoundarySingularity.discrimination (P θ) (P t)))
      (n : ℕ) (bank : List (List (A × Y))),
      ProtocolResolution.HistoryBank n bank →
      ∀ c, c ≤ ProtocolResolution.conditionalJointInfo p n bank → t ≠ θ →
        c * Real.log 2 / ((fisherInformation P θ / 2 + ε) *
          (t - θ) ^ 2) ≤ ProtocolResolution.conditionalExpectedCost p n bank := by
  filter_upwards [fisher_local_conditional_cost_lower_at (H0 := H0) (A := A)
      P θ ε hP hpos hε]
    with t ht p menu n bank hb c hc htn
  have hcoef : 0 < fisherInformation P θ / 2 + ε :=
    add_pos_of_nonneg_of_pos
      (div_nonneg (fisherInformation_nonnegative P θ hpos) (by norm_num)) hε
  have hsq : 0 < (t - θ) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr htn)
  have hden : 0 < (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 :=
    mul_pos hcoef hsq
  apply (div_le_iff₀ hden).2
  calc
    c * Real.log 2 ≤
        ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) *
          ProtocolResolution.conditionalExpectedCost p n bank :=
      ht p menu n bank hb c hc
    _ = ProtocolResolution.conditionalExpectedCost p n bank *
        ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) := by ring

/-- In the limit, a fixed information target requires an inverse-quadratic budget at
every distinct parameter near `θ`, for coordinates differentiable at `θ` with positive
masses at `θ`. -/
theorem fisher_local_conditional_limit_reciprocal_at {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, DifferentiableAt ℝ (fun t => P t y) θ)
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
        (BoundarySingularity.discrimination (P θ) (P t)))
      (c budget : ℝ), 0 ≤ budget →
      c ≤ ProtocolResolution.conditionalInformationLimit p →
      ProtocolResolution.conditionalExtendedCost p ≤ ENNReal.ofReal budget →
      t ≠ θ →
      c * Real.log 2 / ((fisherInformation P θ / 2 + ε) *
        (t - θ) ^ 2) ≤ budget := by
  filter_upwards [fisher_local_conditional_budget_lower_at (H0 := H0) (A := A)
      P θ ε hP hpos hε]
    with t ht p menu c budget hb hc hcost htn
  have hcoef : 0 < fisherInformation P θ / 2 + ε :=
    add_pos_of_nonneg_of_pos
      (div_nonneg (fisherInformation_nonnegative P θ hpos) (by norm_num)) hε
  have hsq : 0 < (t - θ) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr htn)
  have hden : 0 < (fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 :=
    mul_pos hcoef hsq
  apply (div_le_iff₀ hden).2
  calc
    c * Real.log 2 ≤
        ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) * budget :=
      ht p menu c budget hb hc hcost
    _ = budget * ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) := by ring

theorem fisher_local_conditional_information_bound {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y)) (hpos : ∀ y, 0 < P θ y)
    (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t))) (n : ℕ)
      (bank : List (List (A × Y))), ProtocolResolution.HistoryBank n bank →
      ProtocolResolution.conditionalJointInfo p n bank ≤
      ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2 / Real.log 2) *
        ProtocolResolution.conditionalExpectedCost p n bank :=
  fisher_local_conditional_information_bound_at (H0 := H0) (A := A) P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

/-- A local Fisher upper bound yields a lower bound on actual conditional paid
cost, without assuming a capacity or cost inequality as a premise. -/
theorem fisher_local_conditional_cost_lower {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t)))
      (n : ℕ) (bank : List (List (A × Y))),
      ProtocolResolution.HistoryBank n bank →
      ∀ c, c ≤ ProtocolResolution.conditionalJointInfo p n bank →
        c * Real.log 2 ≤ ((fisherInformation P θ / 2 + ε) * (t - θ) ^ 2) *
          ProtocolResolution.conditionalExpectedCost p n bank :=
  fisher_local_conditional_cost_lower_at (H0 := H0) (A := A) P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

/-- The same local Fisher bound applies to the information limit, even if
the stopped protocol has infinite total expected cost. -/
theorem fisher_local_conditional_limit_bound {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t))),
      ENNReal.ofReal (ProtocolResolution.conditionalInformationLimit p) ≤
        ENNReal.ofReal (((fisherInformation P θ / 2 + ε) *
          (t - θ) ^ 2) / Real.log 2) *
          ProtocolResolution.conditionalExtendedCost p :=
  fisher_local_conditional_limit_bound_at (H0 := H0) (A := A) P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

/-- A finite total-cost budget bounds the conditional information acquired in
the local smooth regime; the coefficient also covers Fisher information zero. -/
theorem fisher_local_conditional_budget_lower {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
      (BoundarySingularity.discrimination (P θ) (P t)))
      (c budget : ℝ), 0 ≤ budget →
      c ≤ ProtocolResolution.conditionalInformationLimit p →
      ProtocolResolution.conditionalExtendedCost p ≤ ENNReal.ofReal budget →
      c * Real.log 2 ≤ ((fisherInformation P θ / 2 + ε) *
        (t - θ) ^ 2) * budget :=
  fisher_local_conditional_budget_lower_at (H0 := H0) (A := A) P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

/-- Away from the base parameter, every qualifying conditional strategy pays
at least the reciprocal quadratic Fisher-envelope price, with no need for I > 0. -/
theorem fisher_local_conditional_cost_reciprocal {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
        (BoundarySingularity.discrimination (P θ) (P t)))
      (n : ℕ) (bank : List (List (A × Y))),
      ProtocolResolution.HistoryBank n bank →
      ∀ c, c ≤ ProtocolResolution.conditionalJointInfo p n bank → t ≠ θ →
        c * Real.log 2 / ((fisherInformation P θ / 2 + ε) *
          (t - θ) ^ 2) ≤ ProtocolResolution.conditionalExpectedCost p n bank :=
  fisher_local_conditional_cost_reciprocal_at (H0 := H0) (A := A) P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

/-- In the limit, a fixed information target requires an inverse-quadratic
budget at every distinct parameter in the smooth positive-support regime. -/
theorem fisher_local_conditional_limit_reciprocal {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (P : ℝ → Y → ℝ) (θ ε : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) (hε : 0 < ε) :
    ∀ᶠ t in nhds θ, ∀ (p : ProtocolResolution.ConditionalProtocol H0 Bool A Y)
      (_ : BoundarySingularity.ConditionalPairMenu p
        (BoundarySingularity.discrimination (P θ) (P t)))
      (c budget : ℝ), 0 ≤ budget →
      c ≤ ProtocolResolution.conditionalInformationLimit p →
      ProtocolResolution.conditionalExtendedCost p ≤ ENNReal.ofReal budget →
      t ≠ θ →
      c * Real.log 2 / ((fisherInformation P θ / 2 + ε) *
        (t - θ) ^ 2) ≤ budget :=
  fisher_local_conditional_limit_reciprocal_at (H0 := H0) (A := A) P θ ε
    (fun y => (twiceDifferentiableAt_of_contDiff _ θ (hP y)).differentiableAt) hpos hε

end OperatorKO7.Meta.BoundaryObserver.FisherDiscrimination

namespace OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

open Asymptotics

/-- For a finite family with positive coordinates at the parameter and two
continuous derivatives, triangular discrimination has one half of the Fisher
information as its quadratic coefficient, with a cubic remainder. -/
theorem discrimination_second_order {Y : Type} [Fintype Y]
    (P : ℝ → Y → ℝ) (θ : ℝ)
    (hP : ∀ y, ContDiff ℝ 2 (fun t => P t y))
    (hpos : ∀ y, 0 < P θ y) :
    (fun t => discrimination (P θ) (P t) -
      (1 / 2 : ℝ) * FisherDiscrimination.fisherInformation P θ * (t - θ) ^ 2)
      =O[nhds θ] (fun t => (t - θ) ^ 3) := by
  exact FisherDiscrimination.discrimination_second_order P θ hP hpos

end OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
