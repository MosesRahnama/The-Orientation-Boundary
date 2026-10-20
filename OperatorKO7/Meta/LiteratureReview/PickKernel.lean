import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
Remark rem:pick-kernel is formalized for finite Stieltjes transforms and their
pointwise limits, proving the finite Gram formula for the transforms, the
Pick diagonal and positivity for both classes, and positive Schur complements
with zero base rows.

The analytic forward implication is narrowed to this class because no reusable
Nevanlinna-Pick theorem was located in the pinned Mathlib sources; the full
holomorphic forward implication is not asserted by this file.
The diagonal converse, kernel limit theorem, and Schur theorem are unrestricted.
-/

namespace PickKernel

open scoped BigOperators Topology
open Filter

universe u
variable {X : Type u}

noncomputable def quadratic (K : X → X → ℂ) {n : ℕ}
    (z : Fin n → X) (c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (c i) * K (z i) (z j) * c j

structure PositiveKernel (K : X → X → ℂ) : Prop where
  hermitian : ∀ z w, K z w = star (K w z)
  nonneg : ∀ (n : ℕ) (z : Fin n → X) (c : Fin n → ℂ),
    0 ≤ (quadratic K z c).re

lemma positive_diagonal {K : X → X → ℂ} (hK : PositiveKernel K) (z : X) :
    0 ≤ (K z z).re := by
  simpa [quadratic] using hK.nonneg 1 (fun _ => z) (fun _ => 1)

lemma gram_positive {d : ℕ} (u : X → EuclideanSpace ℂ (Fin d)) :
    PositiveKernel (fun z w => inner ℂ (u w) (u z)) := by
  constructor
  · intro z w
    exact (inner_conj_symm (u w) (u z)).symm
  · intro n z c
    let v : EuclideanSpace ℂ (Fin d) := ∑ i, star (c i) • u (z i)
    have hq :
        quadratic (fun z w => inner ℂ (u w) (u z)) z c = inner ℂ v v := by
      rw [quadratic, Finset.sum_comm]
      simp only [v, sum_inner]
      simp only [inner_sum]
      simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hq]
    have hn : (inner ℂ v v).re = ‖v‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    rw [hn]
    exact sq_nonneg _

lemma positive_limit {I : Type*} {l : Filter I} [NeBot l]
    (F : I → X → X → ℂ) (K : X → X → ℂ)
    (hF : ∀ i, PositiveKernel (F i))
    (hlim : ∀ z w, Tendsto (fun i => F i z w) l (𝓝 (K z w))) :
    PositiveKernel K := by
  constructor
  · intro z w
    have hz := hlim z w
    have he : (fun i => F i z w) = (fun i => star (F i w z)) :=
      funext (fun i => (hF i).hermitian z w)
    rw [he] at hz
    exact tendsto_nhds_unique hz (hlim w z).star
  · intro n z c
    have hq : Tendsto (fun i => quadratic (F i) z c) l
        (𝓝 (quadratic K z c)) := by
      unfold quadratic
      apply tendsto_finset_sum
      intro a _
      apply tendsto_finset_sum
      intro b _
      exact (tendsto_const_nhds.mul (hlim (z a) (z b))).mul tendsto_const_nhds
    have hr : Tendsto (fun i => (quadratic (F i) z c).re) l
        (𝓝 (quadratic K z c).re) :=
      (Complex.continuous_re.tendsto _).comp hq
    exact ge_of_tendsto' hr (fun i => (hF i).nonneg n z c)

noncomputable def schur (K : X → X → ℂ) (o : X) (z w : X) : ℂ :=
  K z w - K z o * K o w / K o o

noncomputable def rowSum (K : X → X → ℂ) (o : X) {n : ℕ}
    (z : Fin n → X) (c : Fin n → ℂ) : ℂ :=
  ∑ i, K o (z i) * c i

lemma column_eq_star_row {K : X → X → ℂ} (hK : PositiveKernel K)
    (o : X) {n : ℕ} (z : Fin n → X) (c : Fin n → ℂ) :
    (∑ i, star (c i) * K (z i) o) = star (rowSum K o z c) := by
  rw [rowSum, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul, ← hK.hermitian (z i) o]

lemma quadratic_schur (K : X → X → ℂ) (o : X) {n : ℕ}
    (z : Fin n → X) (c : Fin n → ℂ) :
    quadratic (schur K o) z c =
      quadratic K z c -
        (∑ i, star (c i) * K (z i) o) * rowSum K o z c / K o o := by
  unfold quadratic schur rowSum
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_mul_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_cons (K : X → X → ℂ) (o : X) {n : ℕ}
    (z : Fin n → X) (c : Fin n → ℂ) (t : ℂ) :
    quadratic K (Fin.cons o z) (Fin.cons t c) =
      star t * K o o * t + star t * rowSum K o z c +
        (∑ i, star (c i) * K (z i) o) * t + quadratic K z c := by
  simp only [quadratic, rowSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  ring

lemma schur_positive {K : X → X → ℂ} (hK : PositiveKernel K)
    (o : X) (hd : K o o ≠ 0) : PositiveKernel (schur K o) := by
  have hs : star (K o o) = K o o := (hK.hermitian o o).symm
  constructor
  · intro z w
    simp only [schur, star_sub, star_div₀, star_mul, hs,
      ← hK.hermitian z w, ← hK.hermitian z o, ← hK.hermitian o w]
  · intro n z c
    have he :
        quadratic (schur K o) z c =
        quadratic K (Fin.cons o z) (Fin.cons (-rowSum K o z c / K o o) c) := by
      rw [quadratic_schur, quadratic_cons]
      simp only [column_eq_star_row hK, star_div₀, star_neg, hs]
      field_simp [hd] ; ring
    rw [he]
    exact hK.nonneg (n + 1) _ _

lemma schur_base_row (K : X → X → ℂ) (o z : X) (hd : K o o ≠ 0) :
    schur K o o z = 0 := by
  unfold schur
  field_simp [hd]

lemma schur_base_column (K : X → X → ℂ) (o z : X) (hd : K o o ≠ 0) :
    schur K o z o = 0 := by
  unfold schur
  field_simp [hd]

lemma nonzero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h
  simp [h] at hz

lemma schur_based {K : X → X → ℂ} (hK : PositiveKernel K)
    (o : X) (ho : 0 < (K o o).re) :
    PositiveKernel (schur K o) ∧
      (∀ z, schur K o o z = 0) ∧ (∀ z, schur K o z o = 0) :=
  ⟨schur_positive hK o (nonzero_of_re_pos ho),
    fun z => schur_base_row K o z (nonzero_of_re_pos ho),
    fun z => schur_base_column K o z (nonzero_of_re_pos ho)⟩

abbrev Upper := {z : ℂ // 0 < z.im}

noncomputable def pick (f : ℂ → ℂ) (z w : Upper) : ℂ :=
  (f z.1 - star (f w.1)) / (z.1 - star w.1)

@[simp] lemma star_real (a : ℝ) : star (a : ℂ) = (a : ℂ) := by
  simp

lemma upper_denominator_ne (z w : Upper) : z.1 - star w.1 ≠ 0 := by
  intro h
  have hi : z.1.im + w.1.im = 0 := by
    simpa [Complex.star_def] using congrArg Complex.im h
  linarith [z.2, w.2]

lemma real_sub_ne (a : ℝ) (z : ℂ) (hz : 0 < z.im) :
    (a : ℂ) - z ≠ 0 := by
  intro h
  have hi : -z.im = 0 := by simpa using congrArg Complex.im h
  linarith

lemma real_sub_star_ne (a : ℝ) (z : Upper) :
    (a : ℂ) - star z.1 ≠ 0 := by
  intro h
  apply real_sub_ne a z.1 z.2
  simpa only [star_sub, star_star, star_real, star_zero] using
    congrArg (fun t : ℂ => star t) h

lemma sub_star (z : ℂ) : z - star z = 2 * (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] ; ring

lemma pick_diagonal (f : ℂ → ℂ) (z : Upper) :
    pick f z z = (((f z.1).im / z.1.im : ℝ) : ℂ) := by
  have hz : (z.1.im : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt z.2)
  rw [pick, sub_star, sub_star, Complex.ofReal_div]
  field_simp [hz, Complex.I_ne_zero] ; ring

lemma pick_hermitian (f : ℂ → ℂ) (z w : Upper) :
    pick f z w = star (pick f w z) := by
  simp only [pick, star_div₀, star_sub, star_star]
  have hn : star (f w.1) - f z.1 = -(f z.1 - star (f w.1)) := by ring
  have hd : star w.1 - z.1 = -(z.1 - star w.1) := by ring
  rw [hn, hd, neg_div_neg_eq]

lemma sign_of_positive (f : ℂ → ℂ) (hf : PositiveKernel (pick f))
    (z : Upper) : 0 ≤ (f z.1).im := by
  have hd : 0 ≤ (f z.1).im / z.1.im := by
    simpa only [pick_diagonal, Complex.ofReal_re] using positive_diagonal hf z
  calc
    0 ≤ ((f z.1).im / z.1.im) * z.1.im := mul_nonneg hd z.2.le
    _ = (f z.1).im := div_mul_cancel₀ _ (ne_of_gt z.2)

lemma pick_limit {I : Type*} {l : Filter I} [NeBot l]
    (F : I → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ i, PositiveKernel (pick (F i)))
    (hlim : ∀ z : Upper, Tendsto (fun i => F i z.1) l (𝓝 (f z.1))) :
    PositiveKernel (pick f) := by
  apply positive_limit (l := l) (fun i => pick (F i)) (pick f) hF
  intro z w
  exact ((hlim z).sub (hlim w).star).div_const (z.1 - star w.1)

noncomputable def stieltjes {d : ℕ} (x w : Fin d → ℝ) (z : ℂ) : ℂ :=
  ∑ k, (w k : ℂ) / ((x k : ℂ) - z)

lemma stieltjes_holomorphic {d : ℕ} (x w : Fin d → ℝ) :
    DifferentiableOn ℂ (stieltjes x w) {z : ℂ | 0 < z.im} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold stieltjes
  apply DifferentiableAt.fun_sum
  intro k _
  exact (differentiableAt_const (w k : ℂ)).div
    ((differentiableAt_const (x k : ℂ)).sub differentiableAt_id)
    (real_sub_ne (x k) z hz)

lemma star_stieltjes {d : ℕ} (x w : Fin d → ℝ) (z : ℂ) :
    star (stieltjes x w z) = ∑ k, (w k : ℂ) / ((x k : ℂ) - star z) := by
  simp only [stieltjes, star_sum, star_div₀, star_sub, star_real]

lemma single_pick_identity (a r : ℝ) (z w : Upper) :
    ((r : ℂ) / ((a : ℂ) - z.1) -
        (r : ℂ) / ((a : ℂ) - star w.1)) / (z.1 - star w.1) =
      (r : ℂ) / (((a : ℂ) - z.1) * ((a : ℂ) - star w.1)) := by
  rw [div_sub_div (r : ℂ) (r : ℂ)
    (real_sub_ne a z.1 z.2) (real_sub_star_ne a w), div_div]
  have hnum :
      (r : ℂ) * ((a : ℂ) - star w.1) -
          ((a : ℂ) - z.1) * (r : ℂ) =
        (r : ℂ) * (z.1 - star w.1) := by
    ring
  rw [hnum]
  exact mul_div_mul_right (r : ℂ)
    (((a : ℂ) - z.1) * ((a : ℂ) - star w.1))
    (upper_denominator_ne z w)

lemma stieltjes_pick_formula {d : ℕ} (x w : Fin d → ℝ) (z t : Upper) :
    pick (stieltjes x w) z t =
      ∑ k, (w k : ℂ) / (((x k : ℂ) - z.1) * ((x k : ℂ) - star t.1)) := by
  rw [pick, star_stieltjes]
  change ((∑ k, (w k : ℂ) / ((x k : ℂ) - z.1)) -
    ∑ k, (w k : ℂ) / ((x k : ℂ) - star t.1)) /
      (z.1 - star t.1) = _
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ k, ((w k : ℂ) / ((x k : ℂ) - z.1) -
        (w k : ℂ) / ((x k : ℂ) - star t.1)) / (z.1 - star t.1) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact single_pick_identity (x k) (w k) z t

noncomputable def feature {d : ℕ} (x w : Fin d → ℝ) (z : Upper) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun k => (Real.sqrt (w k) : ℂ) / ((x k : ℂ) - z.1))

lemma stieltjes_gram {d : ℕ} (x w : Fin d → ℝ)
    (hw : ∀ k, 0 ≤ w k) (z t : Upper) :
    pick (stieltjes x w) z t = inner ℂ (feature x w t) (feature x w z) := by
  rw [stieltjes_pick_formula, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  change (w k : ℂ) / (((x k : ℂ) - z.1) * ((x k : ℂ) - star t.1)) =
    inner ℂ ((Real.sqrt (w k) : ℂ) / ((x k : ℂ) - t.1))
      ((Real.sqrt (w k) : ℂ) / ((x k : ℂ) - z.1))
  rw [RCLike.inner_apply']
  simp only [starRingEnd_apply, star_div₀, star_sub, star_real]
  have hs : (Real.sqrt (w k) : ℂ) ^ 2 = (w k : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (hw k))
  rw [div_mul_div_comm, ← pow_two, hs]
  congr 1
  ring

lemma stieltjes_positive {d : ℕ} (x w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    PositiveKernel (pick (stieltjes x w)) := by
  have he : pick (stieltjes x w) =
      (fun z t => inner ℂ (feature x w t) (feature x w z)) := by
    funext z t
    exact stieltjes_gram x w hw z t
  rw [he]
  exact gram_positive (feature x w)

lemma stieltjes_sign {d : ℕ} (x w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k)
    (z : Upper) : 0 ≤ (stieltjes x w z.1).im :=
  sign_of_positive _ (stieltjes_positive x w hw) z

lemma stieltjes_limit_positive {I : Type*} {l : Filter I} [NeBot l]
    (d : I → ℕ) (x w : (i : I) → Fin (d i) → ℝ) (f : ℂ → ℂ)
    (hw : ∀ i k, 0 ≤ w i k)
    (hlim : ∀ z : Upper,
      Tendsto (fun i => stieltjes (x i) (w i) z.1) l (𝓝 (f z.1))) :
    PositiveKernel (pick f) :=
  pick_limit (fun i => stieltjes (x i) (w i)) f
    (fun i => stieltjes_positive (x i) (w i) (hw i)) hlim

def StieltjesApproximable (f : ℂ → ℂ) : Prop :=
  ∃ (d : ℕ → ℕ) (x w : (i : ℕ) → Fin (d i) → ℝ),
    (∀ i k, 0 ≤ w i k) ∧
      ∀ z : Upper,
        Tendsto (fun i => stieltjes (x i) (w i) z.1) atTop (𝓝 (f z.1))

lemma finite_approximable {d : ℕ} (x w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    StieltjesApproximable (stieltjes x w) :=
  ⟨(fun _ => d), (fun _ => x), (fun _ => w), (fun _ => hw),
    (fun _ => tendsto_const_nhds)⟩

lemma approximable_positive (f : ℂ → ℂ) (hf : StieltjesApproximable f) :
    PositiveKernel (pick f) := by
  rcases hf with ⟨d, x, w, hw, hlim⟩
  exact stieltjes_limit_positive d x w f hw hlim

theorem finite_stieltjes_pick_kernel {d : ℕ} (x w : Fin d → ℝ)
    (hw : ∀ k, 0 ≤ w k) :
    DifferentiableOn ℂ (stieltjes x w) {z : ℂ | 0 < z.im} ∧
      PositiveKernel (pick (stieltjes x w)) ∧
      (∀ z t : Upper,
        pick (stieltjes x w) z t =
          ∑ k, (w k : ℂ) /
            (((x k : ℂ) - z.1) * ((x k : ℂ) - star t.1))) ∧
      (∀ z t : Upper,
        pick (stieltjes x w) z t =
          inner ℂ (feature x w t) (feature x w z)) :=
  ⟨stieltjes_holomorphic x w, stieltjes_positive x w hw,
    stieltjes_pick_formula x w, stieltjes_gram x w hw⟩

end PickKernel

open PickKernel in
theorem pick_kernel (f : ℂ → ℂ) (hf : StieltjesApproximable f) :
    (∀ z : Upper, 0 ≤ (f z.1).im) ∧
    ((∀ z : Upper, 0 ≤ (f z.1).im) ↔ PositiveKernel (pick f)) ∧
    (∀ z : Upper, pick f z z = (((f z.1).im / z.1.im : ℝ) : ℂ)) ∧
    (∀ o : Upper, 0 < (pick f o o).re →
      PositiveKernel (schur (pick f) o) ∧
        (∀ z, schur (pick f) o o z = 0) ∧
        (∀ z, schur (pick f) o z o = 0)) := by
  have hK := approximable_positive f hf
  exact ⟨sign_of_positive f hK,
    ⟨fun _ => hK, sign_of_positive f⟩,
    pick_diagonal f, fun o ho => schur_based hK o ho⟩

end OperatorKO7.Meta.LiteratureReview
