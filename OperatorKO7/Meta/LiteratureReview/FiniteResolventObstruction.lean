import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
Proposition prop:finite-resolvent-obstruction states that a finite Hermitian
matrix has a scalar resolvent holomorphic with nonnegative imaginary part and
a reciprocal-height lower bound at every spectral atom, so a nonzero vector
and a positive scalar preclude boundedness on every vertical unit segment.
-/

open scoped BigOperators

namespace FiniteResolvent

open Matrix

noncomputable local instance : DecidableEq ℝ := Classical.decEq ℝ

abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

variable {n : ℕ}

noncomputable def act (A : Mat n) (v : V n) : V n :=
  WithLp.toLp 2 (A *ᵥ (fun i => v i))

lemma act_mul (A B : Mat n) (v : V n) :
    act (A * B) v = act A (act B v) := by
  ext i
  change ((A * B) *ᵥ (fun j => v j)) i =
    (A *ᵥ (B *ᵥ (fun j => v j))) i
  rw [Matrix.mulVec_mulVec]

lemma act_one (v : V n) : act (1 : Mat n) v = v := by
  ext i
  change ((1 : Mat n) *ᵥ (fun j => v j)) i = v i
  rw [Matrix.one_mulVec]

lemma act_zero (A : Mat n) : act A (0 : V n) = 0 := by
  ext i
  change (A *ᵥ (0 : Fin n → ℂ)) i = 0
  rw [Matrix.mulVec_zero]
  rfl

lemma act_smul (A : Mat n) (c : ℂ) (v : V n) :
    act A (c • v) = c • act A v := by
  ext i
  change (A *ᵥ (c • (fun j => v j))) i =
    (c • (A *ᵥ (fun j => v j))) i
  rw [Matrix.mulVec_smul]

lemma act_diagonal_apply (a : Fin n → ℂ) (v : V n) (i : Fin n) :
    act (Matrix.diagonal a) v i = a i * v i := by
  exact Matrix.mulVec_diagonal a (fun j => v j) i

lemma inner_act (A : Mat n) (v w : V n) :
    inner ℂ (act A v) w = inner ℂ v (act (star A) w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (fun i => w i) ⬝ᵥ star (A *ᵥ (fun i => v i)) =
    (star A *ᵥ (fun i => w i)) ⬝ᵥ star (fun i => v i)
  rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
  calc
    _ = (star (fun i => v i) ᵥ* Aᴴ) ⬝ᵥ (fun i => w i) :=
      dotProduct_comm _ _
    _ = star (fun i => v i) ⬝ᵥ (Aᴴ *ᵥ (fun i => w i)) :=
      (Matrix.dotProduct_mulVec _ _ _).symm
    _ = _ := dotProduct_comm _ _

lemma inner_unitary (U : Matrix.unitaryGroup (Fin n) ℂ) (v w : V n) :
    inner ℂ (act (U : Mat n) v) (act (U : Mat n) w) = inner ℂ v w := by
  rw [inner_act, ← act_mul, U.2.1, act_one]

lemma norm_sq_unitary (U : Matrix.unitaryGroup (Fin n) ℂ) (v : V n) :
    ‖act (U : Mat n) v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_unitary]

noncomputable def conjugateDiagonal (U : Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n → ℂ) : Mat n :=
  (U : Mat n) * Matrix.diagonal a * star (U : Mat n)

lemma conjugateDiagonal_mul (U : Matrix.unitaryGroup (Fin n) ℂ)
    (a b : Fin n → ℂ) :
    conjugateDiagonal U a * conjugateDiagonal U b =
      conjugateDiagonal U (fun i => a i * b i) := by
  unfold conjugateDiagonal
  calc
    _ = (U : Mat n) * Matrix.diagonal a *
        (star (U : Mat n) * (U : Mat n)) *
        Matrix.diagonal b * star (U : Mat n) := by
      simp only [mul_assoc]
    _ = (U : Mat n) * (Matrix.diagonal a * Matrix.diagonal b) *
        star (U : Mat n) := by
      rw [U.2.1]
      simp only [mul_one, mul_assoc]
    _ = _ := by rw [Matrix.diagonal_mul_diagonal]

lemma conjugateDiagonal_sub (U : Matrix.unitaryGroup (Fin n) ℂ)
    (a b : Fin n → ℂ) :
    conjugateDiagonal U (fun i => a i - b i) =
      conjugateDiagonal U a - conjugateDiagonal U b := by
  unfold conjugateDiagonal
  rw [← Matrix.diagonal_sub, mul_sub, sub_mul]

lemma conjugateDiagonal_const (U : Matrix.unitaryGroup (Fin n) ℂ) (z : ℂ) :
    conjugateDiagonal U (fun _ => z) = z • (1 : Mat n) := by
  have hd : Matrix.diagonal (fun _ : Fin n => z) = z • (1 : Mat n) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  unfold conjugateDiagonal
  rw [hd, Matrix.mul_smul, mul_one, Matrix.smul_mul, U.2.2]

def upper : Set ℂ := {z | 0 < z.im}

noncomputable def vertical (x ε : ℝ) : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I

@[simp] lemma vertical_re (x ε : ℝ) : (vertical x ε).re = x := by
  simp [vertical]

@[simp] lemma vertical_im (x ε : ℝ) : (vertical x ε).im = ε := by
  simp [vertical]

lemma denominator_ne_zero (a : ℝ) (z : ℂ) (hz : 0 < z.im) :
    (a : ℂ) - z ≠ 0 := by
  intro h
  have hi : -z.im = 0 := by simpa using congrArg Complex.im h
  linarith

variable {H : Mat n}

lemma shift_eq (hH : H.IsHermitian) (z : ℂ) :
    H - z • 1 = conjugateDiagonal hH.eigenvectorUnitary
      (fun i => (hH.eigenvalues i : ℂ) - z) := by
  have hs : H = conjugateDiagonal hH.eigenvectorUnitary
      (fun i => (hH.eigenvalues i : ℂ)) := hH.spectral_theorem
  calc
    H - z • 1 = conjugateDiagonal hH.eigenvectorUnitary
        (fun i => (hH.eigenvalues i : ℂ)) - z • 1 :=
      congrArg (fun A : Mat n => A - z • 1) hs
    _ = _ := by rw [conjugateDiagonal_sub, conjugateDiagonal_const]

lemma resolvent_inverse (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (H - z • 1)⁻¹ = conjugateDiagonal hH.eigenvectorUnitary
      (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [shift_eq hH z, conjugateDiagonal_mul]
  have hid :
      (fun i => ((hH.eigenvalues i : ℂ) - z) *
        ((hH.eigenvalues i : ℂ) - z)⁻¹) =
      (fun _ : Fin n => (1 : ℂ)) := by
    funext i
    exact mul_inv_cancel₀ (denominator_ne_zero _ z hz)
  rw [hid]
  simpa using conjugateDiagonal_const hH.eigenvectorUnitary (1 : ℂ)

noncomputable def coordinates (hH : H.IsHermitian) (v : V n) : V n :=
  act (star (hH.eigenvectorUnitary : Mat n)) v

lemma recover (hH : H.IsHermitian) (v : V n) :
    act (hH.eigenvectorUnitary : Mat n) (coordinates hH v) = v := by
  unfold coordinates
  rw [← act_mul, hH.eigenvectorUnitary.2.2, act_one]

lemma coordinates_decode (hH : H.IsHermitian) (v : V n) :
    coordinates hH (act (hH.eigenvectorUnitary : Mat n) v) = v := by
  unfold coordinates
  rw [← act_mul, hH.eigenvectorUnitary.2.1, act_one]

lemma coordinates_injective (hH : H.IsHermitian) :
    Function.Injective (coordinates hH) := by
  intro v w h
  calc
    v = act (hH.eigenvectorUnitary : Mat n) (coordinates hH v) :=
      (recover hH v).symm
    _ = act (hH.eigenvectorUnitary : Mat n) (coordinates hH w) :=
      congrArg _ h
    _ = w := recover hH w

lemma coordinates_zero (hH : H.IsHermitian) :
    coordinates hH (0 : V n) = 0 :=
  act_zero _

lemma coordinates_smul (hH : H.IsHermitian) (c : ℂ) (v : V n) :
    coordinates hH (c • v) = c • coordinates hH v :=
  act_smul _ c v

lemma coordinates_action (hH : H.IsHermitian) (v : V n) (i : Fin n) :
    coordinates hH (act H v) i =
      (hH.eigenvalues i : ℂ) * coordinates hH v i := by
  have hd :
      star (hH.eigenvectorUnitary : Mat n) * H *
        (hH.eigenvectorUnitary : Mat n) =
      Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) :=
    hH.star_mul_self_mul_eq_diagonal
  have hv : coordinates hH (act H v) =
      act (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)))
        (coordinates hH v) := by
    calc
      _ = act (star (hH.eigenvectorUnitary : Mat n))
          (act H (act (hH.eigenvectorUnitary : Mat n) (coordinates hH v))) := by
        rw [recover, coordinates]
      _ = act (star (hH.eigenvectorUnitary : Mat n) * H *
          (hH.eigenvectorUnitary : Mat n)) (coordinates hH v) := by
        simp only [act_mul]
      _ = _ := by rw [hd]
  rw [hv, act_diagonal_apply]

lemma inner_coordinates (hH : H.IsHermitian) (v w : V n) :
    inner ℂ (coordinates hH v) (coordinates hH w) = inner ℂ v w := by
  calc
    _ = inner ℂ
        (act (hH.eigenvectorUnitary : Mat n) (coordinates hH v))
        (act (hH.eigenvectorUnitary : Mat n) (coordinates hH w)) :=
      (inner_unitary hH.eigenvectorUnitary _ _).symm
    _ = _ := by rw [recover, recover]

noncomputable def spectralProjection (hH : H.IsHermitian) (x : ℝ) (v : V n) : V n := by
  classical
  exact act (hH.eigenvectorUnitary : Mat n)
    (WithLp.toLp 2 (fun i => if hH.eigenvalues i = x then coordinates hH v i else 0))

lemma projection_coordinates (hH : H.IsHermitian) (x : ℝ) (v : V n) (i : Fin n) :
    coordinates hH (spectralProjection hH x v) i =
      if hH.eigenvalues i = x then coordinates hH v i else 0 := by
  classical
  unfold spectralProjection
  rw [coordinates_decode]
  rfl

lemma projection_eigen (hH : H.IsHermitian) (x : ℝ) (v : V n) :
    act H (spectralProjection hH x v) =
      (x : ℂ) • spectralProjection hH x v := by
  classical
  apply coordinates_injective hH
  ext i
  rw [coordinates_action, coordinates_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, projection_coordinates]
  by_cases hi : hH.eigenvalues i = x <;> simp [hi]

lemma projection_fixed_of_eigen (hH : H.IsHermitian) (x : ℝ) (v : V n)
    (hv : act H v = (x : ℂ) • v) :
    spectralProjection hH x v = v := by
  classical
  apply coordinates_injective hH
  ext i
  rw [projection_coordinates]
  by_cases hi : hH.eigenvalues i = x
  · simp [hi]
  · simp only [hi, if_false]
    have he : coordinates hH (act H v) i =
        coordinates hH ((x : ℂ) • v) i :=
      congrArg (fun u : V n => coordinates hH u i) hv
    rw [coordinates_action, coordinates_smul] at he
    change (hH.eigenvalues i : ℂ) * coordinates hH v i =
      (x : ℂ) * coordinates hH v i at he
    have hm : ((hH.eigenvalues i : ℂ) - (x : ℂ)) * coordinates hH v i = 0 := by
      rw [sub_mul, he, sub_self]
    have hd : (hH.eigenvalues i : ℂ) - (x : ℂ) ≠ 0 := by
      intro hz
      apply hi
      simpa using congrArg Complex.re (sub_eq_zero.mp hz)
    exact ((mul_eq_zero.mp hm).resolve_left hd).symm

lemma projection_idempotent (hH : H.IsHermitian) (x : ℝ) (v : V n) :
    spectralProjection hH x (spectralProjection hH x v) =
      spectralProjection hH x v :=
  projection_fixed_of_eigen hH x _ (projection_eigen hH x v)

lemma projection_selfadjoint (hH : H.IsHermitian) (x : ℝ) (v w : V n) :
    inner ℂ (spectralProjection hH x v) w =
      inner ℂ v (spectralProjection hH x w) := by
  classical
  calc
    _ = inner ℂ (coordinates hH (spectralProjection hH x v))
        (coordinates hH w) := (inner_coordinates hH _ _).symm
    _ = inner ℂ (coordinates hH v)
        (coordinates hH (spectralProjection hH x w)) := by
      rw [PiLp.inner_apply, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [projection_coordinates, projection_coordinates]
      by_cases hx : hH.eigenvalues i = x <;> simp [hx]
    _ = _ := inner_coordinates hH _ _

noncomputable def weight (hH : H.IsHermitian) (v : V n) (i : Fin n) : ℝ :=
  ‖coordinates hH v i‖ ^ 2

noncomputable def atomWeight (hH : H.IsHermitian) (v : V n) (x : ℝ) : ℝ :=
  ‖spectralProjection hH x v‖ ^ 2

lemma weight_nonneg (hH : H.IsHermitian) (v : V n) (i : Fin n) :
    0 ≤ weight hH v i :=
  sq_nonneg _

lemma atomWeight_eq_sum (hH : H.IsHermitian) (v : V n) (x : ℝ) :
    atomWeight hH v x =
      ∑ i, if hH.eigenvalues i = x then weight hH v i else 0 := by
  classical
  unfold atomWeight spectralProjection
  rw [norm_sq_unitary, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  change ‖if hH.eigenvalues i = x then coordinates hH v i else (0 : ℂ)‖ ^ 2 =
    if hH.eigenvalues i = x then weight hH v i else 0
  by_cases hx : hH.eigenvalues i = x <;> simp [hx, weight]

lemma exists_positive_atom (hH : H.IsHermitian) (v : V n) (hv : v ≠ 0) :
    ∃ x : ℝ, x ∈ spectrum ℝ H ∧ 0 < atomWeight hH v x := by
  classical
  have hq : coordinates hH v ≠ 0 := by
    intro h
    apply hv
    apply coordinates_injective hH
    exact h.trans (coordinates_zero hH).symm
  obtain ⟨i, hi⟩ : ∃ i, coordinates hH v i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hq
    ext i
    exact h i
  have hw : 0 < weight hH v i :=
    sq_pos_of_pos (norm_pos_iff.mpr hi)
  apply Exists.intro (hH.eigenvalues i)
  apply And.intro (hH.eigenvalues_mem_spectrum_real i)
  rw [atomWeight_eq_sum]
  have hle :
      (if hH.eigenvalues i = hH.eigenvalues i then weight hH v i else 0) ≤
      ∑ j, if hH.eigenvalues j = hH.eigenvalues i then weight hH v j else 0 := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n =>
        if hH.eigenvalues j = hH.eigenvalues i then weight hH v j else 0)
      (a := i)
    · intro j _
      dsimp only
      split_ifs
      · exact weight_nonneg hH v j
      · exact le_rfl
    · exact Finset.mem_univ i
  exact hw.trans_le (by simpa using hle)

lemma inner_diagonal (a : Fin n → ℂ) (v : V n) :
    inner ℂ v (act (Matrix.diagonal a) v) =
      ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ) * a i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [act_diagonal_apply, RCLike.inner_apply']
  have hn : star (v i) * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [RCLike.inner_apply', Complex.ofReal_pow] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (v i))
  change star (v i) * (a i * v i) = _
  calc
    _ = (star (v i) * v i) * a i := by ring
    _ = _ := by rw [hn]

noncomputable def resolventScalar (H : Mat n) (v : V n) (z : ℂ) : ℂ :=
  inner ℂ v (act ((H - z • 1)⁻¹) v)

noncomputable def stieltjes (eigs w : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑ i, (w i : ℂ) / ((eigs i : ℂ) - z)

lemma resolvent_eq_stieltjes (hH : H.IsHermitian) (v : V n)
    (z : ℂ) (hz : 0 < z.im) :
    resolventScalar H v z = stieltjes hH.eigenvalues (weight hH v) z := by
  rw [resolventScalar, resolvent_inverse hH z hz]
  unfold conjugateDiagonal
  rw [act_mul, act_mul]
  change inner ℂ v
      (act (hH.eigenvectorUnitary : Mat n)
        (act (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹))
          (coordinates hH v))) = _
  calc
    _ = inner ℂ
        (act (hH.eigenvectorUnitary : Mat n) (coordinates hH v))
        (act (hH.eigenvectorUnitary : Mat n)
          (act (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹))
            (coordinates hH v))) := by rw [recover]
    _ = inner ℂ (coordinates hH v)
        (act (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹))
          (coordinates hH v)) := inner_unitary _ _ _
    _ = _ := by
      simpa only [stieltjes, weight, div_eq_mul_inv] using
        inner_diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹)
          (coordinates hH v)

lemma summand_im (a w : ℝ) (z : ℂ) :
    ((w : ℂ) / ((a : ℂ) - z)).im =
      w * z.im / ((a - z.re) ^ 2 + z.im ^ 2) := by
  have hd : Complex.normSq ((a : ℂ) - z) =
      (a - z.re) ^ 2 + z.im ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.div_im, hd]
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im,
    zero_sub, zero_mul, zero_div]
  ring

lemma summand_im_nonneg (a w : ℝ) (hw : 0 ≤ w)
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ ((w : ℂ) / ((a : ℂ) - z)).im := by
  rw [summand_im]
  exact div_nonneg (mul_nonneg hw hz.le)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma summand_at_pole (x w ε : ℝ) (hε : 0 < ε) :
    ((w : ℂ) / ((x : ℂ) - vertical x ε)).im = w / ε := by
  rw [summand_im, vertical_re, vertical_im]
  simp only [sub_self]
  field_simp [ne_of_gt hε] ; ring

lemma stieltjes_holomorphic (eigs w : Fin n → ℝ) :
    DifferentiableOn ℂ (stieltjes eigs w) upper := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold stieltjes
  apply DifferentiableAt.fun_sum
  intro i hi
  exact (differentiableAt_const (w i : ℂ)).div
    ((differentiableAt_const (eigs i : ℂ)).sub differentiableAt_id)
    (denominator_ne_zero (eigs i) z hz)

lemma stieltjes_im_nonneg (eigs w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (stieltjes eigs w z).im := by
  rw [stieltjes, Complex.im_sum]
  exact Finset.sum_nonneg (fun i _ => summand_im_nonneg (eigs i) (w i) (hw i) z hz)

lemma stieltjes_atom_lower_bound (eigs w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x ε : ℝ) (hε : 0 < ε) :
    (∑ i, if eigs i = x then w i else 0) / ε ≤
      (stieltjes eigs w (vertical x ε)).im := by
  classical
  calc
    _ = ∑ i, (if eigs i = x then w i else 0) / ε := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ _ := by
      rw [stieltjes, Complex.im_sum]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hx : eigs i = x
      · simp [hx, summand_at_pole x (w i) ε hε]
      · simp only [hx, if_false, zero_div]
        exact summand_im_nonneg (eigs i) (w i) (hw i)
          (vertical x ε) (by simpa using hε)

lemma resolvent_holomorphic (hH : H.IsHermitian) (v : V n) :
    DifferentiableOn ℂ (resolventScalar H v) upper :=
  (stieltjes_holomorphic hH.eigenvalues (weight hH v)).congr
    (fun z hz => resolvent_eq_stieltjes hH v z hz)

lemma resolvent_im_nonneg (hH : H.IsHermitian) (v : V n)
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (resolventScalar H v z).im := by
  rw [resolvent_eq_stieltjes hH v z hz]
  exact stieltjes_im_nonneg _ _ (weight_nonneg hH v) z hz

lemma resolvent_atom_lower_bound (hH : H.IsHermitian) (v : V n)
    (x ε : ℝ) (hε : 0 < ε) :
    atomWeight hH v x / ε ≤ (resolventScalar H v (vertical x ε)).im := by
  rw [resolvent_eq_stieltjes hH v (vertical x ε) (by simpa using hε),
    atomWeight_eq_sum]
  exact stieltjes_atom_lower_bound _ _ (weight_nonneg hH v) x ε hε

def VerticallyBounded (f : ℂ → ℂ) : Prop :=
  ∀ x : ℝ, ∃ M : ℝ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 → ‖f (vertical x ε)‖ ≤ M

lemma pole_precludes_bound (a M : ℝ) (ha : 0 < a)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → a / ε ≤ M) : False := by
  have haM : a ≤ M := by simpa using h 1 zero_lt_one le_rfl
  have hM : 0 ≤ M := ha.le.trans haM
  let ε : ℝ := min 1 (a / (M + 1))
  have hden : 0 < M + 1 := by linarith
  have hε : 0 < ε := lt_min zero_lt_one (div_pos ha hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεa : ε ≤ a / (M + 1) := min_le_right _ _
  have hlow : ε * (M + 1) ≤ a := (le_div_iff₀ hden).mp hεa
  have hupp : a ≤ M * ε := (div_le_iff₀ hε).mp (h ε hε hε1)
  nlinarith

lemma no_bounded_representation (hH : H.IsHermitian) (v : V n) (hv : v ≠ 0)
    (f : ℂ → ℂ) (hf : VerticallyBounded f) (c : ℝ) (hc : 0 < c) :
    ¬ (∀ z : ℂ, 0 < z.im → f z = (c : ℂ) * resolventScalar H v z) := by
  intro heq
  obtain ⟨x, hxspec, hx⟩ := exists_positive_atom hH v hv
  obtain ⟨M, hM⟩ := hf x
  apply pole_precludes_bound (c * atomWeight hH v x) M (mul_pos hc hx)
  intro ε hε hε1
  have hz : 0 < (vertical x ε).im := by simpa using hε
  calc
    (c * atomWeight hH v x) / ε = c * (atomWeight hH v x / ε) := by ring
    _ ≤ c * (resolventScalar H v (vertical x ε)).im :=
      mul_le_mul_of_nonneg_left (resolvent_atom_lower_bound hH v x ε hε) hc.le
    _ = (f (vertical x ε)).im := by
      rw [heq _ hz]
      simp [Complex.mul_im]
    _ ≤ ‖f (vertical x ε)‖ := Complex.im_le_norm _
    _ ≤ M := hM ε hε hε1

end FiniteResolvent

open FiniteResolvent in
theorem finite_resolvent_obstruction {n : ℕ} {H : Mat n}
    (hH : H.IsHermitian) (v : V n) :
    DifferentiableOn ℂ (resolventScalar H v) upper ∧
    (∀ z : ℂ, 0 < z.im → 0 ≤ (resolventScalar H v z).im) ∧
    (∀ x ε : ℝ, 0 < ε →
      atomWeight hH v x / ε ≤ (resolventScalar H v (vertical x ε)).im) ∧
    (v ≠ 0 → ∀ f : ℂ → ℂ, VerticallyBounded f → ∀ c : ℝ, 0 < c →
      ¬ (∀ z : ℂ, 0 < z.im → f z = (c : ℂ) * resolventScalar H v z)) := by
  apply And.intro (resolvent_holomorphic hH v)
  apply And.intro (resolvent_im_nonneg hH v)
  apply And.intro (resolvent_atom_lower_bound hH v)
  intro hv f hf c hc
  exact no_bounded_representation hH v hv f hf c hc

end OperatorKO7.Meta.LiteratureReview
