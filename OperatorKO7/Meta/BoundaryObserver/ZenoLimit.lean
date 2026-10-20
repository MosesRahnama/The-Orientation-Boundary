import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Repeated record dephasing and the Zeno limit

Manuscript: Theorem `thm:zeno` of the Observation-Boundary Principle.

The dephasing `Δ(A) = ∑ᵣ Pᵣ A Pᵣ` of an observer with orthogonal record projectors `Pᵣ` is a
contraction in the operator norm, by averaging the conjugations by the sign unitaries
`∑ᵣ ±Pᵣ`. For Hermitian `H` with `H_Δ = Δ(H)`, `F_s(A) = e^{-iHs} A e^{iHs}` and
`G_s(A) = e^{-iH_Δ s} A e^{iH_Δ s}`, the difference `Δ(F_s(B)) - G_s(B)` at a block-diagonal `B`
vanishes with its first derivative at `s = 0` and has second derivative of norm at most
`8 ‖H‖² ‖B‖`, so its norm is at most `4 ‖H‖² s² ‖B‖`; a telescoping sum over `N` steps of length
`t / N` gives `‖(Δ ∘ F_{t/N})^N(Δ(A)) - G_t(Δ(A))‖ ≤ 4 ‖H‖² t² ‖A‖ / N`, and the iterates converge
to `G_t(Δ(A))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix.Norms.L2Operator BigOperators
open NormedSpace

namespace OperatorKO7.Meta.BoundaryObserver.ZenoLimit

noncomputable section

variable {n R : Type} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype R] [DecidableEq R]

/-- The dephasing of an observer with record projectors `P`. -/
def deph (P : R → Matrix n n ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ := ∑ r, P r * A * P r

/-- The sign of a Boolean. -/
def sg (b : Bool) : ℂ := if b then 1 else -1

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

/-- `∑_ε sg(ε r) sg(ε s) = 2^{|R|} [r = s]`. -/
theorem sum_sg_mul (r s : R) :
    ∑ ε : R → Bool, sg (ε r) * sg (ε s) = if r = s then (2 : ℂ) ^ Fintype.card R else 0 := by
  by_cases h : r = s
  · subst h
    simp only [sg_mul_self, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, if_true, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · rw [if_neg h]
    let flip : (R → Bool) ≃ (R → Bool) :=
      { toFun := fun ε => Function.update ε r (!ε r)
        invFun := fun ε => Function.update ε r (!ε r)
        left_inv := fun ε => by funext x; by_cases hx : x = r <;> simp [Function.update, hx]
        right_inv := fun ε => by funext x; by_cases hx : x = r <;> simp [Function.update, hx] }
    have hsum : ∑ ε : R → Bool, sg (ε r) * sg (ε s) =
        ∑ ε : R → Bool, sg ((flip ε) r) * sg ((flip ε) s) :=
      (Equiv.sum_comp flip (fun ε => sg (ε r) * sg (ε s))).symm
    have hneg : ∀ ε : R → Bool, sg ((flip ε) r) * sg ((flip ε) s) = -(sg (ε r) * sg (ε s)) := by
      intro ε
      have hs : (flip ε) s = ε s := by simp [flip, Function.update, Ne.symm h]
      have hr : (flip ε) r = !ε r := by simp [flip]
      rw [hs, hr]
      cases ε r <;> cases ε s <;> simp [sg]
    simp only [hneg, Finset.sum_neg_distrib] at hsum
    have : (2 : ℂ) * ∑ ε : R → Bool, sg (ε r) * sg (ε s) = 0 := by linear_combination hsum
    simpa using this

/-- The commutator `[Y, Z] = YZ - ZY`. -/
def ad (Y Z : Matrix n n ℂ) : Matrix n n ℂ := Y * Z - Z * Y

/-- The conjugation flow `e^{uY} B e^{-uY}` at a complex time `u`. -/
def flow (Y : Matrix n n ℂ) (u : ℂ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  exp ℂ (u • Y) * B * exp ℂ (u • -Y)

/-- The generator `-iH` of the evolution `e^{-iHs}`. -/
def gen (H : Matrix n n ℂ) : Matrix n n ℂ := (-Complex.I) • H

theorem flow_zero (Y B : Matrix n n ℂ) : flow Y 0 B = B := by
  simp [flow]

theorem flow_sub (Y : Matrix n n ℂ) (u : ℂ) (a b : Matrix n n ℂ) :
    flow Y u (a - b) = flow Y u a - flow Y u b := by
  simp only [flow, Matrix.mul_sub, Matrix.sub_mul]

theorem flow_flow (Y B : Matrix n n ℂ) (u v : ℂ) : flow Y u (flow Y v B) = flow Y (u + v) B := by
  unfold flow
  have h1 : exp ℂ ((u + v) • Y) = exp ℂ (u • Y) * exp ℂ (v • Y) := by
    rw [add_smul, exp_add_of_commute (((Commute.refl Y).smul_left u).smul_right v)]
  have h2 : exp ℂ ((u + v) • -Y) = exp ℂ (v • -Y) * exp ℂ (u • -Y) := by
    rw [add_comm u v, add_smul, exp_add_of_commute (((Commute.refl (-Y)).smul_left v).smul_right u)]
  rw [h1, h2]
  simp only [Matrix.mul_assoc]

theorem flow_iterate (Y B : Matrix n n ℂ) (s : ℂ) (k : ℕ) :
    (fun C => flow Y s C)^[k] B = flow Y (k * s) B := by
  induction k with
  | zero => simp [flow_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, flow_flow,
      show s + (k : ℂ) * s = ((k + 1 : ℕ) : ℂ) * s by push_cast; ring]

theorem hasDerivAt_flow (Y B : Matrix n n ℂ) (u : ℂ) :
    HasDerivAt (fun v : ℂ => flow Y v B) (ad Y (flow Y u B)) u := by
  have h3 := ((hasDerivAt_exp_smul_const' Y u).mul_const B).fun_mul
    (hasDerivAt_exp_smul_const (-Y) u)
  unfold flow ad
  convert h3 using 1
  noncomm_ring

theorem hasDerivAt_ad {f : ℂ → Matrix n n ℂ} {f' : Matrix n n ℂ} {u : ℂ} (Y : Matrix n n ℂ)
    (h : HasDerivAt f f' u) : HasDerivAt (fun v => ad Y (f v)) (ad Y f') u := by
  unfold ad
  exact (h.const_mul Y).sub (h.mul_const Y)

/-- A complex derivative at a real point restricts to the real derivative. -/
theorem hasDerivAt_real {f : ℂ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ}
    (hf : HasDerivAt f f' (t : ℂ)) : HasDerivAt (fun s : ℝ => f (s : ℂ)) f' t := by
  have hh : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id' (x := t)).ofReal_comp
  simpa using hf.scomp (x := t) hh

theorem norm_ad_le (Y Z : Matrix n n ℂ) : ‖ad Y Z‖ ≤ 2 * ‖Y‖ * ‖Z‖ := by
  unfold ad
  calc ‖Y * Z - Z * Y‖ ≤ ‖Y * Z‖ + ‖Z * Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖ * ‖Z‖ + ‖Z‖ * ‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖Y‖ * ‖Z‖ := by ring

theorem norm_gen (H : Matrix n n ℂ) : ‖gen H‖ = ‖H‖ := by
  rw [gen, norm_smul, norm_neg, Complex.norm_I, one_mul]

theorem gen_mem_skewAdjoint {H : Matrix n n ℂ} (hH : IsSelfAdjoint H) :
    gen H ∈ skewAdjoint (Matrix n n ℂ) := by
  rw [skewAdjoint.mem_iff, gen, star_smul, hH.star_eq]
  have hI : star (-Complex.I) = Complex.I := by
    rw [star_neg, show star Complex.I = -Complex.I from Complex.conj_I, neg_neg]
  rw [hI, neg_smul, neg_neg]

theorem smul_mem_skewAdjoint {X : Matrix n n ℂ} (hX : X ∈ skewAdjoint (Matrix n n ℂ)) (t : ℝ) :
    (t : ℂ) • X ∈ skewAdjoint (Matrix n n ℂ) := by
  rw [skewAdjoint.mem_iff] at hX ⊢
  have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [star_smul, hX, ht, smul_neg]

theorem exp_smul_mem_unitary {X : Matrix n n ℂ} (hX : X ∈ skewAdjoint (Matrix n n ℂ)) (t : ℝ) :
    exp ℂ ((t : ℂ) • X) ∈ unitary (Matrix n n ℂ) :=
  exp_mem_unitary_of_mem_skewAdjoint ℂ (smul_mem_skewAdjoint hX t)

/-- The flow of a skew-adjoint generator at a real time does not increase the norm. -/
theorem norm_flow_le {X : Matrix n n ℂ} (hX : X ∈ skewAdjoint (Matrix n n ℂ)) (t : ℝ)
    (B : Matrix n n ℂ) : ‖flow X (t : ℂ) B‖ ≤ ‖B‖ := by
  have h1 := CStarRing.norm_of_mem_unitary (exp_smul_mem_unitary hX t)
  have h2 := CStarRing.norm_of_mem_unitary (exp_smul_mem_unitary (neg_mem hX) t)
  unfold flow
  calc ‖exp ℂ ((t : ℂ) • X) * B * exp ℂ ((t : ℂ) • -X)‖
      ≤ ‖exp ℂ ((t : ℂ) • X) * B‖ * ‖exp ℂ ((t : ℂ) • -X)‖ := norm_mul_le _ _
    _ ≤ ‖exp ℂ ((t : ℂ) • X)‖ * ‖B‖ * ‖exp ℂ ((t : ℂ) • -X)‖ := by
        gcongr
        exact norm_mul_le _ _
    _ = ‖B‖ := by rw [h1, h2]; ring

/-- The telescoping estimate for iterates of a linear contraction `T` against a map `G` that keeps
a set `S` and does not increase norms on it. -/
theorem iterate_sub_le {E : Type*} [SeminormedAddCommGroup E] (T G : E → E) (S : Set E)
    (hTsub : ∀ a b, T a - T b = T (a - b)) (hT : ∀ a, ‖T a‖ ≤ ‖a‖)
    (hGS : ∀ x ∈ S, G x ∈ S) (hGn : ∀ x ∈ S, ‖G x‖ ≤ ‖x‖)
    {ε : ℝ} (hε : 0 ≤ ε) (hstep : ∀ x ∈ S, ‖T x - G x‖ ≤ ε * ‖x‖)
    {x : E} (hx : x ∈ S) (k : ℕ) :
    ‖T^[k] x - G^[k] x‖ ≤ k * ε * ‖x‖ := by
  have hG : ∀ j : ℕ, G^[j] x ∈ S ∧ ‖G^[j] x‖ ≤ ‖x‖ := by
    intro j
    induction j with
    | zero => exact ⟨hx, le_rfl⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hGS _ ih.1, (hGn _ ih.1).trans ih.2⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 : T (T^[k] x) - G (G^[k] x) =
        T (T^[k] x - G^[k] x) + (T (G^[k] x) - G (G^[k] x)) := by
      rw [← hTsub]
      abel
    rw [h1]
    calc ‖T (T^[k] x - G^[k] x) + (T (G^[k] x) - G (G^[k] x))‖
        ≤ ‖T (T^[k] x - G^[k] x)‖ + ‖T (G^[k] x) - G (G^[k] x)‖ := norm_add_le _ _
      _ ≤ k * ε * ‖x‖ + ε * ‖x‖ :=
          add_le_add ((hT _).trans ih)
            ((hstep _ (hG k).1).trans (mul_le_mul_of_nonneg_left (hG k).2 hε))
      _ = (k + 1 : ℕ) * ε * ‖x‖ := by push_cast; ring

section Projectors

variable (P : R → Matrix n n ℂ) (hPP : ∀ r s, P r * P s = if r = s then P r else 0)
  (hPsum : ∑ r, P r = 1)

theorem deph_add (A B : Matrix n n ℂ) : deph P (A + B) = deph P A + deph P B := by
  simp only [deph, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem deph_sub (A B : Matrix n n ℂ) : deph P (A - B) = deph P A - deph P B := by
  simp only [deph, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem deph_smul (c : ℂ) (A : Matrix n n ℂ) : deph P (c • A) = c • deph P A := by
  simp only [deph, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem deph_neg (A : Matrix n n ℂ) : deph P (-A) = -deph P A := by
  simp only [deph, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem deph_gen (H : Matrix n n ℂ) : deph P (gen H) = gen (deph P H) := by
  unfold gen
  exact deph_smul P _ _

include hPP in
theorem proj_mul_deph (A : Matrix n n ℂ) (r : R) : P r * deph P A = P r * A * P r := by
  unfold deph
  rw [Finset.mul_sum, Finset.sum_eq_single r]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, if_pos rfl]
  · intro s _ hs
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, if_neg (Ne.symm hs)]
    simp
  · intro h
    exact absurd (Finset.mem_univ r) h

include hPP in
theorem deph_mul_proj (A : Matrix n n ℂ) (r : R) : deph P A * P r = P r * A * P r := by
  unfold deph
  rw [Finset.sum_mul, Finset.sum_eq_single r]
  · rw [Matrix.mul_assoc, hPP, if_pos rfl]
  · intro s _ hs
    rw [Matrix.mul_assoc, hPP, if_neg hs]
    simp
  · intro h
    exact absurd (Finset.mem_univ r) h

include hPP in
/-- A block-diagonal matrix commutes with every record projector. -/
theorem proj_commute_of_deph (B : Matrix n n ℂ) (hB : deph P B = B) (r : R) :
    P r * B = B * P r := by
  have h1 := proj_mul_deph P hPP B r
  have h2 := deph_mul_proj P hPP B r
  rw [hB] at h1 h2
  rw [h1, h2]

include hPP in
theorem deph_mul_block (X B : Matrix n n ℂ) (hB : deph P B = B) :
    deph P (X * B) = deph P X * B ∧ deph P (B * X) = B * deph P X := by
  have hc := proj_commute_of_deph P hPP B hB
  constructor
  · unfold deph
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    calc P r * (X * B) * P r = P r * X * (B * P r) := by simp only [Matrix.mul_assoc]
      _ = P r * X * (P r * B) := by rw [← hc r]
      _ = P r * X * P r * B := by simp only [Matrix.mul_assoc]
  · unfold deph
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    calc P r * (B * X) * P r = P r * B * (X * P r) := by simp only [Matrix.mul_assoc]
      _ = B * P r * (X * P r) := by rw [hc r]
      _ = B * (P r * X * P r) := by simp only [Matrix.mul_assoc]

include hPP in
theorem deph_deph (A : Matrix n n ℂ) : deph P (deph P A) = deph P A := by
  unfold deph
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 := proj_mul_deph P hPP A r
  unfold deph at h1
  rw [h1, Matrix.mul_assoc (P r * A), hPP, if_pos rfl]

/-- The sign unitary `∑ᵣ ±Pᵣ`. -/
def sgnU (ε : R → Bool) : Matrix n n ℂ := ∑ r, sg (ε r) • P r

include hPP in
theorem sgnU_mul_self (ε : R → Bool) : sgnU P ε * sgnU P ε = ∑ r, P r := by
  unfold sgnU
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single r]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hPP, if_pos rfl, smul_smul, sg_mul_self, one_smul]
  · intro s _ hs
    rw [Matrix.smul_mul, Matrix.mul_smul, hPP, if_neg (Ne.symm hs)]
    simp
  · intro h
    exact absurd (Finset.mem_univ r) h

include hPP in
/-- Averaging the sign conjugations gives `2^{|R|}` times the dephasing. -/
theorem sum_sgnU_conj (A : Matrix n n ℂ) :
    ∑ ε : R → Bool, sgnU P ε * A * sgnU P ε = (2 : ℂ) ^ Fintype.card R • deph P A := by
  have hexp : ∀ ε : R → Bool, sgnU P ε * A * sgnU P ε =
      ∑ r, ∑ s, (sg (ε r) * sg (ε s)) • (P r * A * P s) := by
    intro ε
    unfold sgnU
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  unfold deph
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_sg_mul]
  rw [Finset.sum_eq_single r]
  · rw [if_pos rfl]
  · intro s _ hs
    rw [if_neg (Ne.symm hs), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ r) h

include hPP hPsum in
theorem sgnU_mem_unitary (hPh : ∀ r, star (P r) = P r) (ε : R → Bool) :
    sgnU P ε ∈ unitary (Matrix n n ℂ) := by
  have hstar : star (sgnU P ε) = sgnU P ε := by
    unfold sgnU
    rw [star_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [star_smul, hPh]
    congr 1
    cases ε r <;> simp [sg]
  have hsq := sgnU_mul_self P hPP ε
  rw [hPsum] at hsq
  rw [unitary.mem_iff, hstar, hsq]
  exact ⟨rfl, rfl⟩

include hPP hPsum in
/-- **The dephasing is a contraction in the operator norm.** -/
theorem norm_deph_le (hPh : ∀ r, star (P r) = P r) (A : Matrix n n ℂ) : ‖deph P A‖ ≤ ‖A‖ := by
  have hsum := sum_sgnU_conj P hPP A
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card R := by positivity
  have hnorm : ‖(2 : ℂ) ^ Fintype.card R • deph P A‖ ≤ (2 : ℝ) ^ Fintype.card R * ‖A‖ := by
    rw [← hsum]
    calc ‖∑ ε : R → Bool, sgnU P ε * A * sgnU P ε‖
        ≤ ∑ ε : R → Bool, ‖sgnU P ε * A * sgnU P ε‖ := norm_sum_le _ _
      _ ≤ ∑ _ε : R → Bool, ‖A‖ := Finset.sum_le_sum fun ε _ => by
          have hu := CStarRing.norm_of_mem_unitary (sgnU_mem_unitary P hPP hPsum hPh ε)
          calc ‖sgnU P ε * A * sgnU P ε‖ ≤ ‖sgnU P ε * A‖ * ‖sgnU P ε‖ := norm_mul_le _ _
            _ ≤ ‖sgnU P ε‖ * ‖A‖ * ‖sgnU P ε‖ := by gcongr; exact norm_mul_le _ _
            _ = ‖A‖ := by rw [hu]; ring
      _ = (2 : ℝ) ^ Fintype.card R * ‖A‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
          push_cast
          ring
  rw [norm_smul, norm_pow, Complex.norm_ofNat] at hnorm
  exact le_of_mul_le_mul_left hnorm hpos

theorem star_deph (hPh : ∀ r, star (P r) = P r) (A : Matrix n n ℂ) :
    star (deph P A) = deph P (star A) := by
  unfold deph
  rw [star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [star_mul, star_mul, hPh, Matrix.mul_assoc]

theorem deph_mem_skewAdjoint (hPh : ∀ r, star (P r) = P r) {X : Matrix n n ℂ}
    (hX : X ∈ skewAdjoint (Matrix n n ℂ)) : deph P X ∈ skewAdjoint (Matrix n n ℂ) := by
  rw [skewAdjoint.mem_iff] at hX ⊢
  rw [star_deph P hPh, hX, deph_neg]

theorem isSelfAdjoint_deph (hPh : ∀ r, star (P r) = P r) {H : Matrix n n ℂ}
    (hH : IsSelfAdjoint H) : IsSelfAdjoint (deph P H) := by
  show star (deph P H) = deph P H
  rw [star_deph P hPh, hH.star_eq]

theorem hasDerivAt_deph {f : ℂ → Matrix n n ℂ} {f' : Matrix n n ℂ} {u : ℂ}
    (h : HasDerivAt f f' u) : HasDerivAt (fun v => deph P (f v)) (deph P f') u := by
  unfold deph
  exact HasDerivAt.fun_sum fun r _ => (h.const_mul (P r)).mul_const (P r)

include hPP in
/-- The flow of a block-diagonal generator keeps the block-diagonal matrices. -/
theorem deph_flow (Y B : Matrix n n ℂ) (hY : deph P Y = Y) (hB : deph P B = B) (u : ℂ) :
    deph P (flow Y u B) = flow Y u B := by
  have hc : ∀ r, Commute (P r) (exp ℂ (u • Y)) := fun r =>
    ((show Commute (P r) Y from proj_commute_of_deph P hPP Y hY r).smul_right u).exp_right ℂ
  have hc' : ∀ r, Commute (P r) (exp ℂ (u • -Y)) := fun r =>
    ((show Commute (P r) Y from proj_commute_of_deph P hPP Y hY r).neg_right.smul_right
      u).exp_right ℂ
  have hterm : ∀ r, P r * flow Y u B * P r =
      exp ℂ (u • Y) * (P r * B * P r) * exp ℂ (u • -Y) := by
    intro r
    unfold flow
    calc P r * (exp ℂ (u • Y) * B * exp ℂ (u • -Y)) * P r
        = (P r * exp ℂ (u • Y)) * B * (exp ℂ (u • -Y) * P r) := by simp only [Matrix.mul_assoc]
      _ = (exp ℂ (u • Y) * P r) * B * (P r * exp ℂ (u • -Y)) := by
          rw [(hc r).eq, (hc' r).eq]
      _ = exp ℂ (u • Y) * (P r * B * P r) * exp ℂ (u • -Y) := by simp only [Matrix.mul_assoc]
  have hsum : deph P (flow Y u B) = exp ℂ (u • Y) * deph P B * exp ℂ (u • -Y) := by
    unfold deph
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => hterm r
  rw [hsum, hB]
  rfl

include hPP hPsum in
/-- **One Zeno step.** For a skew-adjoint generator `X` with `‖X‖ ≤ K` and a block-diagonal `B`,
dephasing after the flow of `X` for time `s ≥ 0` differs from the flow of the dephased generator
by at most `4 K² s² ‖B‖`. -/
theorem zeno_step_estimate (hPh : ∀ r, star (P r) = P r) {X : Matrix n n ℂ}
    (hX : X ∈ skewAdjoint (Matrix n n ℂ)) {K : ℝ} (hXK : ‖X‖ ≤ K) {B : Matrix n n ℂ}
    (hB : deph P B = B) {s : ℝ} (hs : 0 ≤ s) :
    ‖deph P (flow X (s : ℂ) B) - flow (deph P X) (s : ℂ) B‖ ≤ 4 * K ^ 2 * s ^ 2 * ‖B‖ := by
  have hXD : deph P X ∈ skewAdjoint (Matrix n n ℂ) := deph_mem_skewAdjoint P hPh hX
  have hXDK : ‖deph P X‖ ≤ K := (norm_deph_le P hPP hPsum hPh X).trans hXK
  let g0 : ℝ → Matrix n n ℂ := fun t => deph P (flow X t B) - flow (deph P X) t B
  let g1 : ℝ → Matrix n n ℂ := fun t =>
    deph P (ad X (flow X t B)) - ad (deph P X) (flow (deph P X) t B)
  let g2 : ℝ → Matrix n n ℂ := fun t =>
    deph P (ad X (ad X (flow X t B))) - ad (deph P X) (ad (deph P X) (flow (deph P X) t B))
  have hg0 : ∀ t : ℝ, HasDerivAt g0 (g1 t) t := fun t =>
    hasDerivAt_real ((hasDerivAt_deph P (hasDerivAt_flow X B t)).sub
      (hasDerivAt_flow (deph P X) B t))
  have hg1 : ∀ t : ℝ, HasDerivAt g1 (g2 t) t := fun t =>
    hasDerivAt_real ((hasDerivAt_deph P (hasDerivAt_ad X (hasDerivAt_flow X B t))).sub
      (hasDerivAt_ad (deph P X) (hasDerivAt_flow (deph P X) B t)))
  have hg0z : g0 0 = 0 := by
    show deph P (flow X ((0 : ℝ) : ℂ) B) - flow (deph P X) ((0 : ℝ) : ℂ) B = 0
    rw [Complex.ofReal_zero, flow_zero, flow_zero, hB, sub_self]
  have hg1z : g1 0 = 0 := by
    show deph P (ad X (flow X ((0 : ℝ) : ℂ) B)) -
      ad (deph P X) (flow (deph P X) ((0 : ℝ) : ℂ) B) = 0
    rw [Complex.ofReal_zero, flow_zero, flow_zero]
    obtain ⟨h1, h2⟩ := deph_mul_block P hPP X B hB
    unfold ad
    rw [deph_sub, h1, h2, sub_self]
  have had2 : ∀ Y Z : Matrix n n ℂ, ‖Y‖ ≤ K → ‖Z‖ ≤ ‖B‖ →
      ‖ad Y (ad Y Z)‖ ≤ 4 * K ^ 2 * ‖B‖ := by
    intro Y Z hY hZ
    have h1 : ‖ad Y (ad Y Z)‖ ≤ 2 * ‖Y‖ * (2 * ‖Y‖ * ‖Z‖) :=
      (norm_ad_le Y _).trans (mul_le_mul_of_nonneg_left (norm_ad_le Y Z) (by positivity))
    have h2 : ‖Y‖ * ‖Y‖ * ‖Z‖ ≤ K * K * ‖B‖ :=
      mul_le_mul (mul_self_le_mul_self (norm_nonneg Y) hY) hZ (norm_nonneg Z) (mul_self_nonneg K)
    nlinarith [h1, h2]
  have hg2b : ∀ t : ℝ, ‖g2 t‖ ≤ 8 * K ^ 2 * ‖B‖ := by
    intro t
    show ‖deph P (ad X (ad X (flow X t B))) -
      ad (deph P X) (ad (deph P X) (flow (deph P X) t B))‖ ≤ _
    calc ‖deph P (ad X (ad X (flow X t B))) -
          ad (deph P X) (ad (deph P X) (flow (deph P X) t B))‖
        ≤ ‖deph P (ad X (ad X (flow X t B)))‖ +
          ‖ad (deph P X) (ad (deph P X) (flow (deph P X) t B))‖ := norm_sub_le _ _
      _ ≤ ‖ad X (ad X (flow X t B))‖ +
          ‖ad (deph P X) (ad (deph P X) (flow (deph P X) t B))‖ := by
          gcongr
          exact norm_deph_le P hPP hPsum hPh _
      _ ≤ 4 * K ^ 2 * ‖B‖ + 4 * K ^ 2 * ‖B‖ :=
          add_le_add (had2 _ _ hXK (norm_flow_le hX t B)) (had2 _ _ hXDK (norm_flow_le hXD t B))
      _ = 8 * K ^ 2 * ‖B‖ := by ring
  have hcont1 : ContinuousOn g1 (Set.Icc 0 s) := fun x _ =>
    (hg1 x).continuousAt.continuousWithinAt
  have hcont0 : ContinuousOn g0 (Set.Icc 0 s) := fun x _ =>
    (hg0 x).continuousAt.continuousWithinAt
  have hstepA : ∀ x ∈ Set.Icc 0 s, ‖g1 x‖ ≤ 8 * K ^ 2 * ‖B‖ * x :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont1
      (fun x _ => (hg1 x).hasDerivWithinAt) (by simp [hg1z])
      (fun x => ((hasDerivAt_id' (x := x)).const_mul (8 * K ^ 2 * ‖B‖)).congr_deriv (by ring))
      (fun x _ => hg2b x)
  have hstepB : ∀ x ∈ Set.Icc 0 s, ‖g0 x‖ ≤ 8 * K ^ 2 * ‖B‖ / 2 * (x * x) :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont0
      (fun x _ => (hg0 x).hasDerivWithinAt) (by simp [hg0z])
      (fun x => (((hasDerivAt_id' (x := x)).fun_mul (hasDerivAt_id' (x := x))).const_mul
        (8 * K ^ 2 * ‖B‖ / 2)).congr_deriv (by ring))
      (fun x hx => hstepA x (Set.Ico_subset_Icc_self hx))
  calc ‖deph P (flow X (s : ℂ) B) - flow (deph P X) (s : ℂ) B‖ = ‖g0 s‖ := rfl
    _ ≤ 8 * K ^ 2 * ‖B‖ / 2 * (s * s) := hstepB s ⟨hs, le_rfl⟩
    _ = 4 * K ^ 2 * s ^ 2 * ‖B‖ := by ring

include hPP hPsum in
/-- **The Zeno limit, quantitative form.** With `F_s(A) = e^{-iHs} A e^{iHs}` and
`G_s(A) = e^{-iH_Δ s} A e^{iH_Δ s}` for Hermitian `H` and `H_Δ = Δ(H)`,
`‖(Δ ∘ F_{t/N})^N(Δ(A)) - G_t(Δ(A))‖ ≤ 4 ‖H‖² t² ‖A‖ / N` for every `t ≥ 0` and `N ≥ 1`. -/
theorem zeno_limit (hPh : ∀ r, star (P r) = P r) {H : Matrix n n ℂ} (hH : IsSelfAdjoint H)
    (A : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : 1 ≤ N) :
    ‖(fun C => deph P (flow (gen H) ((t / N : ℝ) : ℂ) C))^[N] (deph P A) -
        flow (gen (deph P H)) (t : ℂ) (deph P A)‖ ≤ 4 * ‖H‖ ^ 2 * t ^ 2 / N * ‖A‖ := by
  have hX : gen H ∈ skewAdjoint (Matrix n n ℂ) := gen_mem_skewAdjoint hH
  have hXD : gen (deph P H) ∈ skewAdjoint (Matrix n n ℂ) :=
    gen_mem_skewAdjoint (isSelfAdjoint_deph P hPh hH)
  have hD : deph P (gen (deph P H)) = gen (deph P H) := by
    rw [deph_gen, deph_deph P hPP]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs : 0 ≤ t / N := div_nonneg ht (Nat.cast_nonneg N)
  have hNt : (N : ℂ) * ((t / N : ℝ) : ℂ) = (t : ℂ) := by
    push_cast
    calc (N : ℂ) * ((t : ℂ) / (N : ℂ)) = (t : ℂ) * ((N : ℂ) * (N : ℂ)⁻¹) := by ring
      _ = (t : ℂ) := by rw [mul_inv_cancel₀ hNc, mul_one]
  have hiter : (fun C => flow (gen (deph P H)) ((t / N : ℝ) : ℂ) C)^[N] (deph P A) =
      flow (gen (deph P H)) (t : ℂ) (deph P A) := by
    rw [flow_iterate, hNt]
  rw [← hiter]
  have key := iterate_sub_le (fun C => deph P (flow (gen H) ((t / N : ℝ) : ℂ) C))
    (fun C => flow (gen (deph P H)) ((t / N : ℝ) : ℂ) C) {x | deph P x = x}
    (fun a b => by
      show deph P (flow (gen H) ((t / N : ℝ) : ℂ) a) - deph P (flow (gen H) ((t / N : ℝ) : ℂ) b) =
        deph P (flow (gen H) ((t / N : ℝ) : ℂ) (a - b))
      rw [flow_sub, deph_sub])
    (fun a => (norm_deph_le P hPP hPsum hPh _).trans (norm_flow_le hX (t / N) a))
    (fun x hx => deph_flow P hPP _ x hD hx _)
    (fun x _ => norm_flow_le hXD (t / N) x)
    (by positivity : (0 : ℝ) ≤ 4 * ‖H‖ ^ 2 * (t / N) ^ 2)
    (fun x hx => by
      have h := zeno_step_estimate P hPP hPsum hPh hX (norm_gen H).le hx hs
      rw [deph_gen] at h
      exact h)
    (deph_deph P hPP A) N
  refine key.trans ?_
  have hA : ‖deph P A‖ ≤ ‖A‖ := norm_deph_le P hPP hPsum hPh A
  have hcoef : (N : ℝ) * (4 * ‖H‖ ^ 2 * (t / N) ^ 2) = 4 * ‖H‖ ^ 2 * t ^ 2 / N := by
    calc (N : ℝ) * (4 * ‖H‖ ^ 2 * (t / N) ^ 2)
        = 4 * ‖H‖ ^ 2 * t ^ 2 / N * ((N : ℝ) * (N : ℝ)⁻¹) := by ring
      _ = 4 * ‖H‖ ^ 2 * t ^ 2 / N := by rw [mul_inv_cancel₀ hNr, mul_one]
  rw [hcoef]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

include hPP hPsum in
/-- **The Zeno limit.** The repeatedly dephased evolutions converge to the evolution generated by
the dephased Hamiltonian inside the block-diagonal algebra. -/
theorem zeno_tendsto (hPh : ∀ r, star (P r) = P r) {H : Matrix n n ℂ} (hH : IsSelfAdjoint H)
    (A : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto
      (fun N : ℕ => (fun C => deph P (flow (gen H) ((t / N : ℝ) : ℂ) C))^[N] (deph P A))
      Filter.atTop (nhds (flow (gen (deph P H)) (t : ℂ) (deph P A))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (4 * ‖H‖ ^ 2 * t ^ 2 * ‖A‖))
  refine Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩
  refine (zeno_limit P hPP hPsum hPh hH A ht hN).trans_eq ?_
  beta_reduce
  ring

end Projectors

end

end OperatorKO7.Meta.BoundaryObserver.ZenoLimit
