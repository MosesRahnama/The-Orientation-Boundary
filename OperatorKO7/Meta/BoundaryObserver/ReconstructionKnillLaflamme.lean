import OperatorKO7.Meta.BoundaryObserver.ReconstructionRecovery

/-!
# Finite Knill-Laflamme recovery

The error operators, code projector and recovery map share the finite complex
matrix carrier of the specification.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators Classical ComplexOrder

namespace OperatorKO7.Meta.BoundaryObserver.ReconstructionKnillLaflamme

open OperatorKO7.Meta.BoundaryObserver.ReconstructionRecovery
open OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation

def PSD {n : ℕ} (a : Mat n) : Prop :=
  a = dagger a ∧ ∀ v : Fin n → ℂ,
    0 ≤ (∑ i, ∑ j, star (v i) * a i j * v j).re

def Density (n : ℕ) := {a : Mat n // PSD a ∧ tr a = 1}

noncomputable def krausOutput {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (a : Mat n) : Mat n :=
  ∑ e, errors e * a * dagger (errors e)

def TracePreserving {n m : ℕ} (f : Mat n →ₗ[ℂ] Mat m) : Prop :=
  ∀ a, tr (f a) = tr a

def KnillLaflammeGoal : Prop :=
  ∀ (n : ℕ) (E : Type) [Fintype E] (errors : E → Mat n) (p : Mat n),
    0 < n → p = dagger p → p*p = p →
    (∑ e, dagger (errors e) * errors e) = 1 →
    ((∃ c : E → E → ℂ, ∀ a b,
        p * dagger (errors a) * errors b * p = c a b • p) ↔
     ∃ recovery : Mat n →ₗ[ℂ] Mat n,
       CompletelyPositive recovery ∧ TracePreserving recovery ∧
       ∀ ρ : Density n, p * ρ.val * p = ρ.val → recovery (krausOutput errors ρ.val) = ρ.val)

/-- The specification's square-matrix positivity is its indexed positivity. -/
theorem psd_iff_generalPSD {n : ℕ} (a : Mat n) :
    PSD a ↔ GeneralPSD a := by
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    intro i j
    exact congrArg (fun b : Mat n => b i j) h.1
  · intro h
    refine ⟨?_, h.2⟩
    funext i j
    exact h.1 i j

/-- The density carrier uses Mathlib positivity through the exact equivalence. -/
theorem psd_iff_posSemidef {n : ℕ} (a : Mat n) :
    PSD a ↔ a.PosSemidef :=
  (psd_iff_generalPSD a).trans (generalPSD_iff_posSemidef a)

/-- The specified error operation is the finite Kraus operation on every matrix. -/
theorem krausOutput_eq_cpMapKraus {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (a : Mat n) :
    krausOutput errors a = cpMapKraus errors a := rfl

/-- The error operation preserves complex linear combinations. -/
noncomputable def krausLinearMap {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun := krausOutput errors
  map_add' a b := by
    simp only [krausOutput, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    change (∑ e, errors e * (c • a) * dagger (errors e)) =
      c • ∑ e, errors e * a * dagger (errors e)
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- Every finite amplification of the identity preserves positivity. -/
theorem completelyPositive_id (n : ℕ) :
    CompletelyPositive (LinearMap.id : Mat n →ₗ[ℂ] Mat n) := by
  intro r a ha
  change GeneralPSD a
  exact ha

/-- The identity preserves the trace of every matrix. -/
theorem tracePreserving_id (n : ℕ) :
    TracePreserving (LinearMap.id : Mat n →ₗ[ℂ] Mat n) := by
  intro a
  rfl

/-- The error operation sends the zero matrix to zero. -/
theorem krausOutput_zero {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) : krausOutput errors (0 : Mat n) = 0 := by
  simp only [krausOutput, Matrix.mul_zero, Matrix.zero_mul, Finset.sum_const_zero]

/-- The zero projector satisfies the scalar overlap criterion. -/
theorem zero_projector_overlap {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) :
    ∃ c : E → E → ℂ, ∀ a b,
      (0 : Mat n) * dagger (errors a) * errors b * 0 = c a b • (0 : Mat n) := by
  refine ⟨fun _ _ => 0, ?_⟩
  intro a b
  simp only [Matrix.zero_mul, smul_zero]

/-- The identity recovers every density supported by the zero projector. -/
theorem zero_projector_recovery {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) :
    ∃ recovery : Mat n →ₗ[ℂ] Mat n,
      CompletelyPositive recovery ∧ TracePreserving recovery ∧
      ∀ ρ : Density n, (0 : Mat n) * ρ.val * 0 = ρ.val →
        recovery (krausOutput errors ρ.val) = ρ.val := by
  refine ⟨LinearMap.id, completelyPositive_id n, tracePreserving_id n, ?_⟩
  intro ρ hρ
  have hz : (0 : Mat n) = ρ.val := by
    simpa only [Matrix.zero_mul] using hρ
  change krausOutput errors ρ.val = ρ.val
  rw [← hz, krausOutput_zero]

/-- Both sides of the recovery equivalence hold for the zero projector. -/
theorem knillLaflamme_zero_projector {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) :
    ((∃ c : E → E → ℂ, ∀ a b,
        (0 : Mat n) * dagger (errors a) * errors b * 0 = c a b • (0 : Mat n)) ↔
      ∃ recovery : Mat n →ₗ[ℂ] Mat n,
        CompletelyPositive recovery ∧ TracePreserving recovery ∧
        ∀ ρ : Density n, (0 : Mat n) * ρ.val * 0 = ρ.val →
          recovery (krausOutput errors ρ.val) = ρ.val) :=
  ⟨fun _ => zero_projector_recovery errors, fun _ => zero_projector_overlap errors⟩

/-- Each error operator acts identically on every ancillary block. -/
def krausAmplification {n : ℕ} {E : Type}
    (errors : E → Mat n) (r : ℕ) (e : E) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ :=
  fun i j => if i.1 = j.1 then errors e i.2 j.2 else 0

/-- Left multiplication by an amplified error acts within the selected block. -/
theorem krausAmplification_mul_entry {n r : ℕ} {E : Type}
    (errors : E → Mat n)
    (a : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (e : E) (x y : Fin r) (i j : Fin n) :
    (krausAmplification errors r e * a) (x,i) (y,j) =
      ∑ k : Fin n, errors e i k * a (x,k) (y,j) := by
  change (∑ z : Fin r × Fin n,
    (if x = z.1 then errors e i z.2 else 0) * a z (y,j)) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ k : Fin n,
        (if x = x then errors e i k else 0) * a (x,k) (y,j) := by
      apply Finset.sum_eq_single x
      · intro z _ hzx
        simp only [if_neg (Ne.symm hzx), zero_mul, Finset.sum_const_zero]
      · intro hx
        exact False.elim (hx (Finset.mem_univ x))
    _ = ∑ k : Fin n, errors e i k * a (x,k) (y,j) := by
      simp only [ite_true]

/-- Amplified conjugation equals conjugation of each ancillary block. -/
theorem krausAmplification_sandwich_entry {n r : ℕ} {E : Type}
    (errors : E → Mat n)
    (a : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (e : E) (x y : Fin r) (i j : Fin n) :
    (krausAmplification errors r e * a * (krausAmplification errors r e)ᴴ)
        (x,i) (y,j) =
      (errors e * (Matrix.of fun k l => a (x,k) (y,l) : Mat n) * (errors e)ᴴ) i j := by
  change (∑ z : Fin r × Fin n,
    (krausAmplification errors r e * a) (x,i) z *
      star (if y = z.1 then errors e j z.2 else 0)) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ k : Fin n, (krausAmplification errors r e * a) (x,i) (y,k) *
        star (if y = y then errors e j k else 0) := by
      apply Finset.sum_eq_single y
      · intro z _ hzy
        simp only [if_neg (Ne.symm hzy), star_zero, mul_zero, Finset.sum_const_zero]
      · intro hy
        exact False.elim (hy (Finset.mem_univ y))
    _ = ∑ k : Fin n,
        (∑ l : Fin n, errors e i l * a (x,l) (y,k)) * star (errors e j k) := by
      simp only [ite_true, krausAmplification_mul_entry]
    _ = (errors e * (Matrix.of fun k l => a (x,k) (y,l) : Mat n) * (errors e)ᴴ) i j := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- Every ancillary amplification has the same finite Kraus construction. -/
theorem amplify_krausLinearMap {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (r : ℕ)
    (a : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    amplify (krausLinearMap errors) r a =
      ∑ e : E, krausAmplification errors r e * a *
        (krausAmplification errors r e)ᴴ := by
  ext x y
  change (∑ e : E,
    errors e * (Matrix.of fun k l => a (x.1,k) (y.1,l) : Mat n) * dagger (errors e)) x.2 y.2 =
      (∑ e : E, krausAmplification errors r e * a *
        (krausAmplification errors r e)ᴴ) x y
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro e _
  exact (krausAmplification_sandwich_entry errors a e x.1 y.1 x.2 y.2).symm

/-- A finite Kraus map is completely positive for every finite ancillary size. -/
theorem krausLinearMap_completelyPositive {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) : CompletelyPositive (krausLinearMap errors) := by
  intro r a ha
  apply (generalPSD_iff_posSemidef _).mpr
  rw [amplify_krausLinearMap]
  have hpa : a.PosSemidef := (generalPSD_iff_posSemidef a).mp ha
  refine Finset.sum_induction _ Matrix.PosSemidef
    (fun _ _ hB hC => hB.add hC) Matrix.PosSemidef.zero ?_
  intro e _
  exact hpa.mul_mul_conjTranspose_same (krausAmplification errors r e)

/-- The Kraus completeness equation implies preservation of every matrix trace. -/
theorem krausLinearMap_tracePreserving {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n)
    (hE : (∑ e, dagger (errors e) * errors e) = 1) :
    TracePreserving (krausLinearMap errors) := by
  intro a
  change tr (krausOutput errors a) = tr a
  rw [krausOutput_eq_cpMapKraus, kraus_trace_eq_gram_trace]
  change tr ((∑ e, dagger (errors e) * errors e) * a) = tr a
  rw [hE, Matrix.one_mul]

/-- The range matrix sums the error operators times their adjoints. -/
noncomputable def recoveryRangeSum {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) : Mat n :=
  ∑ d, u d * (u d)ᴴ

/-- The complementary matrix completes the recovery on the ambient space. -/
noncomputable def recoveryComplement {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) : Mat n :=
  1 - recoveryRangeSum u

/-- The range matrix is Hermitian for every finite family. -/
theorem recoveryRangeSum_conjTranspose {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) : (recoveryRangeSum u)ᴴ = recoveryRangeSum u := by
  unfold recoveryRangeSum
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Orthogonal error ranges are fixed by the range matrix. -/
theorem recoveryRangeSum_mul_error {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) (p : Mat n)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0)
    (e : D) : recoveryRangeSum u * u e = u e := by
  change (∑ d, u d * (u d)ᴴ) * u e = u e
  rw [Finset.sum_mul]
  calc
    _ = (u e * (u e)ᴴ) * u e := by
      apply Finset.sum_eq_single e
      · intro d _ hde
        rw [Matrix.mul_assoc, horth d e, if_neg hde, Matrix.mul_zero]
      · intro he
        exact False.elim (he (Finset.mem_univ e))
    _ = u e := by
      rw [Matrix.mul_assoc, horth e e, if_pos rfl, hUP e]

/-- The sum of the orthogonal error ranges is a projection. -/
theorem recoveryRangeSum_idempotent {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) (p : Mat n)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0) :
    recoveryRangeSum u * recoveryRangeSum u = recoveryRangeSum u := by
  change recoveryRangeSum u * (∑ d, u d * (u d)ᴴ) =
    ∑ d, u d * (u d)ᴴ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Matrix.mul_assoc, recoveryRangeSum_mul_error u p hUP horth d]

/-- The complementary matrix is Hermitian. -/
theorem recoveryComplement_conjTranspose {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) : (recoveryComplement u)ᴴ = recoveryComplement u := by
  unfold recoveryComplement
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    recoveryRangeSum_conjTranspose]

/-- The complementary projection annihilates each error range. -/
theorem recoveryComplement_mul_error {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) (p : Mat n)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0)
    (e : D) : recoveryComplement u * u e = 0 := by
  unfold recoveryComplement
  rw [Matrix.sub_mul, Matrix.one_mul,
    recoveryRangeSum_mul_error u p hUP horth e, sub_self]

/-- The complementary matrix is idempotent for orthogonal error ranges. -/
theorem recoveryComplement_idempotent {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) (p : Mat n)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0) :
    recoveryComplement u * recoveryComplement u = recoveryComplement u := by
  have hq := recoveryRangeSum_idempotent u p hUP horth
  unfold recoveryComplement
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    hq, sub_self, sub_zero]

/-- Recovery uses the adjoint errors and one complementary Kraus operator. -/
noncomputable def orthogonalRecoveryKraus {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) : Option D → Mat n
  | none => recoveryComplement u
  | some d => (u d)ᴴ

/-- The recovery map is the Kraus map of the constructed operators. -/
noncomputable def orthogonalRecovery {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) : Mat n →ₗ[ℂ] Mat n :=
  krausLinearMap (orthogonalRecoveryKraus u)

/-- The complementary Kraus operator supplies the missing trace contribution. -/
theorem orthogonalRecoveryKraus_complete {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) (p : Mat n)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0) :
    (∑ k, dagger (orthogonalRecoveryKraus u k) * orthogonalRecoveryKraus u k) = 1 := by
  rw [Fintype.sum_option]
  change (recoveryComplement u)ᴴ * recoveryComplement u +
    (∑ d : D, (u d)ᴴᴴ * (u d)ᴴ) = 1
  rw [recoveryComplement_conjTranspose,
    recoveryComplement_idempotent u p hUP horth]
  simp only [Matrix.conjTranspose_conjTranspose]
  change (1 - recoveryRangeSum u) + recoveryRangeSum u = 1
  exact sub_add_cancel _ _

/-- The constructed recovery is completely positive on every ancillary extension. -/
theorem orthogonalRecovery_completelyPositive {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) : CompletelyPositive (orthogonalRecovery u) :=
  krausLinearMap_completelyPositive (orthogonalRecoveryKraus u)

/-- The constructed recovery preserves trace on the whole matrix space. -/
theorem orthogonalRecovery_tracePreserving {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) (p : Mat n)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0) :
    TracePreserving (orthogonalRecovery u) :=
  krausLinearMap_tracePreserving (orthogonalRecoveryKraus u)
    (orthogonalRecoveryKraus_complete u p hUP horth)

/-- The constructed recovery reverses each orthogonal error branch. -/
theorem orthogonalRecovery_apply_error {n : ℕ} {D : Type} [Fintype D]
    (u : D → Mat n) (p : Mat n)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0)
    (a : Mat n) (e : D) :
    orthogonalRecovery u (u e * a * (u e)ᴴ) = p * a * p := by
  have hzero :
      recoveryComplement u * (u e * a * (u e)ᴴ) *
        (recoveryComplement u)ᴴ = 0 := by
    calc
      _ = (recoveryComplement u * u e) * a * (u e)ᴴ *
          (recoveryComplement u)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by
        simp only [recoveryComplement_mul_error u p hUP horth e, Matrix.zero_mul]
  change (∑ k : Option D,
    orthogonalRecoveryKraus u k * (u e * a * (u e)ᴴ) *
      (orthogonalRecoveryKraus u k)ᴴ) = p * a * p
  rw [Fintype.sum_option]
  change recoveryComplement u * (u e * a * (u e)ᴴ) *
      (recoveryComplement u)ᴴ +
    (∑ d : D, (u d)ᴴ * (u e * a * (u e)ᴴ) * (u d)ᴴᴴ) = p * a * p
  simp only [Matrix.conjTranspose_conjTranspose]
  rw [hzero, zero_add]
  calc
    _ = (u e)ᴴ * (u e * a * (u e)ᴴ) * u e := by
      apply Finset.sum_eq_single e
      · intro d _ hde
        calc
          _ = ((u d)ᴴ * u e) * a * ((u e)ᴴ * u d) := by
            simp only [Matrix.mul_assoc]
          _ = 0 := by
            simp only [horth d e, if_neg hde, Matrix.zero_mul]
      · intro he
        exact False.elim (he (Finset.mem_univ e))
    _ = ((u e)ᴴ * u e) * a * ((u e)ᴴ * u e) := by
      simp only [Matrix.mul_assoc]
    _ = p * a * p := by
      simp only [horth e e, ite_true]

/-- A normalized orthogonal decomposition is reversed on every code matrix. -/
theorem orthogonalRecovery_correct {n : ℕ} {E D : Type}
    [Fintype E] [Fintype D]
    (errors : E → Mat n) (u : D → Mat n) (p : Mat n)
    (weights : D → ℂ)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0)
    (hweights : (∑ d, weights d) = 1)
    (hnoise : ∀ a : Mat n, p * a * p = a →
      krausOutput errors a = ∑ d, weights d • (u d * a * (u d)ᴴ))
    (a : Mat n) (ha : p * a * p = a) :
    orthogonalRecovery u (krausOutput errors a) = a := by
  calc
    _ = ∑ d, weights d • (p * a * p) := by
      rw [hnoise a ha, map_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [(orthogonalRecovery u).map_smul,
        orthogonalRecovery_apply_error u p hUP horth a d]
    _ = a := by
      rw [ha]
      ext i j
      rw [Matrix.sum_apply]
      change (∑ d, weights d * a i j) = a i j
      rw [← Finset.sum_mul, hweights, one_mul]

/-- The orthogonal decomposition supplies an explicit ambient channel recovery. -/
theorem recovery_of_orthogonal_decomposition {n : ℕ} {E D : Type}
    [Fintype E] [Fintype D]
    (errors : E → Mat n) (u : D → Mat n) (p : Mat n)
    (weights : D → ℂ)
    (hUP : ∀ d, u d * p = u d)
    (horth : ∀ d e, (u d)ᴴ * u e = if d = e then p else 0)
    (hweights : (∑ d, weights d) = 1)
    (hnoise : ∀ a : Mat n, p * a * p = a →
      krausOutput errors a = ∑ d, weights d • (u d * a * (u d)ᴴ)) :
    ∃ recovery : Mat n →ₗ[ℂ] Mat n,
      CompletelyPositive recovery ∧ TracePreserving recovery ∧
      ∀ ρ : Density n, p * ρ.val * p = ρ.val →
        recovery (krausOutput errors ρ.val) = ρ.val := by
  refine ⟨orthogonalRecovery u, orthogonalRecovery_completelyPositive u,
    orthogonalRecovery_tracePreserving u p hUP horth, ?_⟩
  intro ρ hρ
  exact orthogonalRecovery_correct errors u p weights hUP horth hweights
    hnoise ρ.val hρ

/-- An orthogonal code projector is positive semidefinite. -/
theorem codeProjector_posSemidef {n : ℕ} (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p) : p.PosSemidef := by
  have hs : pᴴ = p := hstar.symm
  have h := Matrix.posSemidef_conjTranspose_mul_self p
  rw [hs, hidem] at h
  exact h

/-- A nonzero orthogonal code projector has strictly positive real trace. -/
theorem codeProjector_trace_pos {n : ℕ} (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p) (hne : p ≠ 0) :
    0 < (tr p).re := by
  have hp := codeProjector_posSemidef p hstar hidem
  refine lt_of_le_of_ne (posSemidef_trace_re_nonneg p hp) ?_
  intro hzero
  exact hne (posSemidef_eq_zero_of_trace_re_zero p hp hzero.symm)

/-- Each restricted error is stored as one column with input index first. -/
def codeErrorColumns {n : ℕ} {E : Type}
    (errors : E → Mat n) (p : Mat n) : Matrix (Fin n × Fin n) E ℂ :=
  fun k e => (errors e * p) k.2 k.1

/-- The scalar Gram entries are Hilbert-Schmidt inner products of restricted errors. -/
theorem codeErrorColumns_gram_entry {n : ℕ} {E : Type}
    (errors : E → Mat n) (p : Mat n) (a b : E) :
    ((codeErrorColumns errors p)ᴴ * codeErrorColumns errors p) a b =
      tr ((errors a * p)ᴴ * (errors b * p)) := by
  change (∑ k : Fin n × Fin n,
    star ((errors a * p) k.2 k.1) * (errors b * p) k.2 k.1) =
      ∑ i : Fin n, ∑ j : Fin n,
        star ((errors a * p) j i) * (errors b * p) j i
  rw [Fintype.sum_prod_type]

/-- The original overlap equations identify the coefficient matrix with a scaled Gram matrix. -/
theorem codeErrorColumns_gram {n : ℕ} {E : Type}
    (errors : E → Mat n) (p : Mat n) (hstar : p = dagger p)
    (c : Matrix E E ℂ)
    (hKL : ∀ a b, p * dagger (errors a) * errors b * p = c a b • p) :
    (codeErrorColumns errors p)ᴴ * codeErrorColumns errors p = (tr p) • c := by
  have hs : pᴴ = p := hstar.symm
  ext a b
  rw [codeErrorColumns_gram_entry]
  calc
    _ = tr (p * dagger (errors a) * errors b * p) := by
      rw [Matrix.conjTranspose_mul, hs]
      simp only [Matrix.mul_assoc]
    _ = tr (c a b • p) := by rw [hKL a b]
    _ = c a b * tr p := by
      unfold tr
      rw [Matrix.trace_smul]
      rfl
    _ = ((tr p) • c) a b := by
      change c a b * tr p = tr p * c a b
      exact mul_comm _ _

/-- Positivity of the overlap coefficients follows from the actual error equations. -/
theorem overlapMatrix_posSemidef {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p) (hne : p ≠ 0)
    (c : Matrix E E ℂ)
    (hKL : ∀ a b, p * dagger (errors a) * errors b * p = c a b • p) :
    c.PosSemidef := by
  let t : ℝ := (tr p).re
  have hp := codeProjector_posSemidef p hstar hidem
  have ht : 0 < t := codeProjector_trace_pos p hstar hidem hne
  have hreal : tr p = (t : ℂ) := posSemidef_trace_eq_ofReal p hp
  have hscalar : (((t⁻¹ : ℝ) : ℂ) * (t : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, mul_comm t⁻¹ t, mul_inv_cancel₀ (ne_of_gt ht)]
    rfl
  have hscaled :
      (((t⁻¹ : ℝ) : ℂ) •
        ((codeErrorColumns errors p)ᴴ * codeErrorColumns errors p)).PosSemidef :=
    posSemidef_real_smul_gen
      (Matrix.posSemidef_conjTranspose_mul_self (codeErrorColumns errors p))
      (inv_nonneg.mpr (posSemidef_trace_re_nonneg p hp))
  rw [codeErrorColumns_gram errors p hstar c hKL, hreal, smul_smul,
    hscalar, one_smul] at hscaled
  exact hscaled

/-- A nonzero matrix cannot be fixed by a nonunit scalar multiple. -/
theorem scalar_eq_one_of_smul_nonzero_matrix {n : ℕ}
    (p : Mat n) (hp : p ≠ 0) (s : ℂ) (hs : s • p = p) : s = 1 := by
  have hex : ∃ i j : Fin n, p i j ≠ 0 := by
    by_contra hn
    apply hp
    ext i j
    by_contra hij
    exact hn ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hex
  have hentry := congrArg (fun a : Mat n => a i j) hs
  change s * p i j = p i j at hentry
  exact (mul_eq_right₀ hij).mp hentry

/-- The overlap coefficients have total diagonal weight one.
    This normalization follows from the original channel completeness law. -/
theorem knillLaflamme_coefficient_total {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n) (hne : p ≠ 0)
    (hidem : p * p = p)
    (hcomplete : (∑ e, dagger (errors e) * errors e) = 1)
    (c : E → E → ℂ)
    (hKL : ∀ a b, p * dagger (errors a) * errors b * p = c a b • p) :
    (∑ e : E, c e e) = 1 := by
  have hprojected :
      (∑ e : E, p * dagger (errors e) * errors e * p) = p := by
    calc
      _ = p * (∑ e : E, dagger (errors e) * errors e) * p := by
        simp only [Matrix.mul_assoc, Finset.sum_mul, Finset.mul_sum]
      _ = p := by
        rw [hcomplete, Matrix.mul_one, hidem]
  apply scalar_eq_one_of_smul_nonzero_matrix p hne
  calc
    (∑ e : E, c e e) • p = ∑ e : E, c e e • p := by
      rw [Finset.sum_smul]
    _ = ∑ e : E, p * dagger (errors e) * errors e * p := by
      apply Finset.sum_congr rfl
      intro e _
      exact (hKL e e).symm
    _ = p := hprojected

/-- Error operators are changed by a finite complex unitary index rotation. -/
noncomputable def rotatedErrors {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (u : Matrix E E ℂ) (d : E) : Mat n :=
  ∑ a : E, u a d • errors a

/-- The adjoint of a rotated error uses the conjugated matrix coefficients. -/
theorem rotatedErrors_adjoint {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (u : Matrix E E ℂ) (d : E) :
    dagger (rotatedErrors errors u d) =
      ∑ a : E, star (u a d) • dagger (errors a) := by
  unfold rotatedErrors dagger
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.conjTranspose_smul]

/-- A finite index rotation transports the original restricted overlap
    equations to the conjugated coefficient matrix. -/
theorem rotatedErrors_overlap {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (c u : Matrix E E ℂ)
    (hKL : ∀ a b, p * dagger (errors a) * errors b * p = c a b • p)
    (d e : E) :
    p * dagger (rotatedErrors errors u d) *
        rotatedErrors errors u e * p =
      (uᴴ * c * u) d e • p := by
  have hcoeff :
      (∑ a : E, ∑ b : E, star (u a d) * u b e * c a b) =
        (uᴴ * c * u) d e := by
    change (∑ a : E, ∑ b : E, star (u a d) * u b e * c a b) =
      ∑ b : E, (∑ a : E, star (u a d) * c a b) * u b e
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  calc
    p * dagger (rotatedErrors errors u d) * rotatedErrors errors u e * p =
        ∑ a : E, ∑ b : E, (star (u a d) * u b e) •
          (p * dagger (errors a) * errors b * p) := by
      rw [rotatedErrors_adjoint]
      unfold rotatedErrors
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      exact mul_comm _ _
    _ = ∑ a : E, ∑ b : E, (star (u a d) * u b e * c a b) • p := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hKL a b, smul_smul]
    _ = (uᴴ * c * u) d e • p := by
      rw [← hcoeff]
      simp only [Finset.sum_smul]

/-- The original Knill-Laflamme coefficients admit a concrete unitary
    diagonalization, and the rotated physical errors inherit the exact
    diagonal restricted operator overlaps. -/
theorem knillLaflamme_diagonalized_errors
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p) (hne : p ≠ 0)
    (c : E → E → ℂ)
    (hKL : ∀ a b, p * dagger (errors a) * errors b * p = c a b • p) :
    ∃ u : Matrix E E ℂ, uᴴ * u = 1 ∧ u * uᴴ = 1 ∧
      ∃ wt : E → ℝ, (∀ d, 0 ≤ wt d) ∧
        ∀ d e, p * dagger (rotatedErrors errors u d) *
            rotatedErrors errors u e * p =
          (Matrix.diagonal (fun k => (wt k : ℂ))) d e • p := by
  let cm : Matrix E E ℂ := fun a b => c a b
  have hc : cm.PosSemidef :=
    overlapMatrix_posSemidef errors p hstar hidem hne cm hKL
  let u : Matrix E E ℂ := hc.1.eigenvectorUnitary
  let wt : E → ℝ := hc.1.eigenvalues
  have hUL : uᴴ * u = 1 := by
    exact (hc.1.eigenvectorUnitary).property.1
  have hUR : u * uᴴ = 1 := by
    exact (hc.1.eigenvectorUnitary).property.2
  have hdiag : uᴴ * cm * u =
      Matrix.diagonal (fun k : E => (wt k : ℂ)) :=
    hc.1.star_mul_self_mul_eq_diagonal
  refine ⟨u, hUL, hUR, wt, hc.eigenvalues_nonneg, ?_⟩
  intro d e
  rw [rotatedErrors_overlap errors p cm u hKL d e, hdiag]

/-- The spectral weights of the actual Knill-Laflamme overlap have
    total mass one, by invariance of matrix trace under unitary rotation. -/
theorem knillLaflamme_eigenweights_total
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n) (hne : p ≠ 0)
    (hidem : p * p = p)
    (hcomplete : (∑ e, dagger (errors e) * errors e) = 1)
    (c : Matrix E E ℂ)
    (hKL : ∀ a b, p * dagger (errors a) * errors b * p = c a b • p)
    (hc : c.PosSemidef) :
    (∑ d : E, (hc.1.eigenvalues d : ℂ)) = 1 := by
  let u : Matrix E E ℂ := hc.1.eigenvectorUnitary
  have hunitary : u * uᴴ = 1 :=
    (hc.1.eigenvectorUnitary).property.2
  have hdiag : uᴴ * c * u =
      Matrix.diagonal (fun k : E => (hc.1.eigenvalues k : ℂ)) :=
    hc.1.star_mul_self_mul_eq_diagonal
  have htrace : Matrix.trace (uᴴ * c * u) = Matrix.trace c := by
    calc
      _ = Matrix.trace (u * (uᴴ * c)) :=
        Matrix.trace_mul_comm (uᴴ * c) u
      _ = Matrix.trace ((u * uᴴ) * c) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace c := by
        rw [hunitary, Matrix.one_mul]
  calc
    (∑ d : E, (hc.1.eigenvalues d : ℂ)) =
        Matrix.trace (Matrix.diagonal
          (fun k : E => (hc.1.eigenvalues k : ℂ))) :=
      (Matrix.trace_diagonal _).symm
    _ = Matrix.trace (uᴴ * c * u) := by rw [hdiag]
    _ = Matrix.trace c := htrace
    _ = ∑ d : E, c d d := rfl
    _ = 1 :=
      knillLaflamme_coefficient_total errors p hne hidem hcomplete c hKL

/-- The columns of the finite Kraus matrix are the vectorized error operators. -/
def errorOperatorColumns {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) : Matrix (Fin n × Fin n) E ℂ :=
  fun k e => (errors e) k.2 k.1

/-- A unitary change of Kraus index multiplies this matrix on the right. -/
theorem errorOperatorColumns_rotated {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (u : Matrix E E ℂ) :
    errorOperatorColumns (rotatedErrors errors u) =
      errorOperatorColumns errors * u := by
  ext k d
  change (∑ a : E, u a d • errors a) k.2 k.1 =
    ∑ a : E, errors a k.2 k.1 * u a d
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

/-- Conjugating a matrix unit by a single error picks out its two
    corresponding vectorized error coefficients. -/
theorem krausOutput_single_coeff {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (i j r s : Fin n) :
    (krausOutput errors (Matrix.single i j (1 : ℂ))) r s =
      ∑ e : E, errors e r i * star (errors e s j) := by
  unfold krausOutput
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro e _
  calc
    (errors e * Matrix.single i j (1 : ℂ) * dagger (errors e)) r s =
        (errors e * Matrix.single i j (1 : ℂ)) r j *
          dagger (errors e) j s := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [Matrix.mul_single_apply_of_ne (1 : ℂ) i j r k hkj (errors e),
          zero_mul]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
    _ = errors e r i * star (errors e s j) := by
      simp only [dagger, Matrix.mul_single_apply_same, Matrix.conjTranspose_apply, mul_one]

/-- The actual Choi matrix of a finite Kraus operation is the Gram
    matrix of the complete vectorized error family. -/
theorem choi_krausLinearMap {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) :
    choiMatrix (krausLinearMap errors) =
      errorOperatorColumns errors * (errorOperatorColumns errors)ᴴ := by
  ext ⟨i, r⟩ ⟨j, s⟩
  change (krausOutput errors (Matrix.single i j (1 : ℂ))) r s =
    ∑ e : E, errors e r i * star (errors e s j)
  exact krausOutput_single_coeff errors i j r s

/-- Unitary Kraus-index rotation leaves the complete quantum channel
    unchanged on every input matrix, including non-Hermitian inputs. -/
theorem rotatedErrors_krausOutput {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (u : Matrix E E ℂ)
    (hu : u * uᴴ = 1) (a : Mat n) :
    krausOutput (rotatedErrors errors u) a = krausOutput errors a := by
  have hchoi :
      choiMatrix (krausLinearMap (rotatedErrors errors u)) =
        choiMatrix (krausLinearMap errors) := by
    rw [choi_krausLinearMap, choi_krausLinearMap,
      errorOperatorColumns_rotated, Matrix.conjTranspose_mul]
    calc
      (errorOperatorColumns errors * u) *
          (uᴴ * (errorOperatorColumns errors)ᴴ) =
        errorOperatorColumns errors * (u * uᴴ) *
          (errorOperatorColumns errors)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = errorOperatorColumns errors *
          (errorOperatorColumns errors)ᴴ := by
        rw [hu, Matrix.mul_one]
  have heq : krausLinearMap (rotatedErrors errors u) =
      krausLinearMap errors := choiMatrix_injective hchoi
  exact congrArg (fun f : Mat n →ₗ[ℂ] Mat n => f a) heq

/-- A finite matrix with zero adjoint Gram operator is the zero matrix. -/
theorem matrix_eq_zero_of_conjTranspose_mul_self_eq_zero
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℂ)
    (hzero : aᴴ * a = 0) : a = 0 := by
  have hmv : ∀ v : Fin n → ℂ, a *ᵥ v = 0 := by
    intro v
    have hform : star v ⬝ᵥ ((aᴴ * a) *ᵥ v) = 0 := by
      rw [hzero, Matrix.zero_mulVec, dotProduct_zero]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_conjTranspose, star_star] at hform
    exact dotProduct_star_self_eq_zero.mp hform
  ext i j
  have hentry := congrFun (hmv (Pi.single j (1 : ℂ))) i
  simpa only [Matrix.mulVec_single_one, Pi.zero_apply] using hentry

/-- A zero eigenvalue forces the associated restricted rotated error
    operator to vanish, rather than creating an invalid inverse. -/
theorem rotatedErrors_zero_weight
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p)
    (u : Matrix E E ℂ) (wt : E → ℝ)
    (hdiagonal : ∀ d e, p * dagger (rotatedErrors errors u d) *
        rotatedErrors errors u e * p =
          (Matrix.diagonal (fun k => (wt k : ℂ))) d e • p)
    (d : E) (hd : wt d = 0) :
    rotatedErrors errors u d * p = 0 := by
  let f : Mat n := rotatedErrors errors u d
  have hgram : (f * p)ᴴ * (f * p) = 0 := by
    calc
      (f * p)ᴴ * (f * p) = p * dagger f * f * p := by
        rw [Matrix.conjTranspose_mul]
        rw [show pᴴ = p from hstar.symm]
        simp only [Matrix.mul_assoc]
      _ = 0 := by
        have h := hdiagonal d d
        change p * dagger f * f * p =
          (Matrix.diagonal (fun k => (wt k : ℂ))) d d • p at h
        simpa only [Matrix.diagonal_apply_eq, hd, Complex.ofReal_zero, zero_smul] using h
  exact matrix_eq_zero_of_conjTranspose_mul_self_eq_zero _ hgram

/-- Each positive spectral sector carries the restricted error divided
    by the positive square root of its own error weight. -/
noncomputable def normalizedSyndromeErrors
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (u : Matrix E E ℂ) (wt : E → ℝ)
    (d : {e : E // 0 < wt e}) : Mat n :=
  ((↑(Real.sqrt (wt d.val)) : ℂ)⁻¹) •
    (rotatedErrors errors u d.val * p)

/-- Every positive-sector error acts only on the original code. -/
theorem normalizedSyndromeErrors_mul_p
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hidem : p * p = p)
    (u : Matrix E E ℂ) (wt : E → ℝ)
    (d : {e : E // 0 < wt e}) :
    normalizedSyndromeErrors errors p u wt d * p =
      normalizedSyndromeErrors errors p u wt d := by
  unfold normalizedSyndromeErrors
  rw [Matrix.smul_mul, Matrix.mul_assoc, hidem]

/-- Normalized positive-weight error sectors have orthogonal ranges
    and act as isometries from the original code, with no zero inversion. -/
theorem normalizedSyndromeErrors_orthogonal
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p)
    (u : Matrix E E ℂ) (wt : E → ℝ)
    (hdiagonal : ∀ d e, p * dagger (rotatedErrors errors u d) *
        rotatedErrors errors u e * p =
          (Matrix.diagonal (fun k => (wt k : ℂ))) d e • p) :
    ∀ d e : {k : E // 0 < wt k},
      dagger (normalizedSyndromeErrors errors p u wt d) *
        normalizedSyndromeErrors errors p u wt e =
      if d = e then p else 0 := by
  classical
  let σ : {k : E // 0 < wt k} → ℂ :=
    fun d => (↑(Real.sqrt (wt d.val)) : ℂ)⁻¹
  have hs (d : {k : E // 0 < wt k}) : star (σ d) = σ d := by
    dsimp only [σ]
    simp only [Complex.star_def, Complex.conj_inv, Complex.conj_ofReal]
  have hroot (d : {k : E // 0 < wt k}) :
      0 < Real.sqrt (wt d.val) := Real.sqrt_pos.mpr d.property
  have hroot_ne (d : {k : E // 0 < wt k}) :
      (↑(Real.sqrt (wt d.val)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (hroot d))
  have hsquare (d : {k : E // 0 < wt k}) :
      (↑(Real.sqrt (wt d.val)) : ℂ) ^ 2 = (wt d.val : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt d.property.le]
  have hnormal (d : {k : E // 0 < wt k}) :
      σ d * σ d * (wt d.val : ℂ) = 1 := by
    calc
      σ d * σ d * (wt d.val : ℂ) =
          (σ d * (↑(Real.sqrt (wt d.val)) : ℂ)) ^ 2 := by
        rw [← hsquare d]
        ring
      _ = 1 := by
        dsimp only [σ]
        rw [inv_mul_cancel₀ (hroot_ne d), one_pow]
  have hraw (d e : {k : E // 0 < wt k}) :
      (rotatedErrors errors u d.val * p)ᴴ *
          (rotatedErrors errors u e.val * p) =
        p * dagger (rotatedErrors errors u d.val) *
          rotatedErrors errors u e.val * p := by
    rw [Matrix.conjTranspose_mul]
    rw [show pᴴ = p from hstar.symm]
    simp only [Matrix.mul_assoc]
  intro d e
  calc
    dagger (normalizedSyndromeErrors errors p u wt d) *
        normalizedSyndromeErrors errors p u wt e =
        (star (σ d) * σ e) •
          ((rotatedErrors errors u d.val * p)ᴴ *
            (rotatedErrors errors u e.val * p)) := by
      unfold normalizedSyndromeErrors dagger
      change (((σ d) • (rotatedErrors errors u d.val * p))ᴴ *
        ((σ e) • (rotatedErrors errors u e.val * p))) = _
      simp only [Matrix.conjTranspose_smul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul]
      congr 1
      ring
    _ = (star (σ d) * σ e) •
          (p * dagger (rotatedErrors errors u d.val) *
            rotatedErrors errors u e.val * p) := by
      rw [hraw d e]
    _ = (star (σ d) * σ e) •
          ((Matrix.diagonal (fun k => (wt k : ℂ))) d.val e.val • p) := by
      rw [hdiagonal]
    _ = if d = e then p else 0 := by
      by_cases hde : d = e
      · subst e
        simp only [↓reduceIte, Matrix.diagonal_apply_eq, smul_smul,
          hs d, hnormal d, one_smul]
      · have hval : d.val ≠ e.val := by
          intro heq
          exact hde (Subtype.ext heq)
        rw [Matrix.diagonal_apply_ne _ hval, if_neg hde]
        simp only [zero_smul, smul_zero]

/-- Removing indices whose summands vanish does not alter a finite sum. -/
theorem sum_positive_indices_eq_total
    {E : Type} [Fintype E] (wt : E → ℝ)
    {M : Type} [AddCommMonoid M] (f : E → M)
    (hzero : ∀ d, ¬ 0 < wt d → f d = 0) :
    (∑ d : {k : E // 0 < wt k}, f d.val) = ∑ d : E, f d := by
  classical
  have hpartition :=
    Fintype.sum_subtype_add_sum_subtype (fun d : E => 0 < wt d) f
  have hnegative : (∑ d : {k : E // ¬ 0 < wt k}, f d.val) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    exact hzero d.val d.property
  simpa only [hnegative, add_zero] using hpartition

/-- Only strictly positive real eigenweights contribute to their total. -/
theorem positive_eigenweights_sum
    {E : Type} [Fintype E] (wt : E → ℝ)
    (hwt : ∀ d, 0 ≤ wt d)
    (htotal : (∑ d : E, (wt d : ℂ)) = 1) :
    (∑ d : {k : E // 0 < wt k}, (wt d.val : ℂ)) = 1 := by
  calc
    _ = ∑ d : E, (wt d : ℂ) := by
      refine sum_positive_indices_eq_total wt (fun d => (wt d : ℂ)) ?_
      intro d hn
      have hz : wt d = 0 := le_antisymm (le_of_not_gt hn) (hwt d)
      change (wt d : ℂ) = 0
      rw [hz, Complex.ofReal_zero]
    _ = 1 := htotal

/-- Code support permits insertion of the original projector on both
    sides of every physical error's input matrix. -/
theorem error_sandwich_of_code_support {n : ℕ}
    (f p a : Mat n) (hstar : p = dagger p)
    (ha : p * a * p = a) :
    f * a * dagger f =
      (f * p) * a * dagger (f * p) := by
  have hs : pᴴ = p := hstar.symm
  conv_lhs => rw [← ha]
  simp only [dagger, Matrix.conjTranspose_mul, hs, Matrix.mul_assoc]

/-- The positive spectral weight exactly cancels the normalization
    of its constructed code-supported partial isometry. -/
theorem normalizedSyndromeErrors_weighted_sandwich
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p a : Mat n)
    (u : Matrix E E ℂ) (wt : E → ℝ)
    (d : {k : E // 0 < wt k}) :
    (wt d.val : ℂ) •
        (normalizedSyndromeErrors errors p u wt d * a *
          dagger (normalizedSyndromeErrors errors p u wt d)) =
      (rotatedErrors errors u d.val * p) * a *
        dagger (rotatedErrors errors u d.val * p) := by
  let z : ℂ := (Real.sqrt (wt d.val) : ℂ)
  have hz : z ≠ 0 := by
    dsimp only [z]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr d.property))
  have hreal : star z = z := by
    dsimp only [z]
    simp only [Complex.star_def, Complex.conj_ofReal]
  have hsq : z * z = (wt d.val : ℂ) := by
    dsimp only [z]
    rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt d.property.le]
  have hroot :
      z • normalizedSyndromeErrors errors p u wt d =
        rotatedErrors errors u d.val * p := by
    unfold normalizedSyndromeErrors
    change z • (z⁻¹ • (rotatedErrors errors u d.val * p)) = _
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
  calc
    (wt d.val : ℂ) •
        (normalizedSyndromeErrors errors p u wt d * a *
          dagger (normalizedSyndromeErrors errors p u wt d)) =
      (z • normalizedSyndromeErrors errors p u wt d) * a *
        dagger (z • normalizedSyndromeErrors errors p u wt d) := by
      simp only [dagger, Matrix.conjTranspose_smul, hreal,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hsq,
        mul_assoc]
    _ = (rotatedErrors errors u d.val * p) * a *
        dagger (rotatedErrors errors u d.val * p) := by
      rw [hroot]

/-- The original error channel has an exact positive-weight
    orthogonal-syndrome decomposition on every code-supported matrix. -/
theorem knillLaflamme_positive_syndrome_decomposition
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p)
    (u : Matrix E E ℂ) (hu : u * uᴴ = 1)
    (wt : E → ℝ) (hwt : ∀ d, 0 ≤ wt d)
    (hdiagonal : ∀ d e, p * dagger (rotatedErrors errors u d) *
        rotatedErrors errors u e * p =
          (Matrix.diagonal (fun k => (wt k : ℂ))) d e • p)
    (a : Mat n) (ha : p * a * p = a) :
    krausOutput errors a =
      ∑ d : {k : E // 0 < wt k}, (wt d.val : ℂ) •
        (normalizedSyndromeErrors errors p u wt d * a *
          dagger (normalizedSyndromeErrors errors p u wt d)) := by
  have hzero (d : E) (hd : ¬ 0 < wt d) :
      rotatedErrors errors u d * a *
          dagger (rotatedErrors errors u d) = 0 := by
    have hd0 : wt d = 0 := le_antisymm (le_of_not_gt hd) (hwt d)
    have hz := rotatedErrors_zero_weight errors p hstar u wt hdiagonal d hd0
    rw [error_sandwich_of_code_support
      (rotatedErrors errors u d) p a hstar ha]
    rw [hz]
    simp only [Matrix.zero_mul]
  calc
    krausOutput errors a =
        krausOutput (rotatedErrors errors u) a :=
      (rotatedErrors_krausOutput errors u hu a).symm
    _ = ∑ d : E, rotatedErrors errors u d * a *
          dagger (rotatedErrors errors u d) := rfl
    _ = ∑ d : {k : E // 0 < wt k},
          rotatedErrors errors u d.val * a *
            dagger (rotatedErrors errors u d.val) := by
      exact (sum_positive_indices_eq_total wt
        (fun d => rotatedErrors errors u d * a *
          dagger (rotatedErrors errors u d)) hzero).symm
    _ = ∑ d : {k : E // 0 < wt k}, (wt d.val : ℂ) •
          (normalizedSyndromeErrors errors p u wt d * a *
            dagger (normalizedSyndromeErrors errors p u wt d)) := by
      apply Finset.sum_congr rfl
      intro d _
      calc
        rotatedErrors errors u d.val * a *
            dagger (rotatedErrors errors u d.val) =
            (rotatedErrors errors u d.val * p) * a *
              dagger (rotatedErrors errors u d.val * p) :=
          error_sandwich_of_code_support _ p a hstar ha
        _ = (wt d.val : ℂ) •
              (normalizedSyndromeErrors errors p u wt d * a *
                dagger (normalizedSyndromeErrors errors p u wt d)) :=
          (normalizedSyndromeErrors_weighted_sandwich errors p a u wt d).symm

/-- The original Knill-Laflamme overlap equations construct a recovery
    channel on the entire ambient matrix space, including the zero code.
    No orthogonalization, sector weights or isometries are assumed. -/
theorem knillLaflamme_sufficiency
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p)
    (hcomplete : (∑ e, dagger (errors e) * errors e) = 1)
    (hKL : ∃ c : E → E → ℂ, ∀ a b,
      p * dagger (errors a) * errors b * p = c a b • p) :
    ∃ recovery : Mat n →ₗ[ℂ] Mat n,
      CompletelyPositive recovery ∧ TracePreserving recovery ∧
      ∀ ρ : Density n, p * ρ.val * p = ρ.val →
        recovery (krausOutput errors ρ.val) = ρ.val := by
  classical
  by_cases hzero : p = 0
  · subst p
    exact zero_projector_recovery errors
  · obtain ⟨c, hfactor⟩ := hKL
    let cm : Matrix E E ℂ := fun a b => c a b
    have hc : cm.PosSemidef :=
      overlapMatrix_posSemidef errors p hstar hidem hzero cm hfactor
    let u : Matrix E E ℂ := hc.1.eigenvectorUnitary
    let wt : E → ℝ := hc.1.eigenvalues
    have hu : u * uᴴ = 1 :=
      (hc.1.eigenvectorUnitary).property.2
    have hwt : ∀ d, 0 ≤ wt d := hc.eigenvalues_nonneg
    have hdiag : ∀ d e,
        p * dagger (rotatedErrors errors u d) *
          rotatedErrors errors u e * p =
            (Matrix.diagonal (fun k => (wt k : ℂ))) d e • p := by
      intro d e
      have hdiagm : uᴴ * cm * u = Matrix.diagonal (fun k : E => (wt k : ℂ)) :=
        hc.1.star_mul_self_mul_eq_diagonal
      rw [rotatedErrors_overlap errors p cm u hfactor d e, hdiagm]
    have hsum : (∑ d : E, (wt d : ℂ)) = 1 :=
      knillLaflamme_eigenweights_total errors p hzero hidem hcomplete
        cm hfactor hc
    have hsumPos :
        (∑ d : {k : E // 0 < wt k}, (wt d.val : ℂ)) = 1 :=
      positive_eigenweights_sum wt hwt hsum
    let syndrome : {k : E // 0 < wt k} → Mat n :=
      normalizedSyndromeErrors errors p u wt
    have hsupport (d : {k : E // 0 < wt k}) :
        syndrome d * p = syndrome d :=
      normalizedSyndromeErrors_mul_p errors p hidem u wt d
    have horth : ∀ d e : {k : E // 0 < wt k},
        dagger (syndrome d) * syndrome e =
          if d = e then p else 0 :=
      normalizedSyndromeErrors_orthogonal errors p hstar u wt hdiag
    apply recovery_of_orthogonal_decomposition errors syndrome p
      (fun d : {k : E // 0 < wt k} => (wt d.val : ℂ))
      hsupport (fun d e => (horth d e).trans (by split_ifs <;> rfl)) hsumPos
    intro a ha
    exact knillLaflamme_positive_syndrome_decomposition
      errors p hstar u hu wt hwt hdiag a ha

/-- The finite family of composite recovery/error operators has one
    member for each actual recovery Kraus index and original error label. -/
def composedRecoveryErrors {n : ℕ} {E T : Type}
    [Fintype E] [Fintype T]
    (recoveryErrors : T → Mat n) (errors : E → Mat n) :
    T × E → Mat n :=
  fun k => recoveryErrors k.1 * errors k.2

/-- Composition of the two actual Kraus channels is the Kraus channel
    of their indexed operator products, on every input matrix. -/
theorem composedRecoveryErrors_krausOutput
    {n : ℕ} {E T : Type} [Fintype E] [Fintype T]
    (recoveryErrors : T → Mat n) (errors : E → Mat n)
    (a : Mat n) :
    cpMapKraus recoveryErrors (krausOutput errors a) =
      krausOutput (composedRecoveryErrors recoveryErrors errors) a := by
  unfold cpMapKraus krausOutput composedRecoveryErrors dagger
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Every completely positive trace-preserving recovery admits a finite
    Kraus family whose composite physical errors fix all code densities. -/
theorem recovery_induces_composed_kraus
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (recovery : Mat n →ₗ[ℂ] Mat n)
    (hCP : CompletelyPositive recovery)
    (hTP : TracePreserving recovery)
    (hfixed : ∀ ρ : Density n, p * ρ.val * p = ρ.val →
      recovery (krausOutput errors ρ.val) = ρ.val) :
    ∃ K : (Fin n × Fin n) → Mat n,
      (∑ t, dagger (K t) * K t) = 1 ∧
      ∀ ρ : Density n, p * ρ.val * p = ρ.val →
        krausOutput (composedRecoveryErrors K errors) ρ.val = ρ.val := by
  obtain ⟨K, hK⟩ := completelyPositive_kraus recovery hCP
  have hKcomplete : (∑ t, dagger (K t) * K t) = 1 := by
    apply kraus_complete_of_trace_preserving K
    intro a
    rw [← hK a]
    exact hTP a
  refine ⟨K, hKcomplete, ?_⟩
  intro ρ hρ
  rw [← composedRecoveryErrors_krausOutput]
  rw [← hK (krausOutput errors ρ.val)]
  exact hfixed ρ hρ

/-- Scalar action of every actual composite recovery/error operator
    forces the original Knill-Laflamme overlaps. The coefficient matrix
    is constructed from the recovery Kraus amplitudes, not assumed. -/
theorem recovery_composite_scalars_imply_overlaps
    {n : ℕ} {E T : Type} [Fintype E] [Fintype T]
    (errors : E → Mat n) (K : T → Mat n) (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p)
    (hcomplete : (∑ t, dagger (K t) * K t) = 1)
    (γ : T → E → ℂ)
    (hscalar : ∀ t e, K t * errors e * p = γ t e • p) :
    ∃ c : E → E → ℂ, ∀ a b,
      p * dagger (errors a) * errors b * p = c a b • p := by
  refine ⟨fun a b => ∑ t : T, star (γ t a) * γ t b, ?_⟩
  intro a b
  have hprod (t : T) :
      dagger (K t * errors a * p) * (K t * errors b * p) =
        p * dagger (errors a) * dagger (K t) * K t *
          errors b * p := by
    unfold dagger
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, show pᴴ = p from hstar.symm]
    simp only [Matrix.mul_assoc]
  have hterm (t : T) :
      dagger (K t * errors a * p) * (K t * errors b * p) =
        (star (γ t a) * γ t b) • p := by
    rw [hscalar t a, hscalar t b]
    unfold dagger
    rw [Matrix.conjTranspose_smul, show pᴴ = p from hstar.symm]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hidem]
    rw [mul_comm (γ t b) (star (γ t a))]
  calc
    p * dagger (errors a) * errors b * p =
      p * dagger (errors a) *
        (∑ t : T, dagger (K t) * K t) * errors b * p := by
      rw [hcomplete, Matrix.mul_one]
    _ = ∑ t : T, dagger (K t * errors a * p) *
          (K t * errors b * p) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [hprod]
      simp only [Matrix.mul_assoc]
    _ = ∑ t : T, (star (γ t a) * γ t b) • p := by
      apply Finset.sum_congr rfl
      intro t _
      exact hterm t
    _ = (∑ t : T, star (γ t a) * γ t b) • p := by
      rw [Finset.sum_smul]

/-- A native pure vector outer product, including unnormalized vectors. -/
def pureOuter {n : ℕ} (v : Fin n → ℂ) : Mat n :=
  fun i j => v i * star (v j)

/-- The vector is realized as a finite matrix with one output column. -/
def vectorColumn {n : ℕ} (v : Fin n → ℂ) :
    Matrix (Fin n) (Fin 1) ℂ :=
  fun i _ => v i

/-- The pure outer product is an actual positive Gram matrix. -/
theorem pureOuter_eq_column {n : ℕ} (v : Fin n → ℂ) :
    pureOuter v = vectorColumn v * (vectorColumn v)ᴴ := by
  ext i j
  change v i * star (v j) =
    ∑ k : Fin 1, vectorColumn v i k * star (vectorColumn v j k)
  simp only [Fin.sum_univ_one, vectorColumn]

/-- All native pure outer products are positive semidefinite. -/
theorem pureOuter_posSemidef {n : ℕ} (v : Fin n → ℂ) :
    (pureOuter v).PosSemidef := by
  rw [pureOuter_eq_column]
  exact Matrix.posSemidef_self_mul_conjTranspose (vectorColumn v)

/-- The trace of the pure outer product is the sum of its squared norms. -/
theorem pureOuter_trace {n : ℕ} (v : Fin n → ℂ) :
    tr (pureOuter v) = (∑ i : Fin n, Complex.normSq (v i) : ℝ) := by
  change (∑ i : Fin n, v i * star (v i)) =
    ((∑ i : Fin n, Complex.normSq (v i) : ℝ) : ℂ)
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, Complex.mul_conj]

/-- The outer product of a nonzero vector is a nonzero matrix. -/
theorem pureOuter_ne_zero {n : ℕ} (v : Fin n → ℂ)
    (hv : v ≠ 0) : pureOuter v ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  intro hz
  have hentry := congrArg (fun a : Mat n => a i i) hz
  change v i * star (v i) = 0 at hentry
  have hnorm : (Complex.normSq (v i) : ℂ) = 0 := by
    rwa [Complex.star_def, Complex.mul_conj] at hentry
  exact hi (Complex.normSq_eq_zero.mp (Complex.ofReal_injective hnorm))

/-- The native matrix outer product is supported on an orthogonal code
    whenever its generating vector lies in the original code range. -/
theorem pureOuter_code_supported {n : ℕ}
    (p : Mat n) (hstar : p = dagger p)
    (v : Fin n → ℂ) (hv : p *ᵥ v = v) :
    p * pureOuter v * p = pureOuter v := by
  have hc : p * vectorColumn v = vectorColumn v := by
    ext i j
    change (∑ k : Fin n, p i k * v k) = v i
    exact congrFun hv i
  rw [pureOuter_eq_column]
  calc
    p * (vectorColumn v * (vectorColumn v)ᴴ) * p =
      (p * vectorColumn v) * (p * vectorColumn v)ᴴ := by
        rw [Matrix.conjTranspose_mul, show pᴴ = p from hstar.symm]
        simp only [Matrix.mul_assoc]
    _ = vectorColumn v * (vectorColumn v)ᴴ := by
      rw [hc]

/-- Every nonzero positive matrix has strictly positive real trace. -/
theorem posSemidef_trace_re_pos_of_ne_zero {n : ℕ}
    (a : Mat n) (ha : a.PosSemidef) (hne : a ≠ 0) :
    0 < (tr a).re := by
  refine lt_of_le_of_ne (posSemidef_trace_re_nonneg a ha) ?_
  intro hz
  exact hne (posSemidef_eq_zero_of_trace_re_zero a ha hz.symm)

/-- Every nonzero code vector defines a normalized native pure density. -/
noncomputable def normalizedPureDensity {n : ℕ}
    (v : Fin n → ℂ) (hv : v ≠ 0) : Density n := by
  let q : Mat n := pureOuter v
  let t : ℝ := (tr q).re
  have hq : q.PosSemidef := pureOuter_posSemidef v
  have hnq : q ≠ 0 := pureOuter_ne_zero v hv
  have ht : 0 < t := posSemidef_trace_re_pos_of_ne_zero q hq hnq
  let s : ℂ := ((t : ℂ)⁻¹)
  let ρ : Mat n := s • q
  have hsreal : s = ((t⁻¹ : ℝ) : ℂ) := by
    dsimp only [s]
    rw [Complex.ofReal_inv]
  have htrace : tr q = (t : ℂ) := posSemidef_trace_eq_ofReal q hq
  refine ⟨ρ, ?_, ?_⟩
  · apply (psd_iff_posSemidef ρ).mpr
    change (s • q).PosSemidef
    rw [hsreal]
    exact posSemidef_real_smul_gen hq (inv_nonneg.mpr ht.le)
  · change Matrix.trace (s • q) = 1
    rw [Matrix.trace_smul]
    change s * tr q = 1
    rw [htrace]
    dsimp only [s]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne')

/-- The normalized pure density is an explicit scalar multiple
    of the underlying physical vector outer product. -/
theorem normalizedPureDensity_val {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) :
    (normalizedPureDensity v hv).val =
      ((((tr (pureOuter v)).re : ℝ) : ℂ)⁻¹) • pureOuter v := by
  rfl

/-- Every normalized pure density generated in the code is code-supported. -/
theorem normalizedPureDensity_code_supported {n : ℕ}
    (p : Mat n) (hstar : p = dagger p)
    (v : Fin n → ℂ) (hv : v ≠ 0) (hpv : p *ᵥ v = v) :
    p * (normalizedPureDensity v hv).val * p =
      (normalizedPureDensity v hv).val := by
  rw [normalizedPureDensity_val]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [pureOuter_code_supported p hstar v hpv]

/-- Preservation of all supported density matrices implies preservation
    of every unnormalized pure matrix generated by a code vector. -/
theorem krausOutput_pureOuter_of_fixed_code_densities
    {n : ℕ} {T : Type} [Fintype T]
    (errors : T → Mat n) (p : Mat n)
    (hstar : p = dagger p)
    (hfixed : ∀ ρ : Density n, p * ρ.val * p = ρ.val →
      krausOutput errors ρ.val = ρ.val)
    (v : Fin n → ℂ) (hpv : p *ᵥ v = v) :
    krausOutput errors (pureOuter v) = pureOuter v := by
  by_cases hv : v = 0
  · subst v
    have hz : pureOuter (0 : Fin n → ℂ) = 0 := by
      ext i j
      simp only [pureOuter, Pi.zero_apply, zero_mul, Matrix.zero_apply]
    rw [hz, krausOutput_zero]
  · let ρ : Density n := normalizedPureDensity v hv
    have hρsupported : p * ρ.val * p = ρ.val :=
      normalizedPureDensity_code_supported p hstar v hv hpv
    have hρ := hfixed ρ hρsupported
    let t : ℝ := (tr (pureOuter v)).re
    have ht : 0 < t :=
      posSemidef_trace_re_pos_of_ne_zero
        (pureOuter v) (pureOuter_posSemidef v) (pureOuter_ne_zero v hv)
    have htC : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr ht.ne'
    have hρval : ρ.val = ((t : ℂ)⁻¹) • pureOuter v :=
      normalizedPureDensity_val v hv
    rw [hρval] at hρ
    change (krausLinearMap errors) ((t : ℂ)⁻¹ • pureOuter v) =
      (t : ℂ)⁻¹ • pureOuter v at hρ
    rw [(krausLinearMap errors).map_smul] at hρ
    have hscale := congrArg (fun a : Mat n => (t : ℂ) • a) hρ
    simpa only [smul_smul, mul_inv_cancel₀ htC, one_smul]
      using hscale

/-- The native output on an unnormalized pure state is the finite
    Gram matrix of the actual transformed vectors. -/
theorem krausOutput_pureOuter_apply
    {n : ℕ} {T : Type} [Fintype T]
    (errors : T → Mat n) (v : Fin n → ℂ)
    (i j : Fin n) :
    (krausOutput errors (pureOuter v)) i j =
      ∑ t : T, (errors t *ᵥ v) i *
        star ((errors t *ᵥ v) j) := by
  unfold krausOutput
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [pureOuter_eq_column]
  calc
    (errors t * (vectorColumn v * (vectorColumn v)ᴴ) *
        dagger (errors t)) i j =
      ((errors t * vectorColumn v) *
        (errors t * vectorColumn v)ᴴ) i j := by
      unfold dagger
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = (errors t *ᵥ v) i * star ((errors t *ᵥ v) j) := by
      rw [Matrix.mul_apply]
      simp only [Fin.sum_univ_one, Matrix.conjTranspose_apply]
      rfl

/-- Each Kraus error fixes the line of a vector whenever the
    complete Kraus channel fixes the corresponding rank-one matrix.
    The proof uses the nonnegative sum of squared coordinate minors. -/
theorem kraus_pure_fixed_cross
    {n : ℕ} {T : Type} [Fintype T]
    (errors : T → Mat n) (v : Fin n → ℂ)
    (hfixed : krausOutput errors (pureOuter v) = pureOuter v)
    (t : T) (i j : Fin n) :
    v j * (errors t *ᵥ v) i =
      v i * (errors t *ᵥ v) j := by
  let z : T → Fin n → ℂ := fun t i => (errors t *ᵥ v) i
  let δ : T → ℂ := fun t => v j * z t i - v i * z t j
  have hGram (r s : Fin n) :
      (∑ t : T, z t r * star (z t s)) =
        v r * star (v s) := by
    have h := congrFun (congrFun hfixed r) s
    rw [krausOutput_pureOuter_apply] at h
    exact h
  have hnorm (k : T) :
      ((Complex.normSq (δ k) : ℝ) : ℂ) = δ k * star (δ k) := by
    rw [Complex.star_def, Complex.mul_conj]
  have hexpand (k : T) :
      δ k * star (δ k) =
        (v j * star (v j)) * (z k i * star (z k i)) +
        (v i * star (v i)) * (z k j * star (z k j)) -
        (v j * star (v i)) * (z k i * star (z k j)) -
        (v i * star (v j)) * (z k j * star (z k i)) := by
    dsimp only [δ]
    rw [star_sub]
    simp only [StarMul.star_mul]
    ring
  have hsum :
      (∑ k : T, ((Complex.normSq (δ k) : ℝ) : ℂ)) = 0 := by
    calc
      _ = ∑ k : T, δ k * star (δ k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hnorm k
      _ = ∑ k : T,
          ((v j * star (v j)) * (z k i * star (z k i)) +
          (v i * star (v i)) * (z k j * star (z k j)) -
          (v j * star (v i)) * (z k i * star (z k j)) -
          (v i * star (v j)) * (z k j * star (z k i))) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hexpand k
      _ = (v j * star (v j)) *
            (∑ k : T, z k i * star (z k i)) +
          (v i * star (v i)) *
            (∑ k : T, z k j * star (z k j)) -
          (v j * star (v i)) *
            (∑ k : T, z k i * star (z k j)) -
          (v i * star (v j)) *
            (∑ k : T, z k j * star (z k i)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
      _ = 0 := by
        rw [hGram i i, hGram j j, hGram i j, hGram j i]
        ring
  have hreal : (∑ k : T, Complex.normSq (δ k)) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_zero]
    exact hsum
  have hle : Complex.normSq (δ t) ≤
      ∑ k : T, Complex.normSq (δ k) :=
    Finset.single_le_sum
      (fun k _ => Complex.normSq_nonneg (δ k))
      (Finset.mem_univ t)
  have hzero : Complex.normSq (δ t) = 0 := by
    apply le_antisymm
    · simpa only [hreal] using hle
    · exact Complex.normSq_nonneg _
  have hdelta : δ t = 0 := Complex.normSq_eq_zero.mp hzero
  exact sub_eq_zero.mp hdelta

/-!
## Necessity: a recovery forces one scalar per composite operator on the code

Every code vector is mapped by a composite recovery-error operator to a multiple of
itself. Polarization against one fixed nonzero column of the code projector makes that
multiple a single scalar on the whole code. The scalars then give the overlap
coefficients through the completeness of the recovery Kraus family.
-/

/-- Each column of an idempotent code projector is a code vector. -/
theorem codeProjector_column_fixed {n : ℕ} (p : Mat n) (hidem : p * p = p) (c : Fin n) :
    p *ᵥ (fun k => p k c) = fun k => p k c := by
  funext r
  have h := congrFun (congrFun hidem r) c
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- A matrix whose action on every code vector has vanishing two-by-two minors against
that vector acts on the code as one scalar multiple of the code projector. -/
theorem scalar_on_code_of_cross {n : ℕ} (M p : Mat n) (hidem : p * p = p)
    (hcross : ∀ v : Fin n → ℂ, p *ᵥ v = v →
      ∀ i j, v j * (M *ᵥ v) i = v i * (M *ᵥ v) j) :
    ∃ γ : ℂ, M * p = γ • p := by
  by_cases hp : p = 0
  · exact ⟨0, by rw [hp, Matrix.mul_zero, zero_smul]⟩
  obtain ⟨i0, c0, hpc⟩ : ∃ i c, p i c ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hp (Matrix.ext hn)
  obtain ⟨v0, hv0def⟩ : ∃ v0 : Fin n → ℂ, v0 = fun k => p k c0 := ⟨_, rfl⟩
  have hv0 : p *ᵥ v0 = v0 := by
    rw [hv0def]
    exact codeProjector_column_fixed p hidem c0
  have hv0i : v0 i0 ≠ 0 := by
    rw [hv0def]
    exact hpc
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, γ = (M *ᵥ v0) i0 / v0 i0 := ⟨_, rfl⟩
  have hcancel : ∀ (X y : ℂ), X / v0 i0 * y * v0 i0 = X * y := by
    intro X y
    rw [mul_assoc, mul_comm y (v0 i0), ← mul_assoc, div_mul_cancel₀ _ hv0i]
  have hMv0 : ∀ i, (M *ᵥ v0) i = γ * v0 i := by
    intro i
    apply mul_right_cancel₀ hv0i
    have h := hcross v0 hv0 i i0
    rw [hγ, hcancel]
    linear_combination h
  have hcode : ∀ w : Fin n → ℂ, p *ᵥ w = w → M *ᵥ w = γ • w := by
    intro w hw
    have hu : p *ᵥ (w + v0) = w + v0 := by
      rw [Matrix.mulVec_add, hw, hv0]
    have hpol : ∀ i j, w j * (M *ᵥ v0) i + v0 j * (M *ᵥ w) i =
        w i * (M *ᵥ v0) j + v0 i * (M *ᵥ w) j := by
      intro i j
      have h1 := hcross (w + v0) hu i j
      have h2 := hcross w hw i j
      have h3 := hcross v0 hv0 i j
      simp only [Matrix.mulVec_add, Pi.add_apply] at h1
      linear_combination h1 - h2 - h3
    obtain ⟨κ, hdecomp⟩ : ∃ κ : ℂ, ∀ i, (M *ᵥ w) i = γ * w i + κ * v0 i := by
      refine ⟨((M *ᵥ w) i0 - γ * w i0) / v0 i0, fun i => ?_⟩
      have key : ((M *ᵥ w) i - γ * w i) * v0 i0 = ((M *ᵥ w) i0 - γ * w i0) * v0 i := by
        have h := hpol i i0
        rw [hMv0 i, hMv0 i0] at h
        linear_combination h
      apply mul_right_cancel₀ hv0i
      rw [add_mul, hcancel]
      linear_combination key
    by_cases hpar : ∀ i j, w j * v0 i = w i * v0 j
    · have hw' : w = (w i0 / v0 i0) • v0 := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        apply mul_right_cancel₀ hv0i
        rw [hcancel]
        exact (hpar i i0).symm
      have hMw : M *ᵥ w = (w i0 / v0 i0) • (M *ᵥ v0) := by
        conv_lhs => rw [hw']
        exact Matrix.mulVec_smul M (w i0 / v0 i0) v0
      funext i
      have hwi : w i = w i0 / v0 i0 * v0 i := by
        have h := congrFun hw' i
        simpa only [Pi.smul_apply, smul_eq_mul] using h
      rw [hMw]
      simp only [Pi.smul_apply, smul_eq_mul, hMv0 i]
      rw [hwi]
      ring
    · push_neg at hpar
      obtain ⟨i, j, hij⟩ := hpar
      have hR := hcross w hw i j
      rw [hdecomp i, hdecomp j] at hR
      have hκ : κ = 0 := by
        have h : κ * (w j * v0 i - w i * v0 j) = 0 := by
          linear_combination hR
        rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hij
      funext k
      rw [hdecomp k, hκ]
      simp only [Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]
  refine ⟨γ, Matrix.ext fun r c => ?_⟩
  have h := congrFun (hcode (fun k => p k c) (codeProjector_column_fixed p hidem c)) r
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply] using h

/-- Necessity: a completely positive trace-preserving recovery of every code density
forces the Knill-Laflamme overlap equations, with coefficients built from the recovery
Kraus amplitudes. -/
theorem knillLaflamme_necessity {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n) (hstar : p = dagger p) (hidem : p * p = p)
    (recovery : Mat n →ₗ[ℂ] Mat n) (hCP : CompletelyPositive recovery)
    (hTP : TracePreserving recovery)
    (hfixed : ∀ ρ : Density n, p * ρ.val * p = ρ.val →
      recovery (krausOutput errors ρ.val) = ρ.val) :
    ∃ c : E → E → ℂ, ∀ a b, p * dagger (errors a) * errors b * p = c a b • p := by
  obtain ⟨K, hKcomplete, hcomp⟩ :=
    recovery_induces_composed_kraus errors p recovery hCP hTP hfixed
  have hscalar : ∀ t e, ∃ γ : ℂ, K t * errors e * p = γ • p := by
    intro t e
    apply scalar_on_code_of_cross (K t * errors e) p hidem
    intro v hv i j
    have hpure := krausOutput_pureOuter_of_fixed_code_densities
      (composedRecoveryErrors K errors) p hstar hcomp v hv
    exact kraus_pure_fixed_cross (composedRecoveryErrors K errors) v hpure (t, e) i j
  choose γ hγ using hscalar
  exact recovery_composite_scalars_imply_overlaps errors K p hstar hidem hKcomplete γ hγ

/-- The Knill-Laflamme equivalence holds on every finite matrix size, the empty size
included; the specification's premise `0 < n` is therefore not load-bearing. -/
theorem knillLaflamme_equivalence {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n) (hstar : p = dagger p) (hidem : p * p = p)
    (hcomplete : (∑ e, dagger (errors e) * errors e) = 1) :
    (∃ c : E → E → ℂ, ∀ a b,
        p * dagger (errors a) * errors b * p = c a b • p) ↔
      ∃ recovery : Mat n →ₗ[ℂ] Mat n,
        CompletelyPositive recovery ∧ TracePreserving recovery ∧
        ∀ ρ : Density n, p * ρ.val * p = ρ.val →
          recovery (krausOutput errors ρ.val) = ρ.val := by
  constructor
  · intro hKL
    exact knillLaflamme_sufficiency errors p hstar hidem hcomplete hKL
  · rintro ⟨recovery, hCP, hTP, hfixed⟩
    exact knillLaflamme_necessity errors p hstar hidem recovery hCP hTP hfixed

/-- M5.5: the Knill-Laflamme recovery equivalence on the finite matrix carrier. -/
theorem knillLaflammeGoal : KnillLaflammeGoal := by
  intro n E _ errors p _ hstar hidem hcomplete
  exact knillLaflamme_equivalence errors p hstar hidem hcomplete


end OperatorKO7.Meta.BoundaryObserver.ReconstructionKnillLaflamme

end
