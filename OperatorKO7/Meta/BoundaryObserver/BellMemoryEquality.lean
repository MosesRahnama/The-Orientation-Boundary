import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction

/-!
# Pauli memory equality at the maximally entangled state

Manuscript: Proposition `prop:bell-memory-equality`.

For the state `Φ_d = d^{-1/2} ∑ⱼ |jj⟩` of two `d`-level systems, `H(A | B) = -log₂ d`; for every
orthonormal basis of `A`, given by the columns of a unitary, the classical-quantum output of the
basis test with its outcome kept in a register `R` has `H(R | B) = 0`. Every pair of bases has
largest squared overlap `c ≥ 1/d`, with equality exactly when every squared overlap is `1/d`, so
`H(U | B) + H(V | B) = 0 ≥ log₂(1/c) + H(A | B)` with equality exactly then. At `d = 2` the Pauli
tests `Z` and `X` reach equality with `c = 1/2` and `H(A | B) = -1`.

The four entropies come from one lemma: a Hermitian matrix of trace one with `a * a = c • a` has
eigenvalues in `{0, c}` and entropy `-log c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix
open scoped BigOperators ComplexOrder
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Thermal

namespace OperatorKO7.Meta.BoundaryObserver.BellMemoryEquality

section Spectral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem rotate_one' (a : Matrix ι ι ℂ) : rotate (1 : Matrix.unitaryGroup ι ℂ) a = a := by
  simp [rotate]

theorem spectralLift_injective (u : Matrix.unitaryGroup ι ℂ) {p q : ι → ℝ}
    (h : spectralLift u p = spectralLift u q) : p = q := by
  have h1 := congrArg (rotate u⁻¹) h
  rw [rotate_spectralLift, rotate_spectralLift, inv_mul_cancel, spectralLift, spectralLift,
    rotate_one', rotate_one'] at h1
  funext i
  have h2 := congrFun (congrFun h1 i) i
  simp only [realDiagonal, Matrix.diagonal_apply_eq] at h2
  exact_mod_cast h2

theorem realDiagonal_smul (c : ℝ) (p : ι → ℝ) :
    realDiagonal (fun i => c * p i) = (c : ℂ) • realDiagonal p := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [realDiagonal]
  · simp [realDiagonal, Matrix.diagonal_apply_ne _ h]

theorem smul_spectralLift (u : Matrix.unitaryGroup ι ℂ) (c : ℝ) (p : ι → ℝ) :
    (c : ℂ) • spectralLift u p = spectralLift u (fun i => c * p i) := by
  rw [spectralLift, spectralLift, realDiagonal_smul, rotate, rotate, Matrix.mul_smul,
    Matrix.smul_mul]

/-- A Hermitian matrix with `a * a = c • a` has every eigenvalue in `{0, c}`. -/
theorem eigenvalues_of_sq_eq_smul {a : Matrix ι ι ℂ} (ha : a.IsHermitian) {c : ℝ}
    (hsq : a * a = (c : ℂ) • a) (i : ι) : ha.eigenvalues i = 0 ∨ ha.eigenvalues i = c := by
  have hrep := spectralLift_eigenvalues ha
  have h : spectralLift ha.eigenvectorUnitary (fun j => ha.eigenvalues j * ha.eigenvalues j) =
      spectralLift ha.eigenvectorUnitary (fun j => c * ha.eigenvalues j) := by
    calc spectralLift ha.eigenvectorUnitary (fun j => ha.eigenvalues j * ha.eigenvalues j)
        = spectralLift ha.eigenvectorUnitary ha.eigenvalues *
            spectralLift ha.eigenvectorUnitary ha.eigenvalues := (spectralLift_mul _ _ _).symm
      _ = a * a := by rw [hrep]
      _ = (c : ℂ) • a := hsq
      _ = (c : ℂ) • spectralLift ha.eigenvectorUnitary ha.eigenvalues := by rw [hrep]
      _ = _ := smul_spectralLift _ _ _
  have hi := congrFun (spectralLift_injective _ h) i
  have hz : ha.eigenvalues i * (ha.eigenvalues i - c) = 0 := by
    simp only at hi
    linear_combination hi
  rcases mul_eq_zero.1 hz with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- **A scaled projector of trace one has entropy `-log c`.** -/
theorem entropy_of_sq_eq_smul {a : Matrix ι ι ℂ} (ha : a.IsHermitian) {c : ℝ}
    (hsq : a * a = (c : ℂ) • a) (htr : a.trace = 1) : entropy a = -Real.log c := by
  rw [entropy_eq_eigenvalues ha]
  have hterm : ∀ i, Real.negMulLog (ha.eigenvalues i) = -Real.log c * ha.eigenvalues i := by
    intro i
    rcases eigenvalues_of_sq_eq_smul ha hsq i with h | h
    · rw [h, Real.negMulLog_zero, mul_zero]
    · rw [h, Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, eigenvalues_sum_trace ha, htr,
    Complex.one_re, mul_one]

/-- The scaled identity `c • 1` with `c = 1/d` is the maximally mixed state, of entropy `log d`. -/
theorem entropy_maximallyMixed [Nonempty ι] :
    entropy (((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) =
      Real.log (Fintype.card ι) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hherm : ((((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  rw [entropy_of_sq_eq_smul hherm (c := 1 / (Fintype.card ι : ℝ))]
  · rw [one_div, Real.log_inv, neg_neg]
  · rw [Matrix.smul_mul, Matrix.one_mul]
  · rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    push_cast
    field_simp

end Spectral

section States

variable (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The amplitude `d^{-1/2}`. -/
noncomputable def amp : ℝ := (Real.sqrt (Fintype.card ι))⁻¹

theorem amp_sq : amp ι * amp ι = 1 / (Fintype.card ι : ℝ) := by
  have hd : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rw [amp, ← mul_inv, Real.mul_self_sqrt hd, one_div]

/-- The maximally entangled vector `Φ_d = d^{-1/2} ∑ⱼ |jj⟩`. -/
noncomputable def maxEnt : ι × ι → ℂ := fun p => if p.1 = p.2 then (amp ι : ℂ) else 0

/-- The pure state `|Φ_d⟩⟨Φ_d|`. -/
noncomputable def pureState : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.vecMulVec (maxEnt ι) (star (maxEnt ι))

theorem maxEnt_normSq_sum : ∑ p, star (maxEnt ι p) * maxEnt ι p = 1 := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : ι, ∑ b : ι, star (maxEnt ι (a, b)) * maxEnt ι (a, b) =
      ((amp ι * amp ι : ℝ) : ℂ) := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp [maxEnt]
    · intro b _ hb
      simp [maxEnt, Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [Finset.sum_congr rfl fun a _ => hinner a, Finset.sum_const, Finset.card_univ, amp_sq,
    nsmul_eq_mul]
  push_cast
  field_simp

theorem pureState_hermitian : (pureState ι).IsHermitian := by
  ext p q
  simp [pureState, Matrix.vecMulVec_apply, mul_comm]

theorem pureState_sq : pureState ι * pureState ι = ((1 : ℝ) : ℂ) • pureState ι := by
  ext p q
  simp only [pureState, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul]
  have h : ∑ r, maxEnt ι p * star (maxEnt ι r) * (maxEnt ι r * star (maxEnt ι q)) =
      maxEnt ι p * star (maxEnt ι q) * ∑ r, star (maxEnt ι r) * maxEnt ι r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [h, maxEnt_normSq_sum, mul_one]

theorem pureState_trace : (pureState ι).trace = 1 := by
  rw [Matrix.trace, ← maxEnt_normSq_sum ι]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [pureState, Matrix.vecMulVec_apply, mul_comm]

/-- `S(Φ_d) = 0`. -/
theorem entropy_pureState : entropy (pureState ι) = 0 := by
  rw [entropy_of_sq_eq_smul (pureState_hermitian ι) (pureState_sq ι) (pureState_trace ι),
    Real.log_one, neg_zero]

/-- The marginal of `Φ_d` on `B` is the maximally mixed state `1/d`. -/
theorem marginal_pureState :
    marginalRight (pureState ι) =
      (((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) := by
  ext b b'
  simp only [marginalRight, pureState, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · by_cases h : b = b'
    · subst h
      simp only [maxEnt, if_true, mul_one]
      rw [← amp_sq ι]
      push_cast
      simp
    · simp [maxEnt, h]
  · intro a _ ha
    simp [maxEnt, ha]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- `H(A | B) = S(Φ_d) - S(Φ_B) = -log d` (nats). -/
theorem condEntropy_pureState :
    entropy (pureState ι) - entropy (marginalRight (pureState ι)) =
      -Real.log (Fintype.card ι) := by
  rw [entropy_pureState, marginal_pureState, entropy_maximallyMixed, zero_sub]

/-- The classical-quantum output of the test of the basis of columns of `U` on `A`, with the
outcome kept in the register `R`: `σ_{RB} = ∑ᵣ |r⟩⟨r| ⊗ (⟨uᵣ| ⊗ I) ρ (|uᵣ⟩ ⊗ I)`. -/
noncomputable def basisRecord (ρ : Matrix (ι × ι) (ι × ι) ℂ) (U : Matrix ι ι ℂ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  fun p q => if p.1 = q.1 then ∑ a, ∑ a', star (U a p.1) * ρ (a, p.2) (a', q.2) * U a' p.1
    else 0

/-- The output at `Φ_d`: `(1/d) ∑ᵣ |r⟩⟨r| ⊗ |ūᵣ⟩⟨ūᵣ|`. -/
noncomputable def cqState (U : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  fun p q => if p.1 = q.1 then ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) *
    (star (U p.2 p.1) * U q.2 p.1) else 0

theorem basisRecord_pureState (U : Matrix ι ι ℂ) : basisRecord ι (pureState ι) U = cqState ι U := by
  ext p q
  simp only [basisRecord, cqState]
  split_ifs with h
  · rw [Finset.sum_eq_single p.2]
    · rw [Finset.sum_eq_single q.2]
      · simp only [pureState, Matrix.vecMulVec_apply, Pi.star_apply, maxEnt, if_true]
        rw [← amp_sq ι]
        push_cast
        simp only [Complex.star_def, Complex.conj_ofReal]
        ring
      · intro a' _ ha'
        simp [pureState, Matrix.vecMulVec_apply, maxEnt, ha']
      · intro hq
        exact absurd (Finset.mem_univ _) hq
    · intro a _ ha
      exact Finset.sum_eq_zero fun a' _ => by
        simp [pureState, Matrix.vecMulVec_apply, maxEnt, ha]
    · intro hp
      exact absurd (Finset.mem_univ _) hp
  · rfl

variable {ι}

theorem unitary_col (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (r s : ι) :
    ∑ b, star (U b r) * U b s = if r = s then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) r) s
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

theorem unitary_row (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (b b' : ι) :
    ∑ r, U b r * star (U b' r) = if b = b' then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) b) b'
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

theorem cqState_hermitian (U : Matrix ι ι ℂ) : (cqState ι U).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, cqState]
  by_cases h : p.1 = q.1
  · rw [if_pos h.symm, if_pos h, h]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem cqState_sq (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    cqState ι U * cqState ι U = ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) • cqState ι U := by
  ext p q
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, cqState, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p.1]
  · by_cases h : p.1 = q.1
    · simp only [if_true, if_pos h]
      have hcol := unitary_col U hU p.1 p.1
      rw [if_pos rfl] at hcol
      have : ∑ b, ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) * (star (U p.2 p.1) * U b p.1) *
          (((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) * (star (U b p.1) * U q.2 p.1)) =
          ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) * (((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) *
            (star (U p.2 p.1) * U q.2 p.1)) * ∑ b, star (U b p.1) * U b p.1 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, hcol, mul_one, h]
    · simp only [if_true, if_neg h, mul_zero, Finset.sum_const_zero]
  · intro r _ hr
    exact Finset.sum_eq_zero fun b _ => by simp [Ne.symm hr]
  · intro hr
    exact absurd (Finset.mem_univ _) hr

theorem cqState_trace (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (cqState ι U).trace = 1 := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag_apply]
  have hr : ∀ r : ι, ∑ b, cqState ι U (r, b) (r, b) = ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) := by
    intro r
    simp only [cqState, if_true]
    rw [← Finset.mul_sum]
    have hcol := unitary_col U hU r r
    rw [if_pos rfl] at hcol
    rw [hcol, mul_one]
  rw [Finset.sum_congr rfl fun r _ => hr r, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  field_simp

theorem marginal_cqState (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    marginalRight (cqState ι U) =
      (((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) := by
  ext b b'
  simp only [marginalRight, cqState, if_true, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hrow := unitary_row U hU b' b
  have : ∑ r, star (U b r) * U b' r = ∑ r, U b' r * star (U b r) :=
    Finset.sum_congr rfl fun r _ => mul_comm _ _
  rw [this, hrow]
  by_cases h : b = b'
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- **Every basis test at `Φ_d` has `H(R | B) = 0`.** -/
theorem condEntropy_basisRecord (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    entropy (basisRecord ι (pureState ι) U) -
      entropy (marginalRight (basisRecord ι (pureState ι) U)) = 0 := by
  rw [basisRecord_pureState, marginal_cqState U hU, entropy_maximallyMixed,
    entropy_of_sq_eq_smul (cqState_hermitian U) (cqState_sq U hU) (cqState_trace U hU),
    one_div, Real.log_inv, neg_neg, sub_self]

end States

section Overlap

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The largest squared overlap `c = max_{x,z} |⟨u_x | v_z⟩|²` of two bases. -/
noncomputable def maxOverlap (U V : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun p : ι × ι => Complex.normSq ((star U * V) p.1 p.2)

theorem overlap_row_sum (U V : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) (x : ι) :
    ∑ z, Complex.normSq ((star U * V) x z) = 1 := by
  have hM : star U * V ∈ Matrix.unitaryGroup ι ℂ :=
    Submonoid.mul_mem _ (unitary.star_mem hU) hV
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hM) x) x
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, if_true] at h
  have h2 : ((∑ z, Complex.normSq ((star U * V) x z) : ℝ) : ℂ) = 1 := by
    rw [← h, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [show (star U * V) x z = ∑ x_1, star (U x_1 x) * V x_1 z by
      simp [Matrix.mul_apply, Matrix.star_apply], Complex.star_def, Complex.mul_conj]
  exact_mod_cast h2

/-- `c ≥ 1/d`. -/
theorem one_div_card_le_maxOverlap (U V : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) : 1 / (Fintype.card ι : ℝ) ≤ maxOverlap U V := by
  obtain ⟨x⟩ := (inferInstance : Nonempty ι)
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ z, Complex.normSq ((star U * V) x z) < 1 / (Fintype.card ι : ℝ) := fun z =>
    lt_of_le_of_lt (Finset.le_sup' (fun p : ι × ι => Complex.normSq ((star U * V) p.1 p.2))
      (Finset.mem_univ (x, z))) hcon
  have hsum : ∑ z, Complex.normSq ((star U * V) x z) <
      ∑ _z : ι, 1 / (Fintype.card ι : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun z _ => hlt z
  rw [overlap_row_sum U V hU hV x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one_div_cancel hd.ne'] at hsum
  exact lt_irrefl _ hsum

/-- `c = 1/d` exactly when every squared overlap is `1/d`. -/
theorem maxOverlap_eq_iff (U V : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) :
    maxOverlap U V = 1 / (Fintype.card ι : ℝ) ↔
      ∀ x z, Complex.normSq ((star U * V) x z) = 1 / (Fintype.card ι : ℝ) := by
  constructor
  · intro h x z
    have hle : ∀ z', Complex.normSq ((star U * V) x z') ≤ 1 / (Fintype.card ι : ℝ) := fun z' => by
      rw [← h]
      exact Finset.le_sup' (fun p : ι × ι => Complex.normSq ((star U * V) p.1 p.2))
        (Finset.mem_univ (x, z'))
    have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hsum : ∑ z', Complex.normSq ((star U * V) x z') = ∑ _z' : ι, 1 / (Fintype.card ι : ℝ) := by
      rw [overlap_row_sum U V hU hV x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    exact (Finset.sum_eq_sum_iff_of_le fun z' _ => hle z').1 hsum z (Finset.mem_univ z)
  · intro h
    refine le_antisymm ?_ (one_div_card_le_maxOverlap U V hU hV)
    exact Finset.sup'_le _ _ fun p _ => (h p.1 p.2).le

end Overlap

section Bits

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Conditional entropy `H(· | B) = S(σ) - S(σ_B)` in bits. -/
noncomputable def condBits (σ : Matrix (ι × ι) (ι × ι) ℂ) : ℝ :=
  (entropy σ - entropy (marginalRight σ)) / Real.log 2

/-- **Proposition `prop:bell-memory-equality`.** At `Φ_d`: `H(A | B) = -log₂ d`, every pair of
bases has `H(U | B) + H(V | B) = 0 ≥ log₂(1/c) + H(A | B)`, with equality exactly when every
squared overlap is `1/d`. -/
theorem memory_uncertainty (U V : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) :
    condBits (pureState ι) = -Real.logb 2 (Fintype.card ι) ∧
    condBits (basisRecord ι (pureState ι) U) + condBits (basisRecord ι (pureState ι) V) = 0 ∧
    Real.logb 2 (1 / maxOverlap U V) + condBits (pureState ι) ≤
      condBits (basisRecord ι (pureState ι) U) + condBits (basisRecord ι (pureState ι) V) ∧
    (Real.logb 2 (1 / maxOverlap U V) + condBits (pureState ι) =
      condBits (basisRecord ι (pureState ι) U) + condBits (basisRecord ι (pureState ι) V) ↔
        ∀ x z, Complex.normSq ((star U * V) x z) = 1 / (Fintype.card ι : ℝ)) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hA : condBits (pureState ι) = -Real.logb 2 (Fintype.card ι) := by
    rw [condBits, condEntropy_pureState, Real.logb, neg_div]
  have hUV : condBits (basisRecord ι (pureState ι) U) +
      condBits (basisRecord ι (pureState ι) V) = 0 := by
    rw [condBits, condBits, condEntropy_basisRecord U hU, condEntropy_basisRecord V hV, zero_div,
      add_zero]
  have hc := one_div_card_le_maxOverlap U V hU hV
  have hcpos : 0 < maxOverlap U V := lt_of_lt_of_le (by positivity) hc
  have hinv : 1 / maxOverlap U V ≤ Fintype.card ι := by
    rw [div_le_iff₀ hcpos]
    rw [div_le_iff₀ hd] at hc
    linarith
  refine ⟨hA, hUV, ?_, ?_⟩
  · rw [hA, hUV]
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hinv
    linarith
  · rw [hA, hUV, ← maxOverlap_eq_iff U V hU hV]
    constructor
    · intro h
      have hlog : Real.logb 2 (1 / maxOverlap U V) = Real.logb 2 (Fintype.card ι) := by linarith
      have := Real.logb_injOn_pos (by norm_num : (1 : ℝ) < 2)
        (Set.mem_Ioi.2 (by positivity : (0 : ℝ) < 1 / maxOverlap U V)) (Set.mem_Ioi.2 hd) hlog
      rw [this.symm, one_div_one_div]
    · intro h
      rw [h, one_div_one_div]
      ring

/-! ## The Pauli tests at `d = 2` -/

/-- The Hadamard matrix, whose columns are the eigenvectors of the Pauli test `X`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt 2)⁻¹ : ℝ), ((Real.sqrt 2)⁻¹ : ℝ); ((Real.sqrt 2)⁻¹ : ℝ), -((Real.sqrt 2)⁻¹ : ℝ)]

theorem sqrt_two_inv_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

theorem hadamard_unitary : hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, sqrt_two_inv_sq]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.conj_ofReal] <;> rw [h] <;> norm_num

theorem hadamard_overlap (x z : Fin 2) :
    Complex.normSq ((star (1 : Matrix (Fin 2) (Fin 2) ℂ) * hadamard) x z) = 1 / 2 := by
  rw [star_one, Matrix.one_mul]
  fin_cases x <;> fin_cases z <;>
    simp [hadamard, Complex.normSq_ofReal, sqrt_two_inv_sq]

/-- **The Pauli equality.** At the Bell state, `H(A | B) = -1`, `H(Z | B) + H(X | B) = 0`, the
overlap of the eigenbases of `Z` and `X` is `1/2`, and `H(Z | B) + H(X | B) = log₂(1/c) + H(A | B)`. -/
theorem pauli_memory_equality :
    maxOverlap (1 : Matrix (Fin 2) (Fin 2) ℂ) hadamard = 1 / 2 ∧
    condBits (pureState (Fin 2)) = -1 ∧
    condBits (basisRecord (Fin 2) (pureState (Fin 2)) 1) +
      condBits (basisRecord (Fin 2) (pureState (Fin 2)) hadamard) = 0 ∧
    Real.logb 2 (1 / maxOverlap (1 : Matrix (Fin 2) (Fin 2) ℂ) hadamard) +
      condBits (pureState (Fin 2)) =
        condBits (basisRecord (Fin 2) (pureState (Fin 2)) 1) +
          condBits (basisRecord (Fin 2) (pureState (Fin 2)) hadamard) := by
  have hU : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := Submonoid.one_mem _
  obtain ⟨hA, hUV, -, heq⟩ := memory_uncertainty 1 hadamard hU hadamard_unitary
  have hall : ∀ x z : Fin 2, Complex.normSq ((star (1 : Matrix (Fin 2) (Fin 2) ℂ) * hadamard) x z)
      = 1 / (Fintype.card (Fin 2) : ℝ) := fun x z => by
    rw [hadamard_overlap, Fintype.card_fin]
    norm_num
  have hc := (maxOverlap_eq_iff 1 hadamard hU hadamard_unitary).2 hall
  rw [Fintype.card_fin] at hc hA
  refine ⟨by rw [hc]; norm_num, ?_, hUV, heq.2 hall⟩
  rw [hA]
  norm_num [Real.logb_self_eq_one]

end Bits

end OperatorKO7.Meta.BoundaryObserver.BellMemoryEquality
