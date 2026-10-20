import Mathlib

/-!
# A finite dephasing (decoherence) channel (Reverse-Bridge QM substrate, target a)

Mechanizes the finite, discrete decoherence map the reverse-bridge program imports as an analogy: the
pure-dephasing channel `Φ_γ(ρ) = γ • ρ + (1-γ) • diag(ρ)` on a finite complex matrix space, with
`0 ≤ γ ≤ 1`. It is the convex combination of the identity and the complete-dephasing (diagonal)
map `ρ ↦ diag(ρ) = ∑_i P_i ρ P_i`, so it is completely positive by construction (Kraus operators
`{√γ I} ∪ {√(1-γ) P_i}`); the Lean theorems below prove the operationally substantive content:

* trace preservation (`dephase_trace`): `Tr Φ_γ(ρ) = Tr ρ` (the TP of CPTP);
* positivity preservation (`dephase_posSemidef`): `ρ ≥ 0 → Φ_γ(ρ) ≥ 0` (the P of CPTP), so the channel
  maps density matrices to density matrices;
* off-diagonal coherence decay (`dephase_iter_offdiag`, `dephase_iter_offdiag_tendsto`): the off-diagonal
  entries are multiplied by `γ^k` under `k` iterations and tend to `0` for `0 ≤ γ < 1`;
* the pointer-basis fixed-point theorem (`dephase_fixed_iff`): for `γ ≠ 1`, `Φ_γ(ρ) = ρ` iff `ρ` is
  diagonal in the pointer basis (all off-diagonals vanish).

Complements `Meta/QuantumBoundary/DensityMatrixPOVM.lean` (the static mixed-state object); here the object
is the decohering dynamics that drives a state to its pointer-basis diagonal.

## Audit slots
- Relation: finite-dimensional complex matrix algebra (a linear CPTP map), not a rewriting relation.
- Closure: `propext`, `Classical.choice`, `Quot.sound`.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`/`@[csimp]`. Non-vacuity: a concrete `2x2` state whose
  off-diagonal decays as `γ^k`, and a diagonal fixed point.
- Scope: TP + positivity preservation + off-diagonal decay + pointer-basis fixed point; complete
  positivity is structural (the Kraus form), not separately formalized as a Choi-matrix theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.QuantumBoundary.FiniteDecoherenceChannel

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- The **finite dephasing (decoherence) channel** with rate `γ`:
`Φ_γ(ρ) = γ • ρ + (1-γ) • diag(ρ)`, the convex mix of the identity and the diagonal (pointer-basis)
projection. -/
noncomputable def dephase (γ : ℝ) (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (γ : ℂ) • ρ + ((1 - γ : ℝ) : ℂ) • Matrix.diagonal (Matrix.diag ρ)

/-- Off the diagonal the channel just rescales the coherence by `γ`. -/
theorem dephase_apply_offdiag {γ : ℝ} {ρ : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (hij : i ≠ j) :
    (dephase γ ρ) i j = (γ : ℂ) * ρ i j := by
  unfold dephase
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij]
  simp

/-- On the diagonal the channel is the identity (the pointer-basis populations are preserved). -/
theorem dephase_apply_diag {γ : ℝ} {ρ : Matrix (Fin n) (Fin n) ℂ} (i : Fin n) :
    (dephase γ ρ) i i = ρ i i := by
  unfold dephase
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
    Matrix.diag_apply, smul_eq_mul, smul_eq_mul]
  push_cast; ring

/-- **Trace preservation** (the TP of CPTP): `Tr Φ_γ(ρ) = Tr ρ`. -/
theorem dephase_trace {γ : ℝ} {ρ : Matrix (Fin n) (Fin n) ℂ} :
    (dephase γ ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun i _ => dephase_apply_diag i

/-- A diagonal entry of a positive-semidefinite matrix is nonnegative (in the complex order). -/
theorem psd_diag_nonneg {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (i : Fin n) :
    0 ≤ M i i := by
  have h := hM.2 (Pi.single i 1)
  have he : star (Pi.single i (1 : ℂ)) ⬝ᵥ (M *ᵥ Pi.single i 1) = M i i := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq, eq_comm]
  rwa [he] at h

/-- A nonnegative real scalar multiple of a positive-semidefinite matrix is positive semidefinite. -/
theorem posSemidef_real_smul {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) {γ : ℝ}
    (hγ : 0 ≤ γ) : ((γ : ℂ) • M).PosSemidef := by
  refine ⟨?_, ?_⟩
  · show ((γ : ℂ) • M)ᴴ = (γ : ℂ) • M
    rw [Matrix.conjTranspose_smul, hM.1.eq, Complex.star_def, Complex.conj_ofReal]
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr hγ) (hM.2 x)

/-- **Positivity preservation** (the P of CPTP): the channel maps positive-semidefinite states to
positive-semidefinite states, so it maps density matrices to density matrices. -/
theorem dephase_posSemidef {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) : (dephase γ ρ).PosSemidef := by
  unfold dephase
  refine (posSemidef_real_smul hρ hγ0).add (posSemidef_real_smul ?_ (by linarith : (0 : ℝ) ≤ 1 - γ))
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  rw [Matrix.diag_apply]
  exact psd_diag_nonneg hρ i

/-- **Off-diagonal coherence decay (explicit).** Under `k` iterations the off-diagonal entry `i ≠ j`
is multiplied by `γ^k`. -/
theorem dephase_iter_offdiag {γ : ℝ} {ρ : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (hij : i ≠ j) :
    ∀ k : ℕ, ((dephase γ)^[k] ρ) i j = (γ : ℂ) ^ k * ρ i j
  | 0 => by simp
  | (k + 1) => by
    rw [Function.iterate_succ_apply', dephase_apply_offdiag hij, dephase_iter_offdiag hij k]
    ring

/-- **Off-diagonal coherence decay (limit).** For `0 ≤ γ < 1`, every off-diagonal coherence tends to
`0`: the state decoheres toward its pointer-basis diagonal. -/
theorem dephase_iter_offdiag_tendsto {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {ρ : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (hij : i ≠ j) :
    Filter.Tendsto (fun k => ((dephase γ)^[k] ρ) i j) Filter.atTop (nhds 0) := by
  have hfun : (fun k => ((dephase γ)^[k] ρ) i j) = fun k => (γ : ℂ) ^ k * ρ i j := by
    funext k; exact dephase_iter_offdiag hij k
  rw [hfun]
  have hg : Filter.Tendsto (fun k => (γ : ℂ) ^ k) Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun k : ℕ => γ ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
    have hkey := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    simp only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_zero] at hkey
    exact hkey
  simpa using hg.mul_const (ρ i j)

/-- **The pointer-basis fixed-point theorem.** For `γ ≠ 1`, the channel fixes exactly the states that
are already diagonal in the pointer basis (all off-diagonal coherences vanish). -/
theorem dephase_fixed_iff {γ : ℝ} (hγ : γ ≠ 1) {ρ : Matrix (Fin n) (Fin n) ℂ} :
    dephase γ ρ = ρ ↔ ∀ i j, i ≠ j → ρ i j = 0 := by
  constructor
  · intro hfix i j hij
    have he : (γ : ℂ) * ρ i j = ρ i j := by
      have := congrFun (congrFun hfix i) j
      rwa [dephase_apply_offdiag hij] at this
    have h1 : ((γ : ℂ) - 1) * ρ i j = 0 := by linear_combination he
    have hγc : (γ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hγ)
    exact (mul_eq_zero.mp h1).resolve_left hγc
  · intro hdiag
    ext i j
    rcases eq_or_ne i j with h | h
    · subst h; exact dephase_apply_diag i
    · rw [dephase_apply_offdiag h, hdiag i j h, mul_zero]

/-! ## R5 non-vacuity: a concrete decaying coherence and a diagonal fixed point. -/

/-- A concrete off-diagonal coherence decays exactly as `γ^k` under iteration. -/
theorem witness_offdiag_decay (γ : ℝ) (k : ℕ) :
    ((dephase γ)^[k] (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 = (γ : ℂ) ^ k * 2 := by
  have := dephase_iter_offdiag (γ := γ) (ρ := !![1, 2; 3, 4]) (i := 0) (j := 1) (by decide) k
  simpa using this

/-- Any pointer-basis-diagonal state is a fixed point (for `γ ≠ 1`). -/
theorem witness_diagonal_fixed {γ : ℝ} (hγ : γ ≠ 1) (d : Fin 2 → ℂ) :
    dephase γ (Matrix.diagonal d) = Matrix.diagonal d := by
  rw [dephase_fixed_iff hγ]
  intro i j hij
  exact Matrix.diagonal_apply_ne _ hij

#print axioms dephase_trace
#print axioms dephase_posSemidef
#print axioms dephase_iter_offdiag
#print axioms dephase_iter_offdiag_tendsto
#print axioms dephase_fixed_iff
#print axioms witness_offdiag_decay
#print axioms witness_diagonal_fixed

end OperatorKO7.Meta.QuantumBoundary.FiniteDecoherenceChannel
