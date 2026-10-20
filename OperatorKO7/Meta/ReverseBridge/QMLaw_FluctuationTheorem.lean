import Mathlib

/-!
# QM-law mechanization: finite fluctuation theorems (Crooks SP2-37, Jarzynski SP2-36)

This module closes the two previously-`NO-TRANSPORT` catalog walls by supplying the EXACT equalities the
framework previously lacked (it carried only the second-law inequality as a resource monotone). The setting
is a finite path ensemble carrying **microscopic reversibility** (local detailed balance) as the single
explicit, named physical hypothesis -- exactly the input every Crooks/Jarzynski derivation takes. From it we
mechanize, with no `sorry` and only baseline axioms:

* SP2-36 Jarzynski equality (exact): `∑_γ pF(γ) exp(-β W(γ)) = exp(-β ΔF)`.
* SP2-37 Crooks fluctuation theorem: the path-level ratio `pF(γ)/pR(γ*) = exp(β(W(γ)-ΔF))` and the
 work-distribution ratio `P_F(W=w) = exp(β(w-ΔF)) · P_R(W=-w)`.
* The second law as a COROLLARY of the exact equality: `ΔF ≤ ⟨W⟩_F` (Jensen on the convex exponential),
 so the exact equality strictly subsumes the framework's prior monotone inequality.

Honesty: every field is a plain real-valued function on a finite path type; the thermodynamic readings
(work, free energy, temperature, reversibility) are docstring ANALOGY and are NEVER asserted by a theorem.
Microscopic reversibility is an explicit hypothesis (a structure field), not a claim that any physical
system satisfies it. No rewriting relation. Trust: no `sorry`/`admit`/`axiom`/`native_decide`/etc.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseBridge.QMLaw_FluctuationTheorem

open Finset

/-- A finite driven work process with **microscopic reversibility** (local detailed balance), stated
structurally over a finite path ensemble. The thermodynamic reading is docstring ANALOGY only. -/
structure FiniteWorkProcess where
  /-- the (finite) set of trajectories -/
  Path : Type
  [instFin : Fintype Path]
  /-- forward path weight -/
  pF : Path → ℝ
  /-- reverse path probability -/
  pR : Path → ℝ
  /-- work along a path -/
  work : Path → ℝ
  /-- free-energy difference -/
  dF : ℝ
  /-- inverse temperature -/
  beta : ℝ
  beta_pos : 0 < beta
  pF_nonneg : ∀ γ, 0 ≤ pF γ
  pR_nonneg : ∀ γ, 0 ≤ pR γ
  /-- the reverse ensemble is normalized -/
  pR_sum : ∑ γ, pR γ = 1
  /-- time-reversal of paths (a bijection of the trajectory set) -/
  rev : Equiv.Perm Path
  /-- work is odd under time reversal -/
  work_antisym : ∀ γ, work (rev γ) = - work γ
  /-- **microscopic reversibility / local detailed balance** (the named physical hypothesis):
 `pF(γ) = exp(β (W(γ) - ΔF)) · pR(γ*)`. -/
  microRev : ∀ γ, pF γ = Real.exp (beta * (work γ - dF)) * pR (rev γ)

attribute [instance] FiniteWorkProcess.instFin

namespace FiniteWorkProcess

variable (P : FiniteWorkProcess)

/-- **SP2-36 Jarzynski equality (exact).** `∑_γ pF(γ) exp(-β W(γ)) = exp(-β ΔF)`, derived from microscopic
reversibility and the normalization of the reverse ensemble (a reindex by the reversal bijection). This is
the EXACT equality, not the second-law inequality. QM/thermo ANALOGY (docstring only): `⟨e^{-βW}⟩ = e^{-βΔF}`. -/
theorem jarzynski_equality :
    ∑ γ, P.pF γ * Real.exp (-(P.beta * P.work γ)) = Real.exp (-(P.beta * P.dF)) := by
  have key : ∀ γ : P.Path, P.pF γ * Real.exp (-(P.beta * P.work γ))
      = Real.exp (-(P.beta * P.dF)) * P.pR (P.rev γ) := by
    intro γ
    rw [P.microRev γ, mul_right_comm, ← Real.exp_add,
      show P.beta * (P.work γ - P.dF) + -(P.beta * P.work γ) = -(P.beta * P.dF) from by ring]
  calc ∑ γ, P.pF γ * Real.exp (-(P.beta * P.work γ))
      = ∑ γ, Real.exp (-(P.beta * P.dF)) * P.pR (P.rev γ) :=
        Finset.sum_congr rfl (fun γ _ => key γ)
    _ = Real.exp (-(P.beta * P.dF)) * ∑ γ, P.pR (P.rev γ) := by rw [Finset.mul_sum]
    _ = Real.exp (-(P.beta * P.dF)) * ∑ γ, P.pR γ := by rw [Equiv.sum_comp P.rev P.pR]
    _ = Real.exp (-(P.beta * P.dF)) := by rw [P.pR_sum, mul_one]

/-- **SP2-37 Crooks fluctuation theorem (path-level ratio).** The fundamental fluctuation relation: for a
path whose reverse carries nonzero reverse-probability, `pF(γ) / pR(γ*) = exp(β (W(γ) - ΔF))`.
QM/thermo ANALOGY (docstring only): Crooks' microscopic reversibility relation. -/
theorem crooks_path_ratio (γ : P.Path) (h : P.pR (P.rev γ) ≠ 0) :
    P.pF γ / P.pR (P.rev γ) = Real.exp (P.beta * (P.work γ - P.dF)) := by
  rw [P.microRev γ, mul_div_assoc, div_self h, mul_one]

open scoped Classical in
/-- **SP2-37 Crooks fluctuation theorem (work-distribution ratio).** Binning paths by work value, the
forward distribution at `w` and the reverse distribution at `-w` satisfy the exact Crooks ratio
`P_F(W = w) = exp(β (w - ΔF)) · P_R(W = -w)`. Derived from microscopic reversibility, work antisymmetry
under reversal, and the reversal bijection. -/
theorem crooks_work_distribution (w : ℝ) :
    (∑ γ ∈ univ.filter (fun γ : P.Path => P.work γ = w), P.pF γ)
      = Real.exp (P.beta * (w - P.dF))
        * ∑ γ ∈ univ.filter (fun γ : P.Path => P.work γ = -w), P.pR γ := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  have lhs_eq : ∀ γ : P.Path, (if P.work γ = w then P.pF γ else 0)
      = Real.exp (P.beta * (w - P.dF)) * (if P.work γ = w then P.pR (P.rev γ) else 0) := by
    intro γ
    by_cases hγ : P.work γ = w
    · rw [if_pos hγ, if_pos hγ, P.microRev γ, hγ]
    · rw [if_neg hγ, if_neg hγ, mul_zero]
  rw [Finset.sum_congr rfl (fun γ _ => lhs_eq γ), ← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp P.rev (fun δ => if P.work δ = -w then P.pR δ else 0)]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  show (if P.work γ = w then P.pR (P.rev γ) else 0)
     = (if P.work (P.rev γ) = -w then P.pR (P.rev γ) else 0)
  simp only [P.work_antisym γ, neg_inj]

/-- **SP2-36 corollary: the second law** `ΔF ≤ ⟨W⟩_F` for a normalized forward ensemble. The exact
Jarzynski equality implies the work inequality the framework previously carried only as a resource
monotone: by Jensen on the convex exponential, `exp(-β⟨W⟩) ≤ ⟨e^{-βW}⟩ = e^{-βΔF}`, hence `⟨W⟩ ≥ ΔF`. -/
theorem jarzynski_second_law (hpF : ∑ γ, P.pF γ = 1) :
    P.dF ≤ ∑ γ, P.pF γ * P.work γ := by
  have hjen : Real.exp (∑ γ, P.pF γ • (-(P.beta * P.work γ)))
      ≤ ∑ γ, P.pF γ • Real.exp (-(P.beta * P.work γ)) :=
    convexOn_exp.map_sum_le (fun γ _ => P.pF_nonneg γ) hpF (fun γ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjen
  rw [jarzynski_equality] at hjen
  have hsum : (∑ γ, P.pF γ * (-(P.beta * P.work γ))) = -P.beta * ∑ γ, P.pF γ * P.work γ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun γ _ => by ring)
  rw [hsum] at hjen
  have hle := Real.exp_le_exp.mp hjen
  nlinarith [P.beta_pos, hle]

end FiniteWorkProcess

/-! ## R5 non-vacuity witnesses. -/

/-- Work values of the non-trivial two-path witness: `W(0) = 1`, `W(1) = -1`. -/
def work2 : Fin 2 → ℝ := ![1, -1]

/-- Reverse probabilities of the two-path witness: uniform `1/2` each. -/
noncomputable def pR2 : Fin 2 → ℝ := fun _ => 1 / 2

/-- Microscopic-reversibility-induced forward weights of the two-path witness. -/
noncomputable def pF2 : Fin 2 → ℝ := fun γ => Real.exp (1 * (work2 γ - 0)) * pR2 (Equiv.swap 0 1 γ)

/-- **R5 (non-trivial, W ≢ 0): a genuine two-path process** with reversal `swap` and nonzero work,
satisfying every hypothesis of `FiniteWorkProcess`. Non-vacuity of the fluctuation-theorem structure. -/
noncomputable def twoPathProcess : FiniteWorkProcess where
  Path := Fin 2
  pF := pF2
  pR := pR2
  work := work2
  dF := 0
  beta := 1
  beta_pos := one_pos
  pF_nonneg := fun γ => by
    show (0:ℝ) ≤ Real.exp (1 * (work2 γ - 0)) * (1 / 2); positivity
  pR_nonneg := fun _ => by show (0:ℝ) ≤ 1 / 2; norm_num
  pR_sum := by unfold pR2; rw [Fin.sum_univ_two]; norm_num
  rev := Equiv.swap 0 1
  work_antisym := by
    intro γ; fin_cases γ
    · show work2 1 = -work2 0; simp [work2]
    · show work2 0 = -work2 1; simp [work2]
  microRev := fun _ => rfl

/-- The two-path witness has genuinely nonzero work, so the structure is non-vacuous beyond equilibrium. -/
theorem twoPath_work_nonzero : work2 0 ≠ 0 := by unfold work2; norm_num

/-- Jarzynski holds non-vacuously on the two-path witness: `∑ pF·e^{-W} = 1 = e^{0}`. -/
theorem twoPath_jarzynski :
    ∑ γ, twoPathProcess.pF γ * Real.exp (-(twoPathProcess.beta * twoPathProcess.work γ))
      = Real.exp (-(twoPathProcess.beta * twoPathProcess.dF)) :=
  twoPathProcess.jarzynski_equality

/-- **R5 (equilibrium, normalized forward ensemble): a one-path process** witnessing the second law with a
normalized `pF` (`W ≡ 0`, `ΔF = 0`, `pF = pR = 1`, reversal `id`). Saturates `ΔF ≤ ⟨W⟩` at equality. -/
noncomputable def equilibriumProcess : FiniteWorkProcess where
  Path := Fin 1
  pF := fun _ => 1
  pR := fun _ => 1
  work := fun _ => 0
  dF := 0
  beta := 1
  beta_pos := one_pos
  pF_nonneg := by intro _; norm_num
  pR_nonneg := by intro _; norm_num
  pR_sum := by simp
  rev := Equiv.refl _
  work_antisym := by intro _; norm_num
  microRev := by intro γ; simp [Real.exp_zero]

/-- The equilibrium witness's forward ensemble is normalized, so the second law applies and saturates. -/
theorem equilibrium_second_law :
    equilibriumProcess.dF ≤ ∑ γ, equilibriumProcess.pF γ * equilibriumProcess.work γ :=
  equilibriumProcess.jarzynski_second_law (by simp [equilibriumProcess])

/-! ## Headline axiom audit (subset of {propext, Classical.choice, Quot.sound}). -/

#print axioms FiniteWorkProcess.jarzynski_equality
#print axioms FiniteWorkProcess.crooks_path_ratio
#print axioms FiniteWorkProcess.crooks_work_distribution
#print axioms FiniteWorkProcess.jarzynski_second_law
#print axioms twoPath_work_nonzero
#print axioms twoPath_jarzynski
#print axioms equilibrium_second_law

end OperatorKO7.Meta.ReverseBridge.QMLaw_FluctuationTheorem
