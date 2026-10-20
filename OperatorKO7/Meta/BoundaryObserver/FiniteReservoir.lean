import OperatorKO7.Meta.BoundaryObserver.ThermalStaircase

/-!
# Finite reservoirs: the quadratic excess, the remainder estimate and staircase resources

Manuscript: Corollaries `cor:finite-reservoir-excess`, `cor:finite-reservoir-correction` and
`cor:staircase-reservoir-resources`.

The entropy-difference bound of Reeb and Wolf, `D(a ‖ b) ≥ 2 (S(a) - S(b))² / c_d` with
`c_d = ln²(d - 1) + 4` on a `d`-dimensional carrier, enters as the explicit hypothesis
`ReebWolfBound`. Everything the three corollaries derive from it is proved here: the remainder
estimate `βQ - Δ ≥ I + 2 (Δ + I)² / c_d` from the heat balance of `thermal_information_balance`,
the quadratic excess and its parameter form `Δ² / (2N)`, the dimension bounds, their divergence as
the tolerance tends to zero, the staircase excess `E ≥ 2 Δ² / ∑ⱼ c_{d_j}` through the lemma of
Sedrakyan, and the step-count bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix Filter Topology
open scoped BigOperators ComplexOrder Kronecker
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Thermal
open OperatorKO7.Meta.BoundaryObserver.ThermalStaircase

namespace OperatorKO7.Meta.BoundaryObserver.FiniteReservoir

/-- The constant `c_d = ln²(d - 1) + 4` of a reservoir of dimension `d`. -/
noncomputable def resConst (d : ℕ) : ℝ := Real.log ((d : ℝ) - 1) ^ 2 + 4

theorem resConst_pos (d : ℕ) : 0 < resConst d := by
  unfold resConst
  positivity

/-- The entropy-difference bound of Reeb and Wolf on the carrier `κ`, as a hypothesis:
`D(a ‖ b) ≥ 2 (S(a) - S(b))² / c_d` for a density matrix `a` and a positive definite density
matrix `b` with `S(a) ≥ S(b)`. -/
def ReebWolfBound (κ : Type) [Fintype κ] [DecidableEq κ] : Prop :=
  ∀ a b : Matrix κ κ ℂ, a.PosSemidef → a.trace = 1 → b.PosDef → b.trace = 1 →
    entropy b ≤ entropy a →
      2 * (entropy a - entropy b) ^ 2 / resConst (Fintype.card κ) ≤ relativeEntropy a b

section OneUnitary

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- `S(τ_R) - S(γ) = Δ + I(S : R)`: product additivity and unitary invariance. -/
theorem reservoir_entropy_gain (u : Matrix.unitaryGroup (ι × κ) ℂ) {rho : Matrix ι ι ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) {h : Matrix κ κ ℂ} (hh : h.IsHermitian)
    (β : ℝ) :
    entropy (marginalRight (thermalJoint u rho hh β)) - entropy (gibbsState hh β) =
      (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) +
        mutualInfo (thermalJoint u rho hh β) := by
  have he := thermalJoint_entropy u hrho htr hh β
  unfold mutualInfo
  linarith

/-- The heat remainder `βQ - Δ = I + D` is nonnegative for every finite reservoir. -/
theorem remainder_nonneg (u : Matrix.unitaryGroup (ι × κ) ℂ) {rho : Matrix ι ι ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) {h : Matrix κ κ ℂ} (hh : h.IsHermitian)
    (β : ℝ) :
    0 ≤ β * reservoirHeat u rho hh β -
      (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) := by
  obtain ⟨hb, hI, hD⟩ := thermal_information_balance u hrho htr hh β
  linarith

/-- **The remainder estimate** of `cor:finite-reservoir-correction`:
`βQ - Δ ≥ I(S : R) + 2 (Δ + I(S : R))² / c_d`. -/
theorem reservoir_remainder (hRW : ReebWolfBound κ) (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1) {h : Matrix κ κ ℂ}
    (hh : h.IsHermitian) (β : ℝ)
    (hΔ : 0 ≤ entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) :
    mutualInfo (thermalJoint u rho hh β) +
        2 * ((entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) +
          mutualInfo (thermalJoint u rho hh β)) ^ 2 / resConst (Fintype.card κ) ≤
      β * reservoirHeat u rho hh β -
        (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) := by
  obtain ⟨hb, hI, -⟩ := thermal_information_balance u hrho htr hh β
  obtain ⟨htp, htt⟩ := thermalJoint_density u hrho htr hh β
  have hgain := reservoir_entropy_gain u hrho htr hh β
  have hD := hRW (marginalRight (thermalJoint u rho hh β)) (gibbsState hh β)
    (marginalRight_posSemidef htp) ((marginalRight_trace _).trans htt) (gibbsState_posDef hh β)
    (gibbsState_trace hh β) (by linarith)
  rw [hgain] at hD
  linarith

/-- **The finite-reservoir bound** `βQ ≥ Δ + 2 Δ² / c_d`. -/
theorem reservoir_quadratic (hRW : ReebWolfBound κ) (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1) {h : Matrix κ κ ℂ}
    (hh : h.IsHermitian) (β : ℝ)
    (hΔ : 0 ≤ entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) :
    entropy rho - entropy (marginalLeft (thermalJoint u rho hh β)) +
        2 * (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) ^ 2 /
          resConst (Fintype.card κ) ≤ β * reservoirHeat u rho hh β := by
  have hr := reservoir_remainder hRW u hrho htr hh β hΔ
  obtain ⟨-, hI, -⟩ := thermal_information_balance u hrho htr hh β
  have hc := resConst_pos (Fintype.card κ)
  have hmono : 2 * (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) ^ 2 /
      resConst (Fintype.card κ) ≤
      2 * ((entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) +
        mutualInfo (thermalJoint u rho hh β)) ^ 2 / resConst (Fintype.card κ) := by
    apply div_le_div_of_nonneg_right _ hc.le
    nlinarith [mul_nonneg hΔ hI, sq_nonneg (mutualInfo (thermalJoint u rho hh β))]
  linarith

end OneUnitary

/-! ## The parameter form and the dimension bounds -/

/-- For every `N ≥ ln²(d - 1) / 4 + 1`, `Δ² / (2N) ≤ 2 Δ² / c_d`; the bound of Reeb and Wolf in
the parameter form of `cor:finite-reservoir-excess`. -/
theorem excess_le_of_parameter (d : ℕ) (Δ N : ℝ) (hN : Real.log ((d : ℝ) - 1) ^ 2 / 4 + 1 ≤ N) :
    Δ ^ 2 / (2 * N) ≤ 2 * Δ ^ 2 / resConst d := by
  have hc := resConst_pos d
  have hN0 : 0 < N := by
    have := sq_nonneg (Real.log ((d : ℝ) - 1))
    linarith
  rw [div_le_div_iff₀ (by positivity) hc]
  have h := mul_le_mul_of_nonneg_left hN (sq_nonneg Δ)
  unfold resConst
  nlinarith

/-- The dimension bound of `cor:finite-reservoir-correction`: an excess at most `ε` at an
entropy reduction at least `s₀ > 0` needs `d ≥ 1 + exp √(max 0 (2 s₀² / ε - 4))`. -/
theorem dimension_of_excess {d : ℕ} (hd : 2 ≤ d) {s₀ Δ ε : ℝ} (hs : 0 < s₀) (hΔ : s₀ ≤ Δ)
    (hε : 0 < ε) (hE : 2 * Δ ^ 2 / resConst d ≤ ε) :
    1 + Real.exp (Real.sqrt (max 0 (2 * s₀ ^ 2 / ε - 4))) ≤ d := by
  have hc := resConst_pos d
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlog : 0 ≤ Real.log ((d : ℝ) - 1) := Real.log_nonneg hd1
  have h1 : 2 * s₀ ^ 2 / ε - 4 ≤ Real.log ((d : ℝ) - 1) ^ 2 := by
    rw [div_le_iff₀ hc] at hE
    have h2 : 2 * s₀ ^ 2 ≤ 2 * Δ ^ 2 := by nlinarith
    have h3 : 2 * s₀ ^ 2 / ε ≤ resConst d := by
      rw [div_le_iff₀ hε]
      nlinarith
    unfold resConst at h3
    linarith
  have hmax : max 0 (2 * s₀ ^ 2 / ε - 4) ≤ Real.log ((d : ℝ) - 1) ^ 2 :=
    max_le (sq_nonneg _) h1
  have hsqrt : Real.sqrt (max 0 (2 * s₀ ^ 2 / ε - 4)) ≤ Real.log ((d : ℝ) - 1) := by
    calc Real.sqrt (max 0 (2 * s₀ ^ 2 / ε - 4)) ≤ Real.sqrt (Real.log ((d : ℝ) - 1) ^ 2) :=
          Real.sqrt_le_sqrt hmax
      _ = Real.log ((d : ℝ) - 1) := Real.sqrt_sq hlog
  have hexp : Real.exp (Real.sqrt (max 0 (2 * s₀ ^ 2 / ε - 4))) ≤ (d : ℝ) - 1 := by
    calc _ ≤ Real.exp (Real.log ((d : ℝ) - 1)) := Real.exp_le_exp.mpr hsqrt
      _ = (d : ℝ) - 1 := Real.exp_log (by linarith)
  linarith

/-- The dimension bound of `cor:finite-reservoir-excess`: for `0 < η < Δ² / 2`, an excess at
most `η` needs `d ≥ 1 + exp √(2 Δ² / η - 4)`. -/
theorem dimension_of_tolerance {d : ℕ} (hd : 2 ≤ d) {Δ η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η)
    (hηs : η < Δ ^ 2 / 2) (hE : 2 * Δ ^ 2 / resConst d ≤ η) :
    1 + Real.exp (Real.sqrt (2 * Δ ^ 2 / η - 4)) ≤ d := by
  have h := dimension_of_excess hd hΔ le_rfl hη hE
  have hpos : 0 ≤ 2 * Δ ^ 2 / η - 4 := by
    rw [sub_nonneg, le_div_iff₀ hη]
    linarith
  rwa [max_eq_right hpos] at h

/-- The dimension bound diverges as the tolerance tends to zero. -/
theorem dimension_bound_tendsto (s : ℝ) (hs : 0 < s) :
    Tendsto (fun η : ℝ => 1 + Real.exp (Real.sqrt (max 0 (2 * s ^ 2 / η - 4))))
      (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun η : ℝ => 2 * s ^ 2 / η) (𝓝[>] 0) atTop := by
    simp_rw [div_eq_mul_inv]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  have h2 : Tendsto (fun η : ℝ => max 0 (2 * s ^ 2 / η - 4)) (𝓝[>] 0) atTop :=
    tendsto_atTop_mono (fun η => le_max_right _ _) (tendsto_atTop_add_const_right _ (-4) h1)
  have hsq : Tendsto Real.sqrt atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b ^ 2, fun x hx => ?_⟩
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  exact tendsto_atTop_add_const_left _ 1 (Real.tendsto_exp_atTop.comp (hsq.comp h2))

/-! ## One finite operation -/

section Operation

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-- A finite operation that brings a state of positive entropy below `η` with heat within `η / β`
of the entropy removed uses a reservoir of dimension at least
`1 + exp √(max 0 (S(ρ)² / (2η) - 4))`: the staircases of `thm:thermal-staircase` use reservoirs
whose dimension grows without bound as their tolerance tends to zero. -/
theorem operation_dimension (T : ThermalOperation X) (hRW : ReebWolfBound T.bath)
    (hcard : 2 ≤ Fintype.card T.bath) {rho : Matrix X X ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) {β η : ℝ} (hη : 0 < η) (hηs : η ≤ entropy rho / 2)
    (hout : entropy (T.output rho β) < η)
    (hheat : β * T.heat rho β ≤ entropy rho - entropy (T.output rho β) + η) :
    1 + Real.exp (Real.sqrt (max 0 (2 * (entropy rho / 2) ^ 2 / η - 4))) ≤
      Fintype.card T.bath := by
  haveI := T.bathNonempty
  have hΔ : entropy rho / 2 ≤ entropy rho - entropy (T.output rho β) := by linarith
  have hΔ0 : 0 ≤ entropy rho - entropy (marginalLeft (thermalJoint T.joint rho T.ham_hermitian β)) := by
    change 0 ≤ entropy rho - entropy (T.output rho β)
    linarith
  have hq := reservoir_quadratic hRW T.joint hrho htr T.ham_hermitian β hΔ0
  have hE : 2 * (entropy rho - entropy (T.output rho β)) ^ 2 / resConst (Fintype.card T.bath)
      ≤ η := by
    simp only [ThermalOperation.output, ThermalOperation.heat] at hheat hq ⊢
    linarith
  exact dimension_of_excess hcard (by linarith) hΔ hη hE

end Operation

/-! ## Staircases -/

/-- The lemma of Sedrakyan applied to the step excesses: per-step bounds
`E_j ≥ 2 max(δ_j, 0)² / c_j` and a nonnegative total reduction give
`∑ E_j ≥ 2 (∑ δ_j)² / ∑ c_j`. -/
theorem sum_excess_bound (n : ℕ) (δ c E : ℕ → ℝ) (hc : ∀ j, 0 < c j)
    (hstep : ∀ j, 2 * max (δ j) 0 ^ 2 / c j ≤ E j)
    (hΔ : 0 ≤ ∑ j ∈ Finset.range n, δ j) :
    2 * (∑ j ∈ Finset.range n, δ j) ^ 2 / ∑ j ∈ Finset.range n, c j ≤
      ∑ j ∈ Finset.range n, E j := by
  have hA : ∑ j ∈ Finset.range n, δ j ≤ ∑ j ∈ Finset.range n, max (δ j) 0 :=
    Finset.sum_le_sum fun j _ => le_max_left _ _
  have hC : 0 ≤ ∑ j ∈ Finset.range n, c j := Finset.sum_nonneg fun j _ => (hc j).le
  have hsed := Finset.sq_sum_div_le_sum_sq_div (Finset.range n) (fun j => max (δ j) 0)
    (fun j _ => hc j)
  calc 2 * (∑ j ∈ Finset.range n, δ j) ^ 2 / ∑ j ∈ Finset.range n, c j
      ≤ 2 * (∑ j ∈ Finset.range n, max (δ j) 0) ^ 2 / ∑ j ∈ Finset.range n, c j := by
        apply div_le_div_of_nonneg_right _ hC
        have := pow_le_pow_left₀ hΔ hA 2
        linarith
    _ = 2 * ((∑ j ∈ Finset.range n, max (δ j) 0) ^ 2 / ∑ j ∈ Finset.range n, c j) := by ring
    _ ≤ 2 * ∑ j ∈ Finset.range n, max (δ j) 0 ^ 2 / c j := by linarith
    _ = ∑ j ∈ Finset.range n, 2 * max (δ j) 0 ^ 2 / c j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range n, E j := Finset.sum_le_sum fun j _ => hstep j

section Staircase

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The states of a sequence of finite operations, each on a fresh reservoir. -/
noncomputable def stepState (T : ℕ → ThermalOperation X) (rho : Matrix X X ℂ) (β : ℝ) :
    ℕ → Matrix X X ℂ
  | 0 => rho
  | j + 1 => (T j).output (stepState T rho β j) β

theorem stepState_density (T : ℕ → ThermalOperation X) {rho : Matrix X X ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) (β : ℝ) (j : ℕ) :
    (stepState T rho β j).PosSemidef ∧ (stepState T rho β j).trace = 1 := by
  induction j with
  | zero => exact ⟨hrho, htr⟩
  | succ j ih => exact (T j).output_density ih.1 ih.2 β

/-- **Reservoir resources of a staircase.** A sequence of `n` finite operations with reservoirs
of dimensions `d_j` and a nonnegative total entropy reduction `Δ` has excess
`E = βQ - Δ ≥ 2 Δ² / ∑ⱼ c_{d_j}`. -/
theorem staircase_excess (T : ℕ → ThermalOperation X) (hRW : ∀ j, ReebWolfBound (T j).bath)
    {rho : Matrix X X ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1) (β : ℝ) (n : ℕ)
    (hΔ : 0 ≤ entropy rho - entropy (stepState T rho β n)) :
    2 * (entropy rho - entropy (stepState T rho β n)) ^ 2 /
        (∑ j ∈ Finset.range n, resConst (Fintype.card (T j).bath)) ≤
      β * (∑ j ∈ Finset.range n, (T j).heat (stepState T rho β j) β) -
        (entropy rho - entropy (stepState T rho β n)) := by
  have htel : entropy rho - entropy (stepState T rho β n) =
      ∑ j ∈ Finset.range n, (entropy (stepState T rho β j) -
        entropy (stepState T rho β (j + 1))) := by
    rw [Finset.sum_range_sub']
    rfl
  have hstep : ∀ j, 2 * max (entropy (stepState T rho β j) -
      entropy (stepState T rho β (j + 1))) 0 ^ 2 / resConst (Fintype.card (T j).bath) ≤
      β * (T j).heat (stepState T rho β j) β -
        (entropy (stepState T rho β j) - entropy (stepState T rho β (j + 1))) := by
    intro j
    haveI := (T j).bathNonempty
    obtain ⟨hp, ht⟩ := stepState_density T hrho htr β j
    have hsucc : stepState T rho β (j + 1) = (T j).output (stepState T rho β j) β := rfl
    rw [hsucc]
    rcases le_or_gt 0 (entropy (stepState T rho β j) -
        entropy ((T j).output (stepState T rho β j) β)) with h0 | h0
    · rw [max_eq_left h0]
      have hq := reservoir_quadratic (hRW j) (T j).joint hp ht (T j).ham_hermitian β h0
      simp only [ThermalOperation.output, ThermalOperation.heat] at hq ⊢
      linarith
    · rw [max_eq_right h0.le]
      have hr := remainder_nonneg (T j).joint hp ht (T j).ham_hermitian β
      have hc := resConst_pos (Fintype.card (T j).bath)
      simp only [ThermalOperation.output, ThermalOperation.heat] at hr ⊢
      have : 2 * (0 : ℝ) ^ 2 / resConst (Fintype.card (T j).bath) = 0 := by simp
      linarith
  have h := sum_excess_bound n
    (fun j => entropy (stepState T rho β j) - entropy (stepState T rho β (j + 1)))
    (fun j => resConst (Fintype.card (T j).bath))
    (fun j => β * (T j).heat (stepState T rho β j) β -
      (entropy (stepState T rho β j) - entropy (stepState T rho β (j + 1))))
    (fun j => resConst_pos _) hstep (by rw [← htel]; exact hΔ)
  rw [← htel, Finset.sum_sub_distrib, ← Finset.mul_sum, ← htel] at h
  exact h

/-- The step-count bound of `cor:staircase-reservoir-resources`: with every reservoir of
dimension `m`, an excess at most `η` and a reduction above `s - η > 0` need
`n ≥ 2 (s - η)² / (η c_m)`. -/
theorem staircase_step_count {m n : ℕ} (hn : 0 < n) {s η Δ E : ℝ} (hη : 0 < η) (hηs : η < s)
    (hΔ : s - η < Δ) (hE : E ≤ η) (hbound : 2 * Δ ^ 2 / (n * resConst m) ≤ E) :
    2 * (s - η) ^ 2 / (η * resConst m) ≤ n := by
  have hc := resConst_pos m
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 2 * (s - η) ^ 2 ≤ 2 * Δ ^ 2 := by nlinarith
  have h2 : 2 * Δ ^ 2 ≤ η * (n * resConst m) := by
    rw [div_le_iff₀ (by positivity)] at hbound
    have := mul_le_mul_of_nonneg_right hE (by positivity : (0 : ℝ) ≤ n * resConst m)
    linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The staircase with every reservoir of dimension `m` and tolerance `η` on a state of entropy
`s > η`: the number of steps is at least `2 (s - η)² / (η c_m)`. -/
theorem staircase_resources (T : ℕ → ThermalOperation X) (hRW : ∀ j, ReebWolfBound (T j).bath)
    {m : ℕ} (hm : ∀ j, Fintype.card (T j).bath = m) {rho : Matrix X X ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) (β : ℝ) {n : ℕ} (hn : 0 < n) {η : ℝ}
    (hη : 0 < η) (hηs : η < entropy rho)
    (hout : entropy (stepState T rho β n) < η)
    (hheat : β * (∑ j ∈ Finset.range n, (T j).heat (stepState T rho β j) β) ≤
      entropy rho - entropy (stepState T rho β n) + η) :
    2 * (entropy rho - η) ^ 2 / (η * resConst m) ≤ n := by
  have hΔ : entropy rho - η < entropy rho - entropy (stepState T rho β n) := by linarith
  have h := staircase_excess T hRW hrho htr β n (by linarith)
  have hsum : ∑ j ∈ Finset.range n, resConst (Fintype.card (T j).bath) = n * resConst m := by
    simp [hm]
  rw [hsum] at h
  exact staircase_step_count hn hη hηs hΔ (by linarith) h

end Staircase

end OperatorKO7.Meta.BoundaryObserver.FiniteReservoir
