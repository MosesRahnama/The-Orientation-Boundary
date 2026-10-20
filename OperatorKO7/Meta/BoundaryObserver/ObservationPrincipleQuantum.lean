import OperatorKO7.Meta.BoundaryObserver.ReconstructionKnillLaflamme
import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
import OperatorKO7.Meta.BoundaryObserver.ThermalStaircase
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularityQuantum
import OperatorKO7.Meta.BoundaryObserver.PairQubit
import OperatorKO7.Meta.UUET.Quantum.PhaseTwirl
import OperatorKO7.Meta.BoundaryObserver.SourceApexInstrument

set_option autoImplicit false

/-!
# Quantum reconstruction, thermal and channel sentences of the Boundary-Observation Principle

The statements of the quantum sections that no earlier declaration states: the overlap
coefficients of a nonzero Knill–Laflamme code have trace one; the probability of an effect in a
density matrix is real; the two modular means and the relative entropy of a pure basis state
against the maximally mixed qubit are `ln 2`; the final system state of a finite bath is positive
definite and every finite operation leaves positive entropy on a positive-definite input; the
least heat limit over vanishing output entropy is `S(ρ)/β`, with the fair pair staircase; the
projective outcome probabilities `(1 + tr(ρX))/2` and `(1 + tr(ρZ))/2`; the unit diagonal of the
phase correlation and the removal of a fixed coherence; and the sufficiency of diagonal
preservation for the composition of compressed maps, with its class form.

Relation: none beyond the matrices, operations and channels of the imported modules.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleQuantum

open Filter Topology Matrix
open scoped ComplexOrder

/-! ## Theorem `thm:knill-laflamme-recovery`: trace one -/

open OperatorKO7.Meta.BoundaryObserver.ReconstructionRecovery

/-- For a nonzero code the Knill–Laflamme overlap coefficients have trace one. -/
theorem overlap_trace_one {n : ℕ} {E : Type} [Fintype E] (errors : E → Mat n) (p : Mat n)
    (hidem : p * p = p) (hne : p ≠ 0)
    (hcomplete : (∑ e, dagger (errors e) * errors e) = 1)
    (c : E → E → ℂ) (hKL : ∀ a b, p * dagger (errors a) * errors b * p = c a b • p) :
    ∑ a, c a a = 1 := by
  have hsum : (∑ a, c a a) • p = p := by
    calc (∑ a, c a a) • p = ∑ a, c a a • p := Finset.sum_smul
      _ = ∑ a, p * dagger (errors a) * errors a * p := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hKL]
      _ = p * (∑ a, dagger (errors a) * errors a) * p := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          rw [Matrix.mul_assoc p]
      _ = p := by rw [hcomplete, Matrix.mul_one, hidem]
  have h0 : ((∑ a, c a a) - 1) • p = 0 := by rw [sub_smul, hsum, one_smul, sub_self]
  rcases smul_eq_zero.1 h0 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne

/-! ## Theorem `thm:fiber-density`: the probability of an effect is real -/

open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction

/-- For a density matrix and an effect, `tr(ρe)` is real. -/
theorem effect_probability_real {n : ℕ} (ρ : Density n) (e : Effect n) :
    (BoundaryReconstruction.tr (ρ.val * e.val)).im = 0 := by
  have hρ : ρ.val.IsHermitian := ρ.2.1.1
  have he : e.val.IsHermitian := e.2.1.1
  have hstar : star (BoundaryReconstruction.tr (ρ.val * e.val)) =
      BoundaryReconstruction.tr (ρ.val * e.val) := by
    unfold BoundaryReconstruction.tr
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hρ.eq, he.eq,
      Matrix.trace_mul_comm]
  have := congrArg Complex.im hstar
  rw [Complex.star_def, Complex.conj_im] at this
  linarith

/-! ## Proposition `prop:reference-entropy-change`: the two values -/

open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Thermal
open OperatorKO7.Meta.BoundaryObserver.ThermalStaircase

/-- For `b = I/2` on a qubit and the pure basis state `a`, `tr(aK) = tr(bK) = ln 2` with
`K = -log b`, and `D(a ‖ b) = ln 2`. -/
theorem reference_entropy_values :
    modularMean (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ)))
        (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) ![1, 0]) = Real.log 2 ∧
      modularMean (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ)))
        (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ))) =
          Real.log 2 ∧
      relativeEntropy (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) ![1, 0])
        (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ))) =
          Real.log 2 := by
  have hm : ∀ q : Fin 2 → ℝ,
      modularMean (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ)))
        (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) q) =
          -(∑ i, q i * Real.log (1 / 2)) := by
    intro q
    rw [modularMean, matrixLog_spectralLift, spectralLift_mul, spectralLift_trace_re]
  have hl : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have s1 : -(∑ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i * Real.log (1 / 2)) = Real.log 2 := by
    rw [Fin.sum_univ_two, hl]
    simp
  have s2 : -(∑ i : Fin 2, (fun _ => (1 / 2 : ℝ)) i * Real.log (1 / 2)) = Real.log 2 := by
    rw [Fin.sum_univ_two, hl]
    ring
  refine ⟨(hm _).trans s1, (hm _).trans s2, ?_⟩
  rw [relativeEntropy_eq_modular_sub_entropy (spectralLift_hermitian _ _)
    (spectralLift_hermitian _ _), hm, hm, s1, s2, entropy_spectralLift, entropy_spectralLift,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.negMulLog, hl, Real.log_one,
    Real.log_zero]
  ring

/-! ## Theorem `thm:no-exact-erasure` and Corollary `cor:thermal-landauer-infimum` -/

open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal

/-- The final system state of a finite bath is positive definite. -/
theorem thermalSystem_posDef {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ) {rho : Matrix ι ι ℂ} (hrho : rho.PosDef)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    (marginalLeft (thermalJoint u rho hh β)).PosDef :=
  marginalLeft_posDef (thermalJoint_posDef u hrho hh β)

/-- For a system of dimension at least two and a positive-definite input, every finite operation
leaves an output of positive entropy. -/
theorem operation_output_entropy_pos {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (T : ThermalOperation ι) {rho : Matrix ι ι ℂ} (hrho : rho.PosDef) (htr : rho.trace = 1)
    (β : ℝ) : 0 < entropy (T.output rho β) :=
  entropy_pos_of_posDef (thermalSystem_posDef T.joint hrho T.ham_hermitian β)
    (T.output_density hrho.posSemidef htr β).2

/-- A sequence of finite operations with output entropy below `1/(n+1)` and heat within `1/(n+1)`
of `S(ρ)/β` after scaling by `β`. -/
theorem exists_minimizing_sequence {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) :
    ∃ T : ℕ → ThermalOperation ι,
      Tendsto (fun n => entropy ((T n).output rho β)) atTop (𝓝 0) ∧
        Tendsto (fun n => (T n).heat rho β) atTop (𝓝 (entropy rho / β)) := by
  have hη : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose T hT using fun n : ℕ => heat_attains_landauer hrho htr hβ (hη n)
  refine ⟨T, ?_, ?_⟩
  · exact squeeze_zero (fun n => entropy_nonneg_density ((T n).output_density hrho htr β).1
      ((T n).output_density hrho htr β).2) (fun n => (hT n).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · have hdiff : Tendsto (fun n => β * (T n).heat rho β - entropy rho) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (hT n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n => β * (T n).heat rho β) atTop (𝓝 (entropy rho)) := by
      have := hdiff.add_const (entropy rho)
      simpa using this
    have := hlim.div_const β
    simpa [mul_div_cancel_left₀ _ hβ.ne'] using this

/-- Among sequences of finite operations whose output entropy tends to zero and whose heat
converges, the least heat limit is `S(ρ)/β`. -/
theorem least_heat_limit {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) :
    IsLeast {L : ℝ | ∃ T : ℕ → ThermalOperation ι,
        Tendsto (fun n => entropy ((T n).output rho β)) atTop (𝓝 0) ∧
          Tendsto (fun n => (T n).heat rho β) atTop (𝓝 L)} (entropy rho / β) := by
  refine ⟨exists_minimizing_sequence hrho htr hβ, ?_⟩
  rintro L ⟨T, hS, hQ⟩
  have hle : entropy rho - 0 ≤ β * L :=
    le_of_tendsto_of_tendsto' (hS.const_sub (entropy rho)) (hQ.const_mul β)
      (fun n => (T n).landauer hrho htr hβ)
  rw [div_le_iff₀ hβ]
  linarith

/-- For the fair pair, finite staircases give output entropy tending to zero and heat tending to
`ln 2 / β`. -/
theorem fair_pair_staircase {β : ℝ} (hβ : 0 < β) :
    ∃ T : ℕ → ThermalOperation Bool,
      Tendsto (fun n => entropy ((T n).output fairPair β)) atTop (𝓝 0) ∧
        Tendsto (fun n => (T n).heat fairPair β) atTop (𝓝 (Real.log 2 / β)) := by
  have hη : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose T hT using fun n : ℕ => fair_pair_heat_attains hβ (hη n)
  refine ⟨T, ?_, ?_⟩
  · exact squeeze_zero (fun n => entropy_nonneg_density
      ((T n).output_density fairPair_posDef.posSemidef fairPair_trace β).1
      ((T n).output_density fairPair_posDef.posSemidef fairPair_trace β).2)
      (fun n => (hT n).1.le) tendsto_one_div_add_atTop_nhds_zero_nat
  · have hdiff : Tendsto (fun n => β * (T n).heat fairPair β - Real.log 2) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (hT n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n => β * (T n).heat fairPair β) atTop (𝓝 (Real.log 2)) := by
      have := hdiff.add_const (Real.log 2)
      simpa using this
    have := hlim.div_const β
    simpa [mul_div_cancel_left₀ _ hβ.ne'] using this

/-! ## Theorem `thm:sharp-complementary-entropy`: the outcome probabilities -/

open OperatorKO7.Meta.BoundaryObserver.PairQubit

/-- The projective outcome laws of `X` and `Z` give the outcome `+1` the probabilities
`(1 + tr(ρX))/2` and `(1 + tr(ρZ))/2`, through the projectors `(I + X)/2` and `(I + Z)/2`. -/
theorem projective_outcome_probabilities (ρ : Matrix Bool Bool ℂ) (htr : ρ.trace = 1) :
    (ρ * ((1 / 2 : ℂ) • (1 + pairX))).trace.re = (1 + (ρ * pairX).trace.re) / 2 ∧
      (ρ * ((1 / 2 : ℂ) • (1 + pairZ))).trace.re = (1 + (ρ * pairZ).trace.re) / 2 := by
  constructor <;>
  · rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add,
      htr, smul_eq_mul]
    simp [Complex.mul_re]
    ring

/-! ## Theorem `thm:phase-ensemble`: the unit diagonal and a fixed coherence -/

open OperatorKO7.Meta.UUET.Quantum

/-- The phase correlation has unit diagonal. -/
theorem phaseCorrelation_diag {Ω ι : Type} [Fintype Ω] (w : Ω → ℝ) (z : Ω → ι → ℂ)
    (hw : ∑ a, w a = 1) (hz : ∀ a i, z a i * star (z a i) = 1) (i : ι) :
    phaseCorrelation w z i i = 1 := by
  unfold phaseCorrelation
  simp_rw [mul_assoc, hz, mul_one]
  rw [← Complex.ofReal_sum, hw, Complex.ofReal_one]

/-- For a fixed nonzero coherence `ρ_ij`, the phase ensemble removes it if and only if
`M_ij = 0`. -/
theorem phaseEnsemble_removes_coherence_iff {Ω ι : Type} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] (w : Ω → ℝ) (z : Ω → ι → ℂ) (ρ : Operator ι) (i j : ι) (hρ : ρ i j ≠ 0) :
    phaseEnsemble w z ρ i j = 0 ↔ phaseCorrelation w z i j = 0 := by
  rw [phaseEnsemble_apply]
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_right hρ
  · intro h
    rw [h, zero_mul]

/-! ## Theorem `thm:classical-shadow-composition`: diagonal preservation and classes -/

/-- If `G` preserves the diagonal subalgebra, the compressed maps `ΔFΔ` and `ΔGΔ` compose. -/
theorem diagonal_preserving_composes {ι : Type} [DecidableEq ι]
    (f g : Module.End ℂ (Operator ι)) (hg : ∀ ρ, dephaseEnd (g (dephaseEnd ρ)) = g (dephaseEnd ρ)) :
    dephaseEnd * f * g * dephaseEnd =
      (dephaseEnd * f * dephaseEnd) * (dephaseEnd * g * dephaseEnd) := by
  apply (classical_shadow_composition_iff f g).2
  ext ρ : 1
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply]
  rw [hg, sub_self, map_zero, map_zero]

/-- A class of maps admits the compression as a composition-preserving map if and only if the
obstruction vanishes for every pair in the class. -/
theorem class_compression_iff {ι : Type} [DecidableEq ι] (S : Set (Module.End ℂ (Operator ι))) :
    (∀ f ∈ S, ∀ g ∈ S, dephaseEnd * f * g * dephaseEnd =
        (dephaseEnd * f * dephaseEnd) * (dephaseEnd * g * dephaseEnd)) ↔
      ∀ f ∈ S, ∀ g ∈ S, dephaseEnd * f * (1 - dephaseEnd) * g * dephaseEnd = 0 :=
  ⟨fun h f hf g hg => (classical_shadow_composition_iff f g).1 (h f hf g hg),
    fun h f hf g hg => (classical_shadow_composition_iff f g).2 (h f hf g hg)⟩

/-! ## Theorem `thm:m55-channel-dilation`: the ancilla dimension of the construction -/

/-- Theorem `thm:m55-channel-dilation` with the dimension of the construction: every completely
positive trace-preserving map `Mat n → Mat m` has an isometric dilation with an ancilla of
dimension exactly `n * m`, whose partial trace returns the map on every input matrix. -/
theorem channel_dilation_nm {n m : ℕ} (f : ReconstructionRecovery.Mat n →ₗ[ℂ] ReconstructionRecovery.Mat m)
    (hCP : ReconstructionRecovery.CompletelyPositive f)
    (hTP : ∀ a, ReconstructionRecovery.tr (f a) = ReconstructionRecovery.tr a) :
    ∃ u : Matrix (Fin m × Fin (n * m)) (Fin n) ℂ, u.conjTranspose * u = 1 ∧
      ∀ a i j, f a i j = ∑ k, (u * a * u.conjTranspose) (i, k) (j, k) := by
  obtain ⟨K, hK⟩ := ReconstructionRecovery.completelyPositive_kraus f hCP
  have hKTP : ∀ a : ReconstructionRecovery.Mat n,
      ReconstructionRecovery.tr (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus K a) =
        ReconstructionRecovery.tr a := by
    intro a
    rw [← hK a]
    exact hTP a
  have hKcomplete : (∑ e : Fin n × Fin m, (K e)ᴴ * K e : ReconstructionRecovery.Mat n) = 1 :=
    ReconstructionRecovery.kraus_complete_of_trace_preserving K hKTP
  let ξ : Fin (n * m) ≃ (Fin n × Fin m) := finProdFinEquiv.symm
  let L : Fin (n * m) → Matrix (Fin m) (Fin n) ℂ := fun k => K (ξ k)
  have hLcomplete : (∑ k : Fin (n * m), (L k)ᴴ * L k : ReconstructionRecovery.Mat n) = 1 := by
    change (∑ k : Fin (n * m), (K (ξ k))ᴴ * K (ξ k) : ReconstructionRecovery.Mat n) = 1
    exact (Equiv.sum_comp ξ (fun e : Fin n × Fin m => (K e)ᴴ * K e)).trans hKcomplete
  refine ⟨OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespringV L,
    OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespring_isometry L hLcomplete, ?_⟩
  intro a i j
  calc
    f a i j = (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus K a) i j :=
      congrArg (fun b : ReconstructionRecovery.Mat m => b i j) (hK a)
    _ = (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus L a) i j := by
      simp only [OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus, Matrix.sum_apply]
      change (∑ e : Fin n × Fin m, (K e * a * (K e)ᴴ) i j) =
        (∑ k : Fin (n * m), (K (ξ k) * a * (K (ξ k))ᴴ) i j)
      exact (Equiv.sum_comp ξ (fun e => (K e * a * (K e)ᴴ) i j)).symm
    _ = ∑ k : Fin (n * m), (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespringV L * a *
          (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespringV L)ᴴ) (i, k) (j, k) := by
      simpa only [OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.partialTraceAncilla, Matrix.of_apply] using
        congrArg (fun b : ReconstructionRecovery.Mat m => b i j)
          (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespring_dilates L a)

/-! ## Proposition `prop:same-source-cnot`: the recorded branches on every matrix -/

open scoped Kronecker in
/-- Proposition `prop:same-source-cnot`, the recorded branches: for every complex matrix `A` and
every outcome `y`, the projector `P_y` onto the basis value `y` gives
`P_y Φ(A) P_y = P_y A P_y` for the channel `Φ` of the CNOT construction with the uniform bath. -/
theorem cnot_branch_all_matrices (a : BoundaryReconstruction.Mat 2) (y : Fin 2) :
    Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0) *
        BoundaryReconstruction.Thermal.marginalLeft
          (BoundaryReconstruction.Thermal.rotate
            UniversalObservation.Reconstruction.SourceApexInstrument.cnotUnitary
            (a ⊗ₖ BoundaryReconstruction.Thermal.realDiagonal (fun _ : Fin 2 => (1 : ℝ) / 2))) *
        Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0) =
      Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0) * a *
        Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0) := by
  rw [UniversalObservation.Reconstruction.SourceApexInstrument.cnot_channel_all_matrices]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply]
  by_cases hi : i = y <;> by_cases hj : j = y <;> simp [hi, hj]

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleQuantum
