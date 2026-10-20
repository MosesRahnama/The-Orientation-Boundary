import OperatorKO7.Meta.BoundaryObserver.SourceApex
import Mathlib.Tactic.FinCases

/-!
# Thermal and instrument bridges for the same source

The spectral presentation is tied to matrix entropy and partial traces. The
thermal operation is identified on every matrix before the source instance is
assembled.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Classical Kronecker ComplexOrder

namespace UniversalObservation.Reconstruction

open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

namespace SourceApexInstrument

/-- The spectral basis supplies both inverse equations of one unitary. -/
def spectralUnitary {I : Type} [Fintype I] [DecidableEq I]
    (s : SpectralState I) : Matrix.unitaryGroup I ℂ :=
  ⟨s.basis, s.basis_left, s.basis_right⟩

/-- The declared spectral matrix is the native unitary spectral lift. -/
theorem spectralMatrix_eq_spectralLift {I : Type} [Fintype I] [DecidableEq I]
    (s : SpectralState I) :
    spectralMatrix s = Thermal.spectralLift (spectralUnitary s) s.eigen := rfl

/-- Nonnegative spectral weights give a positive matrix on the original carrier. -/
theorem spectralMatrix_posSemidef {I : Type} [Fintype I] [DecidableEq I]
    (s : SpectralState I) : (spectralMatrix s).PosSemidef :=
  (Matrix.PosSemidef.diagonal (fun i =>
    Complex.zero_le_real.mpr (s.eigen_nonnegative i))).mul_mul_conjTranspose_same s.basis

/-- Spectral normalization gives unit trace for the same matrix. -/
theorem spectralMatrix_trace {I : Type} [Fintype I] [DecidableEq I]
    (s : SpectralState I) : (spectralMatrix s).trace = 1 := by
  rw [posSemidef_trace_ofReal (spectralMatrix_posSemidef s)]
  rw [spectralMatrix_eq_spectralLift, Thermal.spectralLift_trace_re,
    s.eigen_total, Complex.ofReal_one]

/-- The specified entropy agrees with matrix entropy, including zero eigenvalues. -/
theorem spectralEntropy_eq_entropy {I : Type} [Fintype I] [DecidableEq I]
    (s : SpectralState I) : spectralEntropy s = Thermal.entropy (spectralMatrix s) := by
  rw [spectralMatrix_eq_spectralLift, Thermal.entropy_spectralLift]
  unfold spectralEntropy
  calc
    -(∑ i, if s.eigen i = 0 then 0 else s.eigen i * Real.log (s.eigen i)) =
        -(∑ i, s.eigen i * Real.log (s.eigen i)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : s.eigen i = 0
      · rw [h, if_pos rfl, zero_mul]
      · rw [if_neg h]
    _ = ∑ i, Real.negMulLog (s.eigen i) := by
      simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

/-- The identity basis gives the declared diagonal matrix. -/
theorem spectralLift_one {I : Type} [Fintype I] [DecidableEq I] (p : I → ℝ) :
    Thermal.spectralLift (1 : Matrix.unitaryGroup I ℂ) p = Thermal.realDiagonal p := by
  change (1 : Matrix I I ℂ) * Thermal.realDiagonal p * star (1 : Matrix I I ℂ) = _
  rw [one_mul, star_one, mul_one]

/-- The experiment supplies the two inverse equations of its actual joint unitary. -/
def experimentUnitary {n m : ℕ} (e : ThermalExperiment n m) :
    Matrix.unitaryGroup (Fin n × Fin m) ℂ :=
  ⟨e.unitary, e.unitary_left, e.unitary_right⟩

/-- The entire specified channel is the partial trace of the actual joint operation. -/
theorem thermalChannel_eq_marginalLeft {n m : ℕ} (e : ThermalExperiment n m) (a : Mat n) :
    thermalChannel e a =
      Thermal.marginalLeft (Thermal.rotate (experimentUnitary e)
        (a ⊗ₖ spectralMatrix e.initialBath)) := by
  change thermalChannel e a =
    Thermal.marginalLeft (e.unitary * (a ⊗ₖ spectralMatrix e.initialBath) *
      e.unitary.conjTranspose)
  rw [Matrix.mul_assoc]
  ext i j
  simp only [thermalChannel, Thermal.marginalLeft, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_assoc]

/-- The joint-state premise identifies the final state with the same unitary operation. -/
theorem finalJoint_eq_rotate {n m : ℕ} (e : ThermalExperiment n m) :
    spectralMatrix e.finalJoint =
      Thermal.rotate (experimentUnitary e)
        (spectralMatrix e.initialSystem ⊗ₖ spectralMatrix e.initialBath) := by
  change spectralMatrix e.finalJoint =
    e.unitary * (spectralMatrix e.initialSystem ⊗ₖ spectralMatrix e.initialBath) *
      e.unitary.conjTranspose
  rw [Matrix.mul_assoc]
  ext i j
  rw [e.joint_rule]
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum, mul_assoc]

/-- The declared final system is the partial trace of the declared joint state. -/
theorem finalSystem_eq_marginalLeft {n m : ℕ} (e : ThermalExperiment n m) :
    spectralMatrix e.finalSystem = Thermal.marginalLeft (spectralMatrix e.finalJoint) := by
  ext i j
  exact e.marginal_system i j

/-- The declared final bath is the other partial trace of that same joint state. -/
theorem finalBath_eq_marginalRight {n m : ℕ} (e : ThermalExperiment n m) :
    spectralMatrix e.finalBath = Thermal.marginalRight (spectralMatrix e.finalJoint) := by
  ext i j
  exact e.marginal_bath i j

/-- The final system is obtained by applying the entire channel to its actual input. -/
theorem finalSystem_eq_thermalChannel {n m : ℕ} (e : ThermalExperiment n m) :
    spectralMatrix e.finalSystem = thermalChannel e (spectralMatrix e.initialSystem) := by
  rw [thermalChannel_eq_marginalLeft, ← finalJoint_eq_rotate,
    ← finalSystem_eq_marginalLeft]

/-- The initial reservoir is the Gibbs state of the declared diagonal Hamiltonian. -/
theorem initialBath_eq_gibbs {n m : ℕ} (e : ThermalExperiment n m) :
    spectralMatrix e.initialBath =
      Thermal.gibbsState (Thermal.spectralLift_hermitian
        (1 : Matrix.unitaryGroup (Fin m) ℂ) e.energy) e.β := by
  rw [Thermal.gibbsState_spectralLift, spectralLift_one]
  exact e.thermal_matrix

/-- The final joint state is the physical thermal evolution of the actual preparation. -/
theorem finalJoint_eq_thermalJoint {n m : ℕ} [Nonempty (Fin m)]
    (e : ThermalExperiment n m) :
    spectralMatrix e.finalJoint =
      Thermal.thermalJoint (experimentUnitary e) (spectralMatrix e.initialSystem)
        (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) e.energy)
        e.β := by
  rw [Thermal.thermalJoint, ← initialBath_eq_gibbs]
  exact finalJoint_eq_rotate e

/-- The specified heat is the energy increase of this same reservoir. -/
theorem heat_eq_reservoirHeat {n m : ℕ} [Nonempty (Fin m)] (e : ThermalExperiment n m) :
    heat e = Thermal.reservoirHeat (experimentUnitary e) (spectralMatrix e.initialSystem)
      (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) e.energy)
      e.β := by
  rw [Thermal.reservoirHeat, ← finalJoint_eq_thermalJoint,
    ← finalBath_eq_marginalRight, ← initialBath_eq_gibbs,
    Thermal.meanEnergy, spectralLift_one]
  simp only [heat, Thermal.realDiagonal, Matrix.trace, Matrix.diag,
    Matrix.diagonal_mul, Complex.re_sum, Complex.re_ofReal_mul,
    Matrix.sub_apply, Complex.sub_re]

/-- The specified bath term is matrix relative entropy against the same Gibbs reservoir. -/
theorem bathRelativeEntropy_eq_relativeEntropy {n m : ℕ} (e : ThermalExperiment n m) :
    bathRelativeEntropy e =
      Thermal.relativeEntropy (spectralMatrix e.finalBath) (spectralMatrix e.initialBath) := by
  rw [Thermal.relativeEntropy_eq (spectralMatrix_posSemidef e.finalBath).1,
    ← spectralEntropy_eq_entropy]
  have hb : spectralMatrix e.initialBath =
      Thermal.spectralLift (1 : Matrix.unitaryGroup (Fin m) ℂ)
        (bathWeight e.β e.energy) := by
    rw [spectralLift_one]
    exact e.thermal_matrix
  rw [hb, Thermal.matrixLog_spectralLift, spectralLift_one]
  simp only [bathRelativeEntropy, Thermal.realDiagonal, Matrix.trace, Matrix.diag,
    Matrix.mul_diagonal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

end SourceApexInstrument

def ThermalIdentityGoal : Prop :=
  ∀ (n m : ℕ) (e : ThermalExperiment n m),
    e.β * heat e = entropyDrop e + correlation e + bathRelativeEntropy e ∧
    0 ≤ correlation e ∧ 0 ≤ bathRelativeEntropy e

/-! ## Native one-round retained-outcome protocol

The initial record retains preparation metadata. The one-round channel samples
the branch weights. Every output test reads the conditional post-state. The
empty history has zero stopped mass and a total record derived from the laws.
-/
theorem thermalIdentityGoal : ThermalIdentityGoal := by
  intro n m e
  letI : Nonempty (Fin m) := ⟨⟨0, e.bath_positive⟩⟩
  have h := Thermal.thermal_information_balance
    (SourceApexInstrument.experimentUnitary e)
    (SourceApexInstrument.spectralMatrix_posSemidef e.initialSystem)
    (SourceApexInstrument.spectralMatrix_trace e.initialSystem)
    (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) e.energy) e.β
  dsimp only at h
  rw [← SourceApexInstrument.heat_eq_reservoirHeat e] at h
  simp only [← SourceApexInstrument.finalJoint_eq_thermalJoint e,
    Thermal.mutualInfo, ← SourceApexInstrument.finalSystem_eq_marginalLeft e,
    ← SourceApexInstrument.finalBath_eq_marginalRight e,
    ← SourceApexInstrument.initialBath_eq_gibbs e,
    ← SourceApexInstrument.bathRelativeEntropy_eq_relativeEntropy e,
    ← SourceApexInstrument.spectralEntropy_eq_entropy] at h
  exact h


namespace SourceApexInstrument

/-- Every positive matrix of unit trace has a spectral presentation on its own carrier. -/
def spectralStateOfMatrix {I : Type} [Fintype I] [DecidableEq I]
    (a : Matrix I I ℂ) (ha : a.PosSemidef) (ht : a.trace = 1) : SpectralState I where
  eigen := ha.1.eigenvalues
  eigen_nonnegative := ha.eigenvalues_nonneg
  eigen_total := (Thermal.eigenvalues_sum_trace ha.1).trans (congrArg Complex.re ht)
  basis := ha.1.eigenvectorUnitary
  basis_left := unitary.coe_star_mul_self ha.1.eigenvectorUnitary
  basis_right := unitary.coe_mul_star_self ha.1.eigenvectorUnitary

/-- The constructed presentation has exactly the supplied matrix. -/
theorem spectralMatrix_ofMatrix {I : Type} [Fintype I] [DecidableEq I]
    (a : Matrix I I ℂ) (ha : a.PosSemidef) (ht : a.trace = 1) :
    spectralMatrix (spectralStateOfMatrix a ha ht) = a :=
  Thermal.spectralLift_eigenvalues ha.1

section UnitaryExperiments

variable {n m : ℕ}
variable (hn : 0 < n) (hm : 0 < m) (β : ℝ) (hβ : 0 < β)
variable (energy : Fin m → ℝ) (initial : SpectralState (Fin n))
variable (u : Matrix.unitaryGroup (Fin n × Fin m) ℂ)

/-- One supplied unitary, Gibbs reservoir and actual initial state construct every
field of the specified experiment. Final spectra come from the evolved matrices. -/
def thermalExperimentOfUnitary : ThermalExperiment n m := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let hh := Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) energy
  let bath := Thermal.gibbsState hh β
  let joint := Thermal.thermalJoint u (spectralMatrix initial) hh β
  have hj : joint.PosSemidef ∧ joint.trace = 1 :=
    Thermal.thermalJoint_density u (spectralMatrix_posSemidef initial)
      (spectralMatrix_trace initial) hh β
  refine
    { system_positive := hn
      bath_positive := hm
      β := β
      β_positive := hβ
      energy := energy
      initialSystem := initial
      initialBath := spectralStateOfMatrix bath (Thermal.gibbsState_posDef hh β).posSemidef
        (Thermal.gibbsState_trace hh β)
      thermal_matrix := ?_
      unitary := u
      unitary_left := unitary.coe_star_mul_self u
      unitary_right := unitary.coe_mul_star_self u
      finalSystem := spectralStateOfMatrix (Thermal.marginalLeft joint)
        (Thermal.marginalLeft_posSemidef hj.1)
        ((Thermal.marginalLeft_trace joint).trans hj.2)
      finalBath := spectralStateOfMatrix (Thermal.marginalRight joint)
        (Thermal.marginalRight_posSemidef hj.1)
        ((Thermal.marginalRight_trace joint).trans hj.2)
      finalJoint := spectralStateOfMatrix joint hj.1 hj.2
      joint_rule := ?_
      marginal_system := ?_
      marginal_bath := ?_ }
  · rw [spectralMatrix_ofMatrix]
    change Thermal.gibbsState
      (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) energy) β = _
    rw [Thermal.gibbsState_spectralLift, spectralLift_one]
    rfl
  · intro i j
    simp only [spectralMatrix_ofMatrix]
    change ((u : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) *
      (spectralMatrix initial ⊗ₖ bath) *
      (u : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ).conjTranspose) i j = _
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, mul_assoc]
  · intro i j
    rw [spectralMatrix_ofMatrix, spectralMatrix_ofMatrix]
    rfl
  · intro r s
    rw [spectralMatrix_ofMatrix, spectralMatrix_ofMatrix]
    rfl

/-- The initial preparation is retained as the exact supplied spectral state. -/
theorem thermalExperimentOfUnitary_initial :
    (thermalExperimentOfUnitary hn hm β hβ energy initial u).initialSystem = initial := rfl

/-- The constructed initial bath is the Gibbs matrix of the same declared Hamiltonian. -/
theorem thermalExperimentOfUnitary_initialBath :
    spectralMatrix (thermalExperimentOfUnitary hn hm β hβ energy initial u).initialBath =
      Thermal.gibbsState
        (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) energy) β := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact spectralMatrix_ofMatrix _
    (Thermal.gibbsState_posDef
      (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) energy) β).posSemidef
    (Thermal.gibbsState_trace
      (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) energy) β)

/-- The supplied unitary determines the constructed channel on every matrix. -/
theorem thermalExperimentOfUnitary_channel (a : Mat n) :
    thermalChannel (thermalExperimentOfUnitary hn hm β hβ energy initial u) a =
      Thermal.marginalLeft (Thermal.rotate u
        (a ⊗ₖ Thermal.gibbsState
          (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin m) ℂ) energy) β)) := by
  rw [thermalChannel_eq_marginalLeft, thermalExperimentOfUnitary_initialBath]; rfl

/-- The constructed experiment satisfies the exact heat balance and both signs. -/
theorem thermalExperimentOfUnitary_balance :
    let e := thermalExperimentOfUnitary hn hm β hβ energy initial u
    e.β * heat e = entropyDrop e + correlation e + bathRelativeEntropy e ∧
      0 ≤ correlation e ∧ 0 ≤ bathRelativeEntropy e :=
  thermalIdentityGoal n m (thermalExperimentOfUnitary hn hm β hβ energy initial u)

end UnitaryExperiments

end SourceApexInstrument


namespace SourceApexInstrument

/-- Controlled addition on the two binary coordinates defines the joint operation. -/
def cnotMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2 = j.1 + j.2 then 1 else 0

/-- Both inverse equations hold on the complete four-dimensional carrier. -/
def cnotUnitary : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  have h11 : (1 : Fin 2) + 1 = 0 := rfl
  refine ⟨cnotMatrix, ?_, ?_⟩
  · change cnotMatrix.conjTranspose * cnotMatrix = 1
    ext ⟨i, r⟩ ⟨j, s⟩
    fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases s <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, cnotMatrix,
        Fintype.sum_prod_type, Fin.sum_univ_two, h11]
  · change cnotMatrix * cnotMatrix.conjTranspose = 1
    ext ⟨i, r⟩ ⟨j, s⟩
    fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases s <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, cnotMatrix,
        Fintype.sum_prod_type, Fin.sum_univ_two, h11]

/-- The zero Hamiltonian gives the uniform binary Gibbs state at every temperature. -/
theorem cnotGibbsState (β : ℝ) :
    Thermal.gibbsState
      (Thermal.spectralLift_hermitian (1 : Matrix.unitaryGroup (Fin 2) ℂ)
        (fun _ : Fin 2 => (0 : ℝ))) β =
      Thermal.realDiagonal (fun _ : Fin 2 => (1 : ℝ) / 2) := by
  rw [Thermal.gibbsState_spectralLift, spectralLift_one]
  apply congrArg Thermal.realDiagonal
  funext r
  norm_num [Thermal.gibbsWeight, Thermal.partition, Fin.sum_univ_two]

/-- The joint unitary and its Gibbs reservoir implement dephasing on every matrix. -/
theorem cnot_channel_all_matrices (a : Mat 2) :
    Thermal.marginalLeft (Thermal.rotate cnotUnitary
      (a ⊗ₖ Thermal.realDiagonal (fun _ : Fin 2 => (1 : ℝ) / 2))) =
      Matrix.diagonal (fun i => a i i) := by
  have h11 : (1 : Fin 2) + 1 = 0 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Thermal.marginalLeft, Thermal.rotate, cnotUnitary, cnotMatrix,
      Matrix.mul_apply, Matrix.star_apply, Matrix.kronecker_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Thermal.realDiagonal, h11] <;> ring

/-- The same CNOT operation constructs a physical experiment for every initial state. -/
def cnotThermalExperiment (initial : SpectralState (Fin 2)) : ThermalExperiment 2 2 :=
  thermalExperimentOfUnitary (by decide) (by decide) 1 (by norm_num)
    (fun _ : Fin 2 => (0 : ℝ)) initial cnotUnitary

/-- The constructed experiment has the declared operation on all matrix inputs. -/
theorem cnotThermalExperiment_channel (initial : SpectralState (Fin 2)) (a : Mat 2) :
    thermalChannel (cnotThermalExperiment initial) a = Matrix.diagonal (fun i => a i i) := by
  rw [cnotThermalExperiment, thermalExperimentOfUnitary_channel,
    cnotGibbsState, cnot_channel_all_matrices]

/-! ## Finite quantum projective source

Every coordinate operation is a linear map on the full matrix algebra. The
positive-dimensional quantum source provides normalized outputs for zero-weight
branches. The operation identification is stated for every matrix input.
-/
theorem cnotThermalExperiment_heat (initial : SpectralState (Fin 2)) :
    heat (cnotThermalExperiment initial) = 0 := by
  change (∑ r : Fin 2, (0 : ℝ) *
    ((spectralMatrix (cnotThermalExperiment initial).finalBath r r).re -
      (spectralMatrix (cnotThermalExperiment initial).initialBath r r).re)) = 0
  simp only [zero_mul, Finset.sum_const_zero]

/-- The uniform binary source preparation has its own normalized spectral presentation. -/
def cnotUniformInput : SpectralState (Fin 2) where
  eigen _ := 1 / 2
  eigen_nonnegative _ := by norm_num
  eigen_total := by norm_num [Fin.sum_univ_two]
  basis := 1
  basis_left := by rw [Matrix.conjTranspose_one, one_mul]
  basis_right := by rw [Matrix.conjTranspose_one, mul_one]

/-- The source preparation is the uniform density matrix in the stated coordinates. -/
theorem cnotUniformMatrix :
    spectralMatrix cnotUniformInput = Thermal.realDiagonal (fun _ : Fin 2 => (1 : ℝ) / 2) := by
  change (1 : Mat 2) * Thermal.realDiagonal (fun _ : Fin 2 => (1 : ℝ) / 2) *
    (1 : Mat 2).conjTranspose = _
  rw [Matrix.conjTranspose_one, one_mul, mul_one]

/-- A normalized coherent ray is a second physical preparation of the same quantum source. -/
def cnotCoherentState : quantumData.State qubit :=
  rayState (fun _ : Fin 2 => (1 : ℂ)) (by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num at h0)

/-- Every matrix entry of the coherent preparation is one half. -/
theorem cnotCoherentState_entry (i j : Fin 2) :
    cnotCoherentState.val i j = (1 / 2 : ℂ) := by
  change ((((sqLength (fun _ : Fin 2 => (1 : ℂ)))⁻¹ : ℝ) : ℂ) *
    ((1 : ℂ) * star (1 : ℂ))) = (1 / 2 : ℂ)
  norm_num [sqLength, dotProduct, Fin.sum_univ_two]

/-- Agreement at the initial uniform state leaves a different operation on a coherent state. -/
theorem cnot_endpoint_agreement_not_operation :
    let e := cnotThermalExperiment cnotUniformInput
    thermalChannel e (spectralMatrix cnotUniformInput) = spectralMatrix cnotUniformInput ∧
      thermalChannel e cnotCoherentState.val ≠ cnotCoherentState.val := by
  dsimp only
  constructor
  · rw [cnotThermalExperiment_channel, cnotUniformMatrix]
    simp only [Thermal.realDiagonal, Matrix.diagonal_apply_eq]
  · intro he
    have h := congrArg (fun a : Mat 2 => a 0 1) he
    dsimp only at h
    rw [cnotThermalExperiment_channel, Matrix.diagonal_apply,
      if_neg (by decide : (0 : Fin 2) ≠ 1), cnotCoherentState_entry] at h
    norm_num at h

end SourceApexInstrument


namespace SourceApexInstrument

/-- The trace of a represented branch is its native weight, including zero weight. -/
theorem realization_map_trace
    {D : OperationalData} (r : QuantumRealization D) {A B : D.Obj}
    (f : D.Process A B) (s : D.State A) :
    (tr (r.maps A B f (r.states A s).val)).re = D.weight f s := by
  rw [r.source_action A B f s]
  change (Matrix.trace ((D.weight f s : ℂ) •
    (r.states B (D.act f s)).val)).re = D.weight f s
  rw [Matrix.trace_smul]
  change ((D.weight f s : ℂ) * tr (r.states B (D.act f s)).val).re = D.weight f s
  rw [density_tr, mul_one, Complex.ofReal_re]

/-- A Hermitian idempotent gives the same record trace with one or two factors. -/
theorem projector_trace_sandwich {n : ℕ} (P a : Mat n)
    (hdagger : dagger P = P) (hidempotent : P * P = P) :
    tr (P * a * dagger P) = tr (P * a) := by
  rw [hdagger]
  change Matrix.trace ((P * a) * P) = Matrix.trace (P * a)
  rw [Matrix.trace_mul_comm (P * a) P, ← Matrix.mul_assoc, hidempotent]

section SourceEnsembles

variable {D : OperationalData} {A : D.Obj} {R H0 Z Act Y : Type}
variable [Fintype H0] [Fintype Z] [Fintype Act] [Fintype Y]

/-- The actual initial joint law weights the represented native preparations. -/
def sourceEnsemble (r : QuantumRealization D)
    (d : SourceProtocolData D A R H0 Z Act Y) : Mat (r.dim A) :=
  ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0, z) : ℂ) •
    (r.states A (d.initial h0 z)).val

/-- The ensemble matrix has exactly the entries used in the source specification. -/
theorem sourceEnsemble_entry (r : QuantumRealization D)
    (d : SourceProtocolData D A R H0 Z Act Y) (i j : Fin (r.dim A)) :
    sourceEnsemble r d i j =
      ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0, z) : ℂ) *
        (r.states A (d.initial h0 z)).val i j := by
  simp only [sourceEnsemble, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- The full implemented source operation transports the entire preparation ensemble. -/
theorem source_final_ensemble [Fintype R]
    (p : RecordedProcess D A R) (r : QuantumRealization D)
    (d : SourceProtocolData D A R H0 Z Act Y) {m : ℕ}
    (e : ThermalExperiment (r.dim A) m) (P : R → Mat (r.dim A))
    (himplementation : ImplementsInstrument D A R p r e P)
    (hinitial : spectralMatrix e.initialSystem = sourceEnsemble r d) :
    spectralMatrix e.finalSystem =
      ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0, z) : ℂ) •
        (r.states A (D.act p.total (d.initial h0 z))).val := by
  calc
    spectralMatrix e.finalSystem =
        thermalChannel e (spectralMatrix e.initialSystem) :=
      finalSystem_eq_thermalChannel e
    _ = r.maps A A p.total (spectralMatrix e.initialSystem) :=
      himplementation.2.2.2.1 _
    _ = ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0, z) : ℂ) •
        r.maps A A p.total (r.states A (d.initial h0 z)).val := by
      rw [hinitial]
      simp only [sourceEnsemble, map_sum, LinearMap.map_smul]
    _ = ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0, z) : ℂ) •
        (r.states A (D.act p.total (d.initial h0 z))).val := by
      apply Finset.sum_congr rfl
      intro h0 _
      apply Finset.sum_congr rfl
      intro z _
      rw [r.source_action A A p.total (d.initial h0 z),
        p.total_weight, Complex.ofReal_one, one_smul]

/-- The output projectors recover the native branch probabilities for the same ensemble. -/
theorem source_record_ensemble [Fintype R]
    (p : RecordedProcess D A R) (r : QuantumRealization D)
    (d : SourceProtocolData D A R H0 Z Act Y) {m : ℕ}
    (e : ThermalExperiment (r.dim A) m) (P : R → Mat (r.dim A))
    (himplementation : ImplementsInstrument D A R p r e P)
    (hinitial : spectralMatrix e.initialSystem = sourceEnsemble r d) (y : R) :
    (tr (P y * spectralMatrix e.finalSystem)).re =
      ∑ h0, ∑ z, d.protocol.initialJoint.mass (h0, z) *
        D.weight (p.branch y) (d.initial h0 z) := by
  rw [finalSystem_eq_thermalChannel]
  calc
    (tr (P y * thermalChannel e (spectralMatrix e.initialSystem))).re =
        (tr (P y * thermalChannel e (spectralMatrix e.initialSystem) *
          dagger (P y))).re :=
      congrArg Complex.re
        (projector_trace_sandwich (P y)
          (thermalChannel e (spectralMatrix e.initialSystem))
          (himplementation.1 y).1 (himplementation.1 y).2).symm
    _ = (tr (r.maps A A (p.branch y) (spectralMatrix e.initialSystem))).re :=
      congrArg (fun a : Mat (r.dim A) => (tr a).re)
        (himplementation.2.2.2.2.1 y _)
    _ = ∑ h0, ∑ z, d.protocol.initialJoint.mass (h0, z) *
        (tr (r.maps A A (p.branch y) (r.states A (d.initial h0 z)).val)).re := by
      rw [hinitial]
      simp only [sourceEnsemble, map_sum, LinearMap.map_smul, tr,
        Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
        smul_eq_mul, Complex.re_ofReal_mul]
    _ = ∑ h0, ∑ z, d.protocol.initialJoint.mass (h0, z) *
        D.weight (p.branch y) (d.initial h0 z) := by
      apply Finset.sum_congr rfl
      intro h0 _
      apply Finset.sum_congr rfl
      intro z _
      rw [realization_map_trace]

end SourceEnsembles

end SourceApexInstrument

/-- Every actually implemented source with its own ensemble and resource coordinates
satisfies the complete Apex target for the constructed native one-round protocol.
The final ensemble, retained-record probabilities and thermal balance are conclusions. -/
theorem sourceOneRound_apex_of_implementation
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [DecidableEq R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (recordLaw : OperatorKO7.Meta.BoundaryObserver.ProtocolResolution.FiniteLaw H0)
    (prior : H0 → OperatorKO7.Meta.BoundaryObserver.ProtocolResolution.FiniteLaw Z)
    (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h)
    (cost : RecordedProcess D A R → ℕ → ℝ)
    (r : QuantumRealization D) {m : ℕ}
    (e : ThermalExperiment (r.dim A) m) (P : R → Mat (r.dim A))
    (himplementation : ImplementsInstrument D A R p r e P)
    (hinitial : spectralMatrix e.initialSystem =
      SourceApexInstrument.sourceEnsemble r
        (sourceOneRoundData hL p recordLaw prior prepare charge hcharge))
    (hheat : cost p 0 = heat e)
    (hcost : cost p 1 = Protocol.conditionalExpectedCost
      (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).protocol
      (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).rounds
      (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).bank) :
    ApexInstanceGoal D A R H0 Z Unit R (recordedSourceContract p cost) p
      (recordedSourceBinding p cost)
      (sourceOneRoundData hL p recordLaw prior prepare charge hcharge) m := by
  let d := sourceOneRoundData hL p recordLaw prior prepare charge hcharge
  have hpre := sourceApex_prephysical D A R H0 Z Unit R p cost d
  have hthermal := thermalIdentityGoal (r.dim A) m e
  refine ⟨hL, hpre.1, hpre.2.1,
    sourceOneRound_sourceProtocolLink hL p recordLaw prior prepare charge hcharge,
    hpre.2.2.1, hpre.2.2.2, r, e, P, himplementation,
    sourceDemandQuantumGoal D A R p (recordedSourceContract p cost)
      (recordedSourceBinding p cost) r,
    ?_, ?_, ?_, hheat, hcost, hthermal.1, hthermal.2.1, hthermal.2.2⟩
  · intro i j
    calc
      spectralMatrix e.initialSystem i j =
          SourceApexInstrument.sourceEnsemble r d i j :=
        congrArg (fun a : Mat (r.dim A) => a i j) hinitial
      _ = ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0, z) : ℂ) *
          (r.states A (d.initial h0 z)).val i j :=
        SourceApexInstrument.sourceEnsemble_entry r d i j
  · intro i j
    have h := congrArg (fun a : Mat (r.dim A) => a i j)
      (SourceApexInstrument.source_final_ensemble p r d e P
        himplementation hinitial)
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h
  · exact SourceApexInstrument.source_record_ensemble p r d e P
      himplementation hinitial


namespace SourceApexInstrument

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution

/-- The two basis preparations have equal, explicitly normalized prior mass. -/
def cnotPrior : FiniteLaw (Fin 2) where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  total := by norm_num [Fin.sum_univ_two]

/-- The concrete source contains both native branches and the same total dephasing map. -/
def cnotSource : RecordedProcess quantumData qubit (Fin 2) :=
  sourceProjectiveRecordedProcess qubit

/-- Every candidate is run with the same preparation law and one unit charge per reading. -/
def cnotProtocolData (q : RecordedProcess quantumData qubit (Fin 2)) :
    SourceProtocolData quantumData qubit (Fin 2) Unit (Fin 2) Unit (Fin 2) :=
  sourceOneRoundData quantumData_operationalLaws q unitLaw
    (fun _ => cnotPrior) (fun _ z => basisState qubit z)
    (fun _ _ => 1) (fun _ _ => zero_le_one)

/-- The physical witness uses the same uniform source ensemble and zero-energy Gibbs bath. -/
def cnotSourceExperiment : ThermalExperiment 2 2 :=
  cnotThermalExperiment cnotUniformInput

/-- Coordinate zero records heat and coordinate one records the single paid reading. -/
def cnotResourceCost (_q : RecordedProcess quantumData qubit (Fin 2)) (k : ℕ) : ℝ :=
  if k = 1 then 1 else 0

/-- The native demand contract retains the actual source operations and their resource values. -/
def cnotSourceContract : Completion.SourceContract :=
  recordedSourceContract cnotSource cnotResourceCost

/-- Identity equivalences bind every demand input and outcome to that same quantum source. -/
def cnotSourceBinding :
    SourceBinding quantumData qubit (Fin 2) cnotSource cnotSourceContract :=
  recordedSourceBinding cnotSource cnotResourceCost

/-- The actual basis preparation has its stated matrix entries. -/
theorem cnotPreparation_entry (z i j : Fin 2) :
    (basisState qubit z).val i j = if i = z ∧ j = z then 1 else 0 := by
  rw [basisState_val]
  exact unitEntry_apply z z i j

/-- The retained unit record and binary prior determine each initial joint cell. -/
theorem cnotInitialJoint_mass (q : RecordedProcess quantumData qubit (Fin 2))
    (u : Unit) (z : Fin 2) :
    (cnotProtocolData q).protocol.initialJoint.mass (u, z) = 1 / 2 := by
  change (1 : ℝ) * (1 / 2) = 1 / 2
  exact one_mul _

/-- The actual stopped-history cost is one for every native candidate in this contract. -/
theorem cnotProtocol_expectedCost (q : RecordedProcess quantumData qubit (Fin 2)) :
    Protocol.conditionalExpectedCost (cnotProtocolData q).protocol
      (cnotProtocolData q).rounds (cnotProtocolData q).bank = 1 := by
  change conditionalExpectedCost
    (sourceOneRoundConditional quantumData_operationalLaws q unitLaw
      (fun _ => cnotPrior) (fun _ z => basisState qubit z)
      (fun _ _ => 1) (fun _ _ => zero_le_one))
    1 (historyBank Unit (Fin 2) 1) = 1
  rw [sourceOneRound_conditionalExpectedCost]
  change (∑ _u : Unit, (1 : ℝ) * 1) = 1
  rw [source_sum_unit, one_mul]

/-- The CNOT experiment implements both branches and their total map on every matrix. -/
theorem cnotInstrument :
    ImplementsInstrument quantumData qubit (Fin 2) cnotSource
      quantumData_realization cnotSourceExperiment sourceCoordinateProjector := by
  apply sourceProjective_implementsInstrument_of_channel qubit cnotSourceExperiment
  intro a
  exact cnotThermalExperiment_channel cnotUniformInput a

/-- The physical initial density is exactly the mixture of this protocol's preparations. -/
theorem cnotInitialEnsemble :
    spectralMatrix cnotSourceExperiment.initialSystem =
      sourceEnsemble quantumData_realization (cnotProtocolData cnotSource) := by
  change spectralMatrix cnotUniformInput =
    sourceEnsemble quantumData_realization (cnotProtocolData cnotSource)
  rw [cnotUniformMatrix]
  ext i j
  rw [sourceEnsemble_entry]
  simp only [cnotInitialJoint_mass]
  change Thermal.realDiagonal (fun _ : Fin 2 => (1 : ℝ) / 2) i j =
    ∑ _u : Unit, ∑ z : Fin 2, ((1 / 2 : ℝ) : ℂ) * (basisState qubit z).val i j
  rw [source_sum_unit]
  simp only [cnotPreparation_entry]
  fin_cases i <;> fin_cases j <;>
    norm_num [Thermal.realDiagonal, Fin.sum_univ_two]

end SourceApexInstrument

/-- Proves the declared `ApexInstanceGoal` for the constructed quantum source,
instrument, preparation ensemble, protocol, and thermal experiment. The
physical-balance and information bounds appear as conclusions in that type. -/
theorem apexInstanceGoal :
    ApexInstanceGoal quantumData qubit (Fin 2) Unit (Fin 2) Unit (Fin 2)
      SourceApexInstrument.cnotSourceContract SourceApexInstrument.cnotSource
      SourceApexInstrument.cnotSourceBinding
      (SourceApexInstrument.cnotProtocolData SourceApexInstrument.cnotSource) 2 := by
  apply sourceOneRound_apex_of_implementation
    quantumData_operationalLaws SourceApexInstrument.cnotSource
    OperatorKO7.Meta.BoundaryObserver.ProtocolResolution.unitLaw
    (fun _ => SourceApexInstrument.cnotPrior) (fun _ z => basisState qubit z)
    (fun _ _ => 1) (fun _ _ => zero_le_one) SourceApexInstrument.cnotResourceCost
    quantumData_realization SourceApexInstrument.cnotSourceExperiment
    sourceCoordinateProjector SourceApexInstrument.cnotInstrument
    SourceApexInstrument.cnotInitialEnsemble
  · change 0 = heat
      (SourceApexInstrument.cnotThermalExperiment SourceApexInstrument.cnotUniformInput)
    exact
      (SourceApexInstrument.cnotThermalExperiment_heat SourceApexInstrument.cnotUniformInput).symm
  · change 1 = Protocol.conditionalExpectedCost
      (SourceApexInstrument.cnotProtocolData SourceApexInstrument.cnotSource).protocol
      (SourceApexInstrument.cnotProtocolData SourceApexInstrument.cnotSource).rounds
      (SourceApexInstrument.cnotProtocolData SourceApexInstrument.cnotSource).bank
    exact (SourceApexInstrument.cnotProtocol_expectedCost SourceApexInstrument.cnotSource).symm


namespace SourceApexInstrument

/-- Each native retained outcome reads the corresponding basis preparation with certainty. -/
theorem cnot_native_branch_weight (z y : Fin 2) :
    quantumData.weight (cnotSource.branch y) (basisState qubit z) =
      if y = z then 1 else 0 := by
  change (tr (sourceCoordinateMap y (basisState qubit z).val)).re =
    if y = z then 1 else 0
  rw [sourceCoordinateMap_trace, cnotPreparation_entry]
  by_cases h : y = z
  · rw [if_pos ⟨h, h⟩, if_pos h, Complex.one_re]
  · rw [if_neg (fun h' => h h'.1), if_neg h, Complex.zero_re]

/-- The same source distinguishes two pure physical preparations by an actual retained record. -/
theorem cnot_nontrivial_record :
    ∃ s t : quantumData.State qubit,
      s ≠ t ∧ Pure quantumData s ∧ Pure quantumData t ∧
        quantumData.weight (cnotSource.branch 0) s = 1 ∧
        quantumData.weight (cnotSource.branch 0) t = 0 := by
  have hs : quantumData.weight (cnotSource.branch 0) (basisState qubit (0 : Fin 2)) = 1 := by
    rw [cnot_native_branch_weight, if_pos rfl]
  have ht : quantumData.weight (cnotSource.branch 0) (basisState qubit (1 : Fin 2)) = 0 := by
    rw [cnot_native_branch_weight, if_neg (by decide : (0 : Fin 2) ≠ 1)]
  refine ⟨basisState qubit (0 : Fin 2), basisState qubit (1 : Fin 2), ?_,
    basisState_pure qubit (0 : Fin 2), basisState_pure qubit (1 : Fin 2), hs, ht⟩
  intro he
  have h := congrArg (quantumData.weight (cnotSource.branch 0)) he
  rw [hs, ht] at h
  exact one_ne_zero h

end SourceApexInstrument

end UniversalObservation.Reconstruction
