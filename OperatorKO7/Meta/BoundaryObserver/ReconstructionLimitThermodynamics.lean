import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
import OperatorKO7.Meta.BoundaryObserver.ThermalReset
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitThermodynamics

noncomputable section

open BoundaryReconstruction.Thermal
open scoped BigOperators ComplexOrder Kronecker ENNReal

/-- The last coordinate contains the entire remaining geometric tail. -/
def geometricWeight (q : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val < n then (1 - q) * q ^ i.val else q ^ n

theorem geometricWeight_castSucc (q : ℝ) (n : ℕ) (i : Fin n) :
    geometricWeight q n i.castSucc = (1 - q) * q ^ i.val := by
  change (if i.val < n then (1 - q) * q ^ i.val else q ^ n) = _
  exact if_pos i.isLt

theorem geometricWeight_last (q : ℝ) (n : ℕ) :
    geometricWeight q n (Fin.last n) = q ^ n := by
  change (if n < n then (1 - q) * q ^ n else q ^ n) = _
  exact if_neg (by omega)

theorem geometricWeight_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) (i : Fin (n + 1)) : 0 < geometricWeight q n i := by
  have hbase : 0 < 1 - q := by linarith
  unfold geometricWeight
  split_ifs <;> positivity

theorem geometricWeight_sum (q : ℝ) (n : ℕ) :
    (∑ i : Fin (n + 1), geometricWeight q n i) = 1 := by
  rw [Fin.sum_univ_castSucc, geometricWeight_last]
  have hfirst :
      (∑ i : Fin n, geometricWeight q n i.castSucc) = 1 - q ^ n := by
    calc
      (∑ i : Fin n, geometricWeight q n i.castSucc) =
          ∑ i : Fin n, (1 - q) * q ^ i.val :=
        Finset.sum_congr rfl (fun i _ => geometricWeight_castSucc q n i)
      _ = (1 - q) * ∑ i : Fin n, q ^ i.val := by rw [← Finset.mul_sum]
      _ = (1 - q) * ∑ i ∈ Finset.range n, q ^ i := by
        rw [Fin.sum_univ_eq_sum_range]
      _ = 1 - q ^ n := mul_neg_geom_sum q n
  rw [hfirst]
  ring

/-- The finite state is the native complex diagonal matrix of the cutoff weights. -/
def geometricDensity (q : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  realDiagonal (geometricWeight q n)

theorem realDiagonal_trace {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    (realDiagonal p).trace = ((∑ i, p i : ℝ) : ℂ) := by
  rw [realDiagonal, Matrix.trace_diagonal, Complex.ofReal_sum]

theorem geometricDensity_posDef {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (geometricDensity q n).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact Complex.zero_lt_real.mpr (geometricWeight_pos hq0 hq1 n i)

theorem geometricDensity_trace (q : ℝ) (n : ℕ) :
    (geometricDensity q n).trace = 1 := by
  change (realDiagonal (geometricWeight q n)).trace = 1
  rw [realDiagonal_trace, geometricWeight_sum, Complex.ofReal_one]

theorem geometricDensity_density {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (geometricDensity q n).PosSemidef ∧ (geometricDensity q n).trace = 1 :=
  ⟨(geometricDensity_posDef hq0 hq1 n).posSemidef, geometricDensity_trace q n⟩

theorem spectralLift_one {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    spectralLift (1 : Matrix.unitaryGroup ι ℂ) p = realDiagonal p := by
  simp only [spectralLift, rotate, Matrix.UnitaryGroup.one_val, star_one, one_mul, mul_one]

/-- Native matrix entropy equals the finite entropy of the displayed diagonal entries. -/
theorem entropy_realDiagonal {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    entropy (realDiagonal p) = ∑ i, Real.negMulLog (p i) := by
  rw [← spectralLift_one p, entropy_spectralLift]

theorem geometricDensity_entropy (q : ℝ) (n : ℕ) :
    entropy (geometricDensity q n) =
      ∑ i : Fin (n + 1), Real.negMulLog (geometricWeight q n i) :=
  entropy_realDiagonal (geometricWeight q n)

theorem geometricDensity_entropy_split (q : ℝ) (n : ℕ) :
    entropy (geometricDensity q n) =
      (∑ i ∈ Finset.range n, Real.negMulLog ((1 - q) * q ^ i)) +
        Real.negMulLog (q ^ n) := by
  rw [geometricDensity_entropy, Fin.sum_univ_castSucc, geometricWeight_last]
  have hfirst :
      (∑ i : Fin n, Real.negMulLog (geometricWeight q n i.castSucc)) =
        ∑ i ∈ Finset.range n, Real.negMulLog ((1 - q) * q ^ i) := by
    calc
      (∑ i : Fin n, Real.negMulLog (geometricWeight q n i.castSucc)) =
          ∑ i : Fin n, Real.negMulLog ((1 - q) * q ^ i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [geometricWeight_castSucc]
      _ = ∑ i ∈ Finset.range n, Real.negMulLog ((1 - q) * q ^ i) :=
        Fin.sum_univ_eq_sum_range (fun i => Real.negMulLog ((1 - q) * q ^ i)) n
  rw [hfirst]

def selectedDensity (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  geometricDensity (1 / 2) n

def selectedBathDensity (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  geometricDensity (1 / 4) n

theorem selectedDensity_density (n : ℕ) :
    (selectedDensity n).PosSemidef ∧ (selectedDensity n).trace = 1 :=
  geometricDensity_density (by norm_num) (by norm_num) n

theorem selectedBathDensity_density (n : ℕ) :
    (selectedBathDensity n).PosSemidef ∧ (selectedBathDensity n).trace = 1 :=
  geometricDensity_density (by norm_num) (by norm_num) n

/-- The logarithmic energy realizes a positive probability vector at inverse temperature one. -/
def logEnergy {ι : Type} (p : ι → ℝ) (i : ι) : ℝ :=
  -Real.log (p i)

theorem gibbsWeight_logEnergy {ι : Type} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    gibbsWeight 1 (logEnergy p) = p := by
  have hexp : ∀ i, Real.exp (-(1 : ℝ) * logEnergy p i) = p i := by
    intro i
    have he : -(1 : ℝ) * logEnergy p i = Real.log (p i) := by
      unfold logEnergy
      ring
    rw [he]
    exact Real.exp_log (hp i)
  have hpartition : partition 1 (logEnergy p) = 1 := by
    unfold partition
    calc
      (∑ i, Real.exp (-(1 : ℝ) * logEnergy p i)) = ∑ i, p i :=
        Finset.sum_congr rfl (fun i _ => hexp i)
      _ = 1 := hsum
  funext i
  rw [gibbsWeight, hpartition, hexp, div_one]

theorem gibbsState_realDiagonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) (β : ℝ) :
    gibbsState (realDiagonal_hermitian energy) β =
      realDiagonal (gibbsWeight β energy) := by
  calc
    gibbsState (realDiagonal_hermitian energy) β =
        gibbsState (spectralLift_hermitian (1 : Matrix.unitaryGroup ι ℂ) energy) β :=
      gibbsState_congr _ _ (spectralLift_one energy).symm β
    _ = spectralLift (1 : Matrix.unitaryGroup ι ℂ) (gibbsWeight β energy) :=
      gibbsState_spectralLift (1 : Matrix.unitaryGroup ι ℂ) energy β
    _ = realDiagonal (gibbsWeight β energy) := spectralLift_one _

theorem gibbsState_logEnergy {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    gibbsState (realDiagonal_hermitian (logEnergy p)) 1 = realDiagonal p := by
  rw [gibbsState_realDiagonal, gibbsWeight_logEnergy p hp hsum]

def geometricEnergy (r : ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  logEnergy (geometricWeight r n)

def geometricHamiltonian (r : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  realDiagonal (geometricEnergy r n)

theorem geometricHamiltonian_hermitian (r : ℝ) (n : ℕ) :
    (geometricHamiltonian r n).IsHermitian :=
  realDiagonal_hermitian (geometricEnergy r n)

theorem geometricGibbs_eq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    gibbsState (geometricHamiltonian_hermitian r n) 1 = geometricDensity r n :=
  gibbsState_logEnergy (geometricWeight r n)
    (geometricWeight_pos hr0 hr1 n) (geometricWeight_sum r n)

theorem geometricEnergy_castSucc {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) (i : Fin n) :
    geometricEnergy r n i.castSucc =
      -Real.log (1 - r) - (i.val : ℝ) * Real.log r := by
  have hbase : 0 < 1 - r := by linarith
  unfold geometricEnergy logEnergy
  rw [geometricWeight_castSucc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

/-- The last energy uses the lumped tail mass and therefore has no interior offset. -/
theorem geometricEnergy_last (r : ℝ) (n : ℕ) :
    geometricEnergy r n (Fin.last n) = -(n : ℝ) * Real.log r := by
  unfold geometricEnergy logEnergy
  rw [geometricWeight_last, Real.log_pow]
  ring

theorem meanEnergy_realDiagonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (energy p : ι → ℝ) :
    meanEnergy (realDiagonal energy) (realDiagonal p) = ∑ i, energy i * p i := by
  simp only [meanEnergy, realDiagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re]

/-- The joint state is generated by the native swap on the declared input and Gibbs bath. -/
def geometricJoint (q r : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  thermalJoint ThermalReset.swapUnitary (geometricDensity q n)
    (geometricHamiltonian_hermitian r n) 1

def geometricHeat (q r : ℝ) (n : ℕ) : ℝ :=
  reservoirHeat ThermalReset.swapUnitary (geometricDensity q n)
    (geometricHamiltonian_hermitian r n) 1

theorem geometricJoint_density {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ) :
    (geometricJoint q r n).PosSemidef ∧ (geometricJoint q r n).trace = 1 :=
  thermalJoint_density ThermalReset.swapUnitary
    (geometricDensity_density hq0 hq1 n).1 (geometricDensity_trace q n)
    (geometricHamiltonian_hermitian r n) 1

theorem geometricJoint_eq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (q : ℝ) (n : ℕ) :
    geometricJoint q r n = geometricDensity r n ⊗ₖ geometricDensity q n := by
  unfold geometricJoint
  rw [ThermalReset.swap_joint, geometricGibbs_eq hr0 hr1 n]

theorem geometric_output {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (q : ℝ) (n : ℕ) :
    marginalLeft (geometricJoint q r n) = geometricDensity r n := by
  unfold geometricJoint
  rw [ThermalReset.swap_output _ (geometricDensity_trace q n), geometricGibbs_eq hr0 hr1 n]

theorem geometric_reservoir (q r : ℝ) (n : ℕ) :
    marginalRight (geometricJoint q r n) = geometricDensity q n :=
  ThermalReset.swap_reservoir (geometricDensity q n) (geometricHamiltonian_hermitian r n) 1

/-- The finite heat formula is the energy change of the same reservoir under the native swap. -/
theorem geometricHeat_eq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (q : ℝ) (n : ℕ) :
    geometricHeat q r n =
      (∑ i, geometricEnergy r n i * geometricWeight q n i) -
        ∑ i, geometricEnergy r n i * geometricWeight r n i := by
  unfold geometricHeat
  rw [ThermalReset.swap_heat, geometricGibbs_eq hr0 hr1 n, meanEnergy_sub]
  change meanEnergy (realDiagonal (geometricEnergy r n)) (realDiagonal (geometricWeight q n)) -
    meanEnergy (realDiagonal (geometricEnergy r n)) (realDiagonal (geometricWeight r n)) = _
  rw [meanEnergy_realDiagonal, meanEnergy_realDiagonal]

theorem geometricHeat_balance {q r : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    geometricHeat q r n =
        entropy (geometricDensity q n) - entropy (geometricDensity r n) +
          relativeEntropy (geometricDensity q n) (geometricDensity r n) ∧
      0 ≤ relativeEntropy (geometricDensity q n) (geometricDensity r n) := by
  have h := ThermalReset.swap_balance (geometricDensity q n)
    (geometricDensity_density hq0 hq1 n).1 (geometricDensity_trace q n)
    (geometricHamiltonian_hermitian r n) 1
  rw [geometricGibbs_eq hr0 hr1 n, one_mul] at h
  exact h

def selectedJoint (n : ℕ) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  geometricJoint (1 / 2) (1 / 4) n

def selectedHeat (n : ℕ) : ℝ :=
  geometricHeat (1 / 2) (1 / 4) n

theorem selectedGibbs_eq (n : ℕ) :
    gibbsState (geometricHamiltonian_hermitian (1 / 4) n) 1 = selectedBathDensity n :=
  geometricGibbs_eq (by norm_num) (by norm_num) n

theorem selectedJoint_density (n : ℕ) :
    (selectedJoint n).PosSemidef ∧ (selectedJoint n).trace = 1 :=
  geometricJoint_density (by norm_num) (by norm_num) (1 / 4) n

theorem selectedSwap_output (n : ℕ) :
    marginalLeft (selectedJoint n) = selectedBathDensity n :=
  geometric_output (by norm_num) (by norm_num) (1 / 2) n

theorem selectedSwap_reservoir (n : ℕ) :
    marginalRight (selectedJoint n) = selectedDensity n :=
  geometric_reservoir (1 / 2) (1 / 4) n

def geometricEntropy (q : ℝ) : ℝ :=
  Real.binEntropy q / (1 - q)

theorem geometricEntropy_eq {q : ℝ} (hq1 : q < 1) :
    geometricEntropy q = -Real.log (1 - q) - q / (1 - q) * Real.log q := by
  have hd : 1 - q ≠ 0 := by linarith
  unfold geometricEntropy
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog]
  field_simp
  ring

theorem geometricEntropy_coefficient {q : ℝ} (hq1 : q < 1) :
    (1 - q) * geometricEntropy q = Real.binEntropy q := by
  have hd : 1 - q ≠ 0 := by linarith
  unfold geometricEntropy
  field_simp

theorem geometricEntropy_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ geometricEntropy q := by
  have hb := Real.binEntropy_nonneg hq0 hq1.le
  have hd : 0 < 1 - q := by linarith
  unfold geometricEntropy
  positivity

theorem geometricDensity_entropy_succ (q : ℝ) (n : ℕ) :
    entropy (geometricDensity q (n + 1)) =
      entropy (geometricDensity q n) + q ^ n * Real.binEntropy q := by
  rw [geometricDensity_entropy_split q (n + 1), geometricDensity_entropy_split q n,
    Finset.sum_range_succ, pow_succ,
    Real.negMulLog_mul (1 - q) (q ^ n), Real.negMulLog_mul (q ^ n) q,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

theorem geometricDensity_entropy_closed {q : ℝ} (hq1 : q < 1) (n : ℕ) :
    entropy (geometricDensity q n) = (1 - q ^ n) * geometricEntropy q := by
  induction n with
  | zero =>
      rw [geometricDensity_entropy_split]
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, Real.negMulLog_one,
        zero_add, sub_self, zero_mul]
  | succ n ih =>
      rw [geometricDensity_entropy_succ, ih, pow_succ,
        ← geometricEntropy_coefficient hq1]
      ring

theorem geometricEntropy_error {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    |entropy (geometricDensity q n) - geometricEntropy q| = q ^ n * geometricEntropy q := by
  have hH := geometricEntropy_nonneg hq0 hq1
  have hprod : 0 ≤ q ^ n * geometricEntropy q := by positivity
  rw [geometricDensity_entropy_closed hq1]
  have he : (1 - q ^ n) * geometricEntropy q - geometricEntropy q =
      -(q ^ n * geometricEntropy q) := by ring
  rw [he, abs_neg, abs_of_nonneg hprod]

theorem geometricEntropy_tendsto {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Filter.Tendsto (fun n => entropy (geometricDensity q n))
      Filter.atTop (nhds (geometricEntropy q)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have h :
      Filter.Tendsto (fun n : ℕ => (1 - q ^ n) * geometricEntropy q)
        Filter.atTop (nhds ((1 - (0 : ℝ)) * geometricEntropy q)) :=
    (tendsto_const_nhds.sub hp).mul tendsto_const_nhds
  have he : (fun n => entropy (geometricDensity q n)) =
      (fun n => (1 - q ^ n) * geometricEntropy q) :=
    funext (geometricDensity_entropy_closed hq1)
  rw [he]
  simpa only [sub_zero, one_mul] using h

/-- The affine energy sum retains the distinct energy assigned to the final lumped coordinate. -/
theorem geometricAffine_sum {q : ℝ} (hq1 : q < 1) (a b : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (a + (i : ℝ) * b) * ((1 - q) * q ^ i)) +
        (n : ℝ) * b * q ^ n =
      (1 - q ^ n) * (a + q / (1 - q) * b) := by
  have hd : 1 - q ≠ 0 := by linarith
  have hc : (1 - q) * (a + q / (1 - q) * b) = (1 - q) * a + q * b := by
    field_simp
    ring
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, pow_zero,
        zero_mul, zero_add, sub_self]
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, pow_succ]
      calc
        (∑ i ∈ Finset.range n, (a + (i : ℝ) * b) * ((1 - q) * q ^ i)) +
              (a + (n : ℝ) * b) * ((1 - q) * q ^ n) +
              ((n : ℝ) + 1) * b * (q ^ n * q) =
            ((∑ i ∈ Finset.range n, (a + (i : ℝ) * b) * ((1 - q) * q ^ i)) +
              (n : ℝ) * b * q ^ n) + q ^ n * ((1 - q) * a + q * b) := by ring
        _ = (1 - q ^ n) * (a + q / (1 - q) * b) +
              q ^ n * ((1 - q) * a + q * b) := by rw [ih]
        _ = (1 - q ^ n * q) * (a + q / (1 - q) * b) := by
          rw [← hc]
          ring

def geometricCrossEnergy (q r : ℝ) : ℝ :=
  -Real.log (1 - r) - q / (1 - q) * Real.log r

theorem geometricCrossEnergy_self {r : ℝ} (hr1 : r < 1) :
    geometricCrossEnergy r r = geometricEntropy r := by
  rw [geometricEntropy_eq hr1]
  rfl

theorem geometricCrossEnergy_nonneg {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ geometricCrossEnergy q r := by
  have hqbase : 0 < 1 - q := by linarith
  have hrbase : 0 < 1 - r := by linarith
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hlogbase : Real.log (1 - r) < 0 := Real.log_neg hrbase (by linarith)
  have hprod : 0 ≤ q / (1 - q) * (-Real.log r) :=
    mul_nonneg (div_nonneg hq0 hqbase.le) (by linarith)
  unfold geometricCrossEnergy
  nlinarith

theorem geometricMeanEnergy_eq {q r : ℝ}
    (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    meanEnergy (geometricHamiltonian r n) (geometricDensity q n) =
      (1 - q ^ n) * geometricCrossEnergy q r := by
  change meanEnergy (realDiagonal (geometricEnergy r n)) (realDiagonal (geometricWeight q n)) = _
  rw [meanEnergy_realDiagonal, Fin.sum_univ_castSucc, geometricEnergy_last, geometricWeight_last]
  have hfirst :
      (∑ i : Fin n, geometricEnergy r n i.castSucc * geometricWeight q n i.castSucc) =
        ∑ i ∈ Finset.range n,
          (-Real.log (1 - r) + (i : ℝ) * (-Real.log r)) * ((1 - q) * q ^ i) := by
    calc
      (∑ i : Fin n, geometricEnergy r n i.castSucc * geometricWeight q n i.castSucc) =
          ∑ i : Fin n,
            (-Real.log (1 - r) + (i.val : ℝ) * (-Real.log r)) * ((1 - q) * q ^ i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [geometricEnergy_castSucc hr0 hr1, geometricWeight_castSucc]
        ring
      _ = ∑ i ∈ Finset.range n,
          (-Real.log (1 - r) + (i : ℝ) * (-Real.log r)) * ((1 - q) * q ^ i) :=
        Fin.sum_univ_eq_sum_range
          (fun i => (-Real.log (1 - r) + (i : ℝ) * (-Real.log r)) * ((1 - q) * q ^ i)) n
  rw [hfirst]
  have h := geometricAffine_sum hq1 (-Real.log (1 - r)) (-Real.log r) n
  unfold geometricCrossEnergy
  convert h using 1 <;> ring

theorem geometricHeat_closed {q r : ℝ}
    (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    geometricHeat q r n =
      (1 - q ^ n) * geometricCrossEnergy q r -
        (1 - r ^ n) * geometricEntropy r := by
  unfold geometricHeat
  rw [ThermalReset.swap_heat, geometricGibbs_eq hr0 hr1 n, meanEnergy_sub,
    geometricMeanEnergy_eq hq1 hr0 hr1 n, geometricMeanEnergy_eq hr1 hr0 hr1 n,
    geometricCrossEnergy_self hr1]

theorem geometricHeat_error {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    |geometricHeat q r n - (geometricCrossEnergy q r - geometricEntropy r)| ≤
      q ^ n * geometricCrossEnergy q r + r ^ n * geometricEntropy r := by
  have hC := geometricCrossEnergy_nonneg hq0 hq1 hr0 hr1
  have hH := geometricEntropy_nonneg hr0.le hr1
  have hqprod : 0 ≤ q ^ n * geometricCrossEnergy q r := by positivity
  have hrprod : 0 ≤ r ^ n * geometricEntropy r := by positivity
  rw [geometricHeat_closed hq1 hr0 hr1 n, abs_le]
  constructor <;> nlinarith

theorem geometricHeat_tendsto {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => geometricHeat q r n) Filter.atTop
      (nhds (geometricCrossEnergy q r - geometricEntropy r)) := by
  have hpq := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hpr := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have h :
      Filter.Tendsto (fun n : ℕ =>
        (1 - q ^ n) * geometricCrossEnergy q r - (1 - r ^ n) * geometricEntropy r)
        Filter.atTop
        (nhds ((1 - (0 : ℝ)) * geometricCrossEnergy q r -
          (1 - (0 : ℝ)) * geometricEntropy r)) :=
    ((tendsto_const_nhds.sub hpq).mul tendsto_const_nhds).sub
      ((tendsto_const_nhds.sub hpr).mul tendsto_const_nhds)
  have he : (fun n => geometricHeat q r n) =
      (fun n => (1 - q ^ n) * geometricCrossEnergy q r -
        (1 - r ^ n) * geometricEntropy r) :=
    funext (geometricHeat_closed hq1 hr0 hr1)
  rw [he]
  simpa only [sub_zero, one_mul] using h

theorem selectedEntropy_value :
    geometricEntropy (1 / 2) = 2 * Real.log 2 := by
  unfold geometricEntropy
  rw [one_div, Real.binEntropy_two_inv]
  norm_num
  ring

theorem selectedEntropy_tendsto :
    Filter.Tendsto (fun n => entropy (selectedDensity n))
      Filter.atTop (nhds (2 * Real.log 2)) := by
  rw [← selectedEntropy_value]
  exact geometricEntropy_tendsto (by norm_num) (by norm_num)

theorem selectedHeat_limit_value :
    geometricCrossEnergy (1 / 2) (1 / 4) - geometricEntropy (1 / 4) =
      (2 / 3) * Real.log 4 := by
  rw [geometricEntropy_eq (show (1 : ℝ) / 4 < 1 by norm_num)]
  unfold geometricCrossEnergy
  have hlog : Real.log ((1 : ℝ) / 4) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  norm_num
  ring

theorem selectedHeat_limit_pos : 0 < (2 / 3 : ℝ) * Real.log 4 := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

theorem selectedHeat_tendsto :
    Filter.Tendsto selectedHeat Filter.atTop (nhds ((2 / 3) * Real.log 4)) := by
  rw [← selectedHeat_limit_value]
  exact geometricHeat_tendsto (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def infiniteWeight (q : ℝ) (k : ℕ) : ℝ :=
  (1 - q) * q ^ k

theorem infiniteWeight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ infiniteWeight q k := by
  have hb : 0 < 1 - q := by linarith
  unfold infiniteWeight
  positivity

theorem infiniteWeight_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (infiniteWeight q) 1 := by
  have hd : 1 - q ≠ 0 := by linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 - q)
  have hv : (1 - q) * (1 - q)⁻¹ = 1 := by field_simp
  rw [hv] at h
  exact h

/-- The common carrier uses Mathlib's standard real sequence space with exponent one. -/
abbrev DiagonalL1 := lp (fun _ : ℕ => ℝ) 1

theorem diagonalL1_norm_eq (x : DiagonalL1) :
    ‖x‖ = ∑' k, |x k| := by
  have h := lp.norm_rpow_eq_tsum (p := 1) (by norm_num) x
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact h

def geometricState {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : DiagonalL1 :=
  ⟨infiniteWeight q, by
    apply memℓp_gen
    have he :
        (fun k => ‖infiniteWeight q k‖ ^ (1 : ℝ≥0∞).toReal) = infiniteWeight q := by
      funext k
      rw [ENNReal.toReal_one, Real.rpow_one]
      change |infiniteWeight q k| = infiniteWeight q k
      exact abs_of_nonneg (infiniteWeight_nonneg hq0 hq1 k)
    rw [he]
    exact (infiniteWeight_hasSum hq0 hq1).summable⟩

theorem geometricState_apply {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    geometricState hq0 hq1 k = infiniteWeight q k := rfl

theorem geometricState_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ geometricState hq0 hq1 k :=
  infiniteWeight_nonneg hq0 hq1 k

theorem geometricState_normalized {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' k, geometricState hq0 hq1 k) = 1 :=
  (infiniteWeight_hasSum hq0 hq1).tsum_eq

theorem geometricState_norm_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖geometricState hq0 hq1‖ = 1 := by
  rw [diagonalL1_norm_eq]
  have he : (fun k => |geometricState hq0 hq1 k|) = infiniteWeight q := by
    funext k
    change |infiniteWeight q k| = infiniteWeight q k
    exact abs_of_nonneg (infiniteWeight_nonneg hq0 hq1 k)
  rw [he]
  exact (infiniteWeight_hasSum hq0 hq1).tsum_eq

def selectedState : DiagonalL1 :=
  geometricState (q := 1 / 2) (by norm_num) (by norm_num)

def selectedBathState : DiagonalL1 :=
  geometricState (q := 1 / 4) (by norm_num) (by norm_num)

def infiniteEnergy (r : ℝ) (k : ℕ) : ℝ :=
  -Real.log (1 - r) - (k : ℝ) * Real.log r

theorem infiniteAffine_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a b : ℝ) :
    HasSum (fun k : ℕ => (a + (k : ℝ) * b) * infiniteWeight q k)
      (a + q / (1 - q) * b) := by
  have hd : 1 - q ≠ 0 := by linarith
  have hnorm : ‖q‖ < 1 := by
    change |q| < 1
    rw [abs_of_nonneg hq0]
    exact hq1
  have h0 := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((1 - q) * a)
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left ((1 - q) * b)
  convert h0.add h1 using 1
  · funext k
    unfold infiniteWeight
    ring
  · field_simp
    ring

def infiniteMeanEnergy (q r : ℝ) : ℝ :=
  ∑' k, infiniteEnergy r k * infiniteWeight q k

theorem infiniteMeanEnergy_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℝ) :
    HasSum (fun k => infiniteEnergy r k * infiniteWeight q k) (geometricCrossEnergy q r) := by
  have h := infiniteAffine_hasSum hq0 hq1 (-Real.log (1 - r)) (-Real.log r)
  convert h using 1
  · funext k
    unfold infiniteEnergy
    ring
  · unfold geometricCrossEnergy
    ring

theorem infiniteMeanEnergy_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℝ) :
    infiniteMeanEnergy q r = geometricCrossEnergy q r :=
  (infiniteMeanEnergy_hasSum hq0 hq1 r).tsum_eq

theorem infiniteWeight_negMulLog {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    Real.negMulLog (infiniteWeight q k) = infiniteEnergy q k * infiniteWeight q k := by
  have hb : 0 < 1 - q := by linarith
  unfold infiniteWeight infiniteEnergy Real.negMulLog
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

def infiniteEntropy (q : ℝ) : ℝ :=
  ∑' k, Real.negMulLog (infiniteWeight q k)

theorem infiniteEntropy_hasSum {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k => Real.negMulLog (infiniteWeight q k)) (geometricEntropy q) := by
  have he :
      (fun k => Real.negMulLog (infiniteWeight q k)) =
        (fun k => infiniteEnergy q k * infiniteWeight q k) :=
    funext (infiniteWeight_negMulLog hq0 hq1)
  rw [he, ← geometricCrossEnergy_self hq1]
  exact infiniteMeanEnergy_hasSum hq0.le hq1 q

theorem infiniteEntropy_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    infiniteEntropy q = geometricEntropy q :=
  (infiniteEntropy_hasSum hq0 hq1).tsum_eq

def infiniteHeat (q r : ℝ) : ℝ :=
  infiniteMeanEnergy q r - infiniteMeanEnergy r r

theorem infiniteHeat_eq {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    infiniteHeat q r = geometricCrossEnergy q r - geometricEntropy r := by
  unfold infiniteHeat
  rw [infiniteMeanEnergy_eq hq0 hq1 r, infiniteMeanEnergy_eq hr0 hr1 r,
    geometricCrossEnergy_self hr1]

theorem geometricEntropy_actual_limit {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Filter.Tendsto (fun n => entropy (geometricDensity q n))
      Filter.atTop (nhds (infiniteEntropy q)) := by
  rw [infiniteEntropy_eq hq0 hq1]
  exact geometricEntropy_tendsto hq0.le hq1

theorem geometricHeat_actual_limit {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => geometricHeat q r n)
      Filter.atTop (nhds (infiniteHeat q r)) := by
  rw [infiniteHeat_eq hq0 hq1 hr0.le hr1]
  exact geometricHeat_tendsto hq0 hq1 hr0 hr1

/-- The shifted series computes the actual energy beyond the declared cutoff. -/
def energyTail (q r : ℝ) (N : ℕ) : ℝ :=
  ∑' k, infiniteEnergy r (N + k) * infiniteWeight q (N + k)

theorem infiniteAffineTail_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (a b : ℝ) (N : ℕ) :
    HasSum (fun k => (a + ((N + k : ℕ) : ℝ) * b) * infiniteWeight q (N + k))
      (q ^ N * (a + (N : ℝ) * b + q / (1 - q) * b)) := by
  have h := (infiniteAffine_hasSum hq0 hq1 (a + (N : ℝ) * b) b).mul_left (q ^ N)
  have he :
      (fun k => (a + ((N + k : ℕ) : ℝ) * b) * infiniteWeight q (N + k)) =
        (fun k : ℕ => q ^ N * ((a + (N : ℝ) * b + (k : ℝ) * b) * infiniteWeight q k)) := by
    funext k
    unfold infiniteWeight
    rw [pow_add, Nat.cast_add]
    ring
  rw [he]
  exact h

theorem energyTail_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℝ) (N : ℕ) :
    HasSum (fun k => infiniteEnergy r (N + k) * infiniteWeight q (N + k))
      (q ^ N * (geometricCrossEnergy q r - (N : ℝ) * Real.log r)) := by
  have h := infiniteAffineTail_hasSum hq0 hq1 (-Real.log (1 - r)) (-Real.log r) N
  convert h using 1
  · funext k
    unfold infiniteEnergy
    ring
  · unfold geometricCrossEnergy
    ring

theorem energyTail_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℝ) (N : ℕ) :
    energyTail q r N = q ^ N * (geometricCrossEnergy q r - (N : ℝ) * Real.log r) :=
  (energyTail_hasSum hq0 hq1 r N).tsum_eq

theorem energyTail_tendsto {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℝ) :
    Filter.Tendsto (energyTail q r) Filter.atTop (nhds 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hn := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have h :
      Filter.Tendsto (fun n : ℕ =>
        q ^ n * geometricCrossEnergy q r - ((n : ℝ) * q ^ n) * Real.log r)
        Filter.atTop (nhds ((0 : ℝ) * geometricCrossEnergy q r - 0 * Real.log r)) :=
    (hp.mul_const (geometricCrossEnergy q r)).sub (hn.mul_const (Real.log r))
  have he : energyTail q r =
      (fun n : ℕ => q ^ n * geometricCrossEnergy q r - ((n : ℝ) * q ^ n) * Real.log r) := by
    funext n
    rw [energyTail_eq hq0 hq1 r n]
    ring
  rw [he]
  simpa only [zero_mul, sub_zero] using h

def entropyTail (q : ℝ) (N : ℕ) : ℝ :=
  ∑' k, Real.negMulLog (infiniteWeight q (N + k))

theorem entropyTail_eq_energyTail {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    entropyTail q N = energyTail q q N := by
  have he :
      (fun k => Real.negMulLog (infiniteWeight q (N + k))) =
        (fun k => infiniteEnergy q (N + k) * infiniteWeight q (N + k)) :=
    funext (fun k => infiniteWeight_negMulLog hq0 hq1 (N + k))
  unfold entropyTail energyTail
  rw [he]

theorem entropyTail_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    entropyTail q N = q ^ N * (geometricEntropy q - (N : ℝ) * Real.log q) := by
  rw [entropyTail_eq_energyTail hq0 hq1 N, energyTail_eq hq0.le hq1 q N,
    geometricCrossEnergy_self hq1]

theorem entropyTail_tendsto {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Filter.Tendsto (entropyTail q) Filter.atTop (nhds 0) := by
  have he : entropyTail q = energyTail q q :=
    funext (entropyTail_eq_energyTail hq0 hq1)
  rw [he]
  exact energyTail_tendsto hq0.le hq1 q

theorem selected_tail_control :
    Filter.Tendsto (entropyTail (1 / 2)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (energyTail (1 / 2) (1 / 4)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (energyTail (1 / 4) (1 / 4)) Filter.atTop (nhds 0) :=
  ⟨entropyTail_tendsto (by norm_num) (by norm_num),
    energyTail_tendsto (by norm_num) (by norm_num) (1 / 4),
    energyTail_tendsto (by norm_num) (by norm_num) (1 / 4)⟩

def padFunction {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then p ⟨k, h⟩ else 0

theorem padFunction_hasSum {n : ℕ} (p : Fin n → ℝ) :
    HasSum (padFunction p) (∑ i, p i) := by
  have hfinite :
      HasSum (padFunction p) (∑ k ∈ Finset.range n, padFunction p k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hk' : ¬k < n := by simpa only [Finset.mem_range] using hk
    rw [padFunction, dif_neg hk']
  have he : (∑ k ∈ Finset.range n, padFunction p k) = ∑ i : Fin n, p i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [padFunction, dif_pos i.isLt]
  rw [he] at hfinite
  exact hfinite

theorem padFunction_abs_hasSum {n : ℕ} (p : Fin n → ℝ) :
    HasSum (fun k => |padFunction p k|) (∑ i, |p i|) := by
  have he : (fun k => |padFunction p k|) = padFunction (fun i => |p i|) := by
    funext k
    by_cases hk : k < n
    · simp only [padFunction, dif_pos hk]
    · simp only [padFunction, dif_neg hk, abs_zero]
  rw [he]
  exact padFunction_hasSum (fun i => |p i|)

/-- Finite vectors enter the common carrier by literal zero padding. -/
def padVector {n : ℕ} (p : Fin n → ℝ) : DiagonalL1 :=
  ⟨padFunction p, by
    apply memℓp_gen
    simp only [ENNReal.toReal_one, Real.rpow_one]
    exact (padFunction_abs_hasSum p).summable⟩

theorem padVector_apply {n : ℕ} (p : Fin n → ℝ) (k : ℕ) :
    padVector p k = padFunction p k := rfl

theorem padVector_norm {n : ℕ} (p : Fin n → ℝ) :
    ‖padVector p‖ = ∑ i, |p i| := by
  rw [diagonalL1_norm_eq]
  exact (padFunction_abs_hasSum p).tsum_eq

theorem padVector_sub {n : ℕ} (p s : Fin n → ℝ) :
    padVector p - padVector s = padVector (fun i => p i - s i) := by
  apply lp.ext
  funext k
  change padFunction p k - padFunction s k = padFunction (fun i => p i - s i) k
  by_cases hk : k < n
  · simp only [padFunction, dif_pos hk]
  · simp only [padFunction, dif_neg hk, sub_self]

theorem padVector_norm_sub {n : ℕ} (p s : Fin n → ℝ) :
    ‖padVector p - padVector s‖ = ∑ i, |p i - s i| := by
  rw [padVector_sub, padVector_norm]

theorem padVector_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (k : ℕ) : 0 ≤ padVector p k := by
  change 0 ≤ padFunction p k
  by_cases hk : k < n
  · rw [padFunction, dif_pos hk]
    exact hp ⟨k, hk⟩
  · rw [padFunction, dif_neg hk]

theorem padVector_normalized {n : ℕ} (p : Fin n → ℝ) (hp : ∑ i, p i = 1) :
    (∑' k, padVector p k) = 1 :=
  (padFunction_hasSum p).tsum_eq.trans hp

theorem diagonalL1_abs_summable (x : DiagonalL1) :
    Summable (fun k => |x k|) := by
  have h := (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] at h
  exact h

def paddedGeometric (q : ℝ) (n : ℕ) : DiagonalL1 :=
  padVector (geometricWeight q n)

theorem paddedGeometric_before (q : ℝ) (n k : ℕ) (hk : k < n) :
    paddedGeometric q n k = infiniteWeight q k := by
  change padFunction (geometricWeight q n) k = infiniteWeight q k
  rw [padFunction, dif_pos (show k < n + 1 by omega)]
  change (if k < n then (1 - q) * q ^ k else q ^ n) = (1 - q) * q ^ k
  exact if_pos hk

theorem paddedGeometric_at (q : ℝ) (n : ℕ) :
    paddedGeometric q n n = q ^ n := by
  change padFunction (geometricWeight q n) n = q ^ n
  rw [padFunction, dif_pos (show n < n + 1 by omega)]
  change (if n < n then (1 - q) * q ^ n else q ^ n) = q ^ n
  exact if_neg (by omega)

theorem paddedGeometric_after (q : ℝ) (n k : ℕ) (hk : n < k) :
    paddedGeometric q n k = 0 := by
  change padFunction (geometricWeight q n) k = 0
  rw [padFunction, dif_neg (show ¬k < n + 1 by omega)]

theorem paddedGeometric_normalized (q : ℝ) (n : ℕ) :
    (∑' k, paddedGeometric q n k) = 1 :=
  padVector_normalized (geometricWeight q n) (geometricWeight_sum q n)

theorem paddedGeometric_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n k : ℕ) :
    0 ≤ paddedGeometric q n k :=
  padVector_nonneg (geometricWeight q n) (fun i => (geometricWeight_pos hq0 hq1 n i).le) k

theorem infiniteWeight_tail_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    HasSum (fun k => infiniteWeight q (k + N)) (q ^ N) := by
  have h := (infiniteWeight_hasSum hq0 hq1).mul_left (q ^ N)
  have he : (fun k => infiniteWeight q (k + N)) =
      (fun k => q ^ N * infiniteWeight q k) := by
    funext k
    unfold infiniteWeight
    rw [pow_add]
    ring
  rw [he]
  simpa only [mul_one] using h

/-- The coarse cutoff and the infinite state differ by an exact standard lp norm. -/
theorem paddedGeometric_norm_error {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ‖paddedGeometric q n - geometricState hq0 hq1‖ = 2 * q ^ (n + 1) := by
  have hbefore : ∀ k, k < n →
      |paddedGeometric q n k - geometricState hq0 hq1 k| = 0 := by
    intro k hk
    rw [paddedGeometric_before q n k hk, geometricState_apply, sub_self, abs_zero]
  have hat :
      |paddedGeometric q n n - geometricState hq0 hq1 n| = q ^ (n + 1) := by
    rw [paddedGeometric_at, geometricState_apply]
    unfold infiniteWeight
    have he : q ^ n - (1 - q) * q ^ n = q ^ (n + 1) := by rw [pow_succ]; ring
    rw [he, abs_of_nonneg (by positivity)]
  have hafter : ∀ k, n < k →
      |paddedGeometric q n k - geometricState hq0 hq1 k| = infiniteWeight q k := by
    intro k hk
    rw [paddedGeometric_after q n k hk, geometricState_apply, zero_sub, abs_neg,
      abs_of_nonneg (infiniteWeight_nonneg hq0 hq1 k)]
  have hprefix :
      (∑ k ∈ Finset.range (n + 1),
        |paddedGeometric q n k - geometricState hq0 hq1 k|) = q ^ (n + 1) := by
    rw [Finset.sum_range_succ]
    have hz :
        (∑ k ∈ Finset.range n,
          |paddedGeometric q n k - geometricState hq0 hq1 k|) = 0 :=
      Finset.sum_eq_zero (fun k hk => hbefore k (Finset.mem_range.mp hk))
    rw [hz, hat, zero_add]
  have htail :
      (∑' k, |paddedGeometric q n (k + (n + 1)) -
        geometricState hq0 hq1 (k + (n + 1))|) = q ^ (n + 1) := by
    have he :
        (fun k => |paddedGeometric q n (k + (n + 1)) -
          geometricState hq0 hq1 (k + (n + 1))|) =
        (fun k => infiniteWeight q (k + (n + 1))) :=
      funext (fun k => hafter (k + (n + 1)) (by omega))
    rw [he]
    exact (infiniteWeight_tail_hasSum hq0 hq1 (n + 1)).tsum_eq
  have hs := diagonalL1_abs_summable (paddedGeometric q n - geometricState hq0 hq1)
  have hsplit := hs.sum_add_tsum_nat_add (n + 1)
  rw [diagonalL1_norm_eq]
  change (∑' k, |paddedGeometric q n k - geometricState hq0 hq1 k|) = _
  change (∑ k ∈ Finset.range (n + 1),
      |paddedGeometric q n k - geometricState hq0 hq1 k|) +
      (∑' k, |paddedGeometric q n (k + (n + 1)) -
        geometricState hq0 hq1 (k + (n + 1))|) =
      (∑' k, |paddedGeometric q n k - geometricState hq0 hq1 k|) at hsplit
  rw [← hsplit, hprefix, htail]
  ring

theorem paddedGeometric_norm_tendsto {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Filter.Tendsto (fun n => ‖paddedGeometric q n - geometricState hq0 hq1‖)
      Filter.atTop (nhds 0) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const q).const_mul 2
  have he : (fun n => ‖paddedGeometric q n - geometricState hq0 hq1‖) =
      (fun n : ℕ => 2 * (q ^ n * q)) := by
    funext n
    rw [paddedGeometric_norm_error hq0 hq1 n, pow_succ]
  rw [he]
  simpa only [zero_mul, mul_zero] using h

theorem selectedState_norm_limit :
    Filter.Tendsto (fun n => ‖paddedGeometric (1 / 2) n - selectedState‖)
      Filter.atTop (nhds 0) :=
  paddedGeometric_norm_tendsto (by norm_num) (by norm_num)

def selectedReports (n test : ℕ) : ℂ :=
  (paddedGeometric (1 / 2) n test : ℂ)

def selectedLimitReports (test : ℕ) : ℂ :=
  (selectedState test : ℂ)

theorem selectedReports_finite (n test : ℕ) (ht : test < n + 1) :
    selectedReports n test = selectedDensity n ⟨test, ht⟩ ⟨test, ht⟩ := by
  change (padFunction (geometricWeight (1 / 2) n) test : ℂ) =
    selectedDensity n ⟨test, ht⟩ ⟨test, ht⟩
  rw [padFunction, dif_pos ht]
  simp only [selectedDensity, geometricDensity, realDiagonal, Matrix.diagonal_apply_eq]

def LimitReportsGoal (reports : ℕ → ℕ → ℂ) (limit : ℕ → ℂ) : Prop :=
  ∀ test, Filter.Tendsto (fun n => reports n test) Filter.atTop (nhds (limit test))

theorem LimitReportsGoal_proof :
    LimitReportsGoal selectedReports selectedLimitReports := by
  intro test
  apply tendsto_atTop_of_eventually_const (i₀ := test + 1)
  intro n hn
  change (paddedGeometric (1 / 2) n test : ℂ) = (infiniteWeight (1 / 2) test : ℂ)
  rw [paddedGeometric_before (1 / 2) n test (by omega)]

/-- The lower-case theorem alias retains the exact scalar report convergence contract. -/
theorem limitReportsGoal : LimitReportsGoal selectedReports selectedLimitReports :=
  LimitReportsGoal_proof

/-- Observable extension repeats the final value and is distinct from zero padding a state. -/
def cutoffExtension (n : ℕ) (a : Fin (n + 1) → ℂ) (k : ℕ) : ℂ :=
  a ⟨min k n, by omega⟩

theorem cutoffExtension_fin (n : ℕ) (a : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    cutoffExtension n a i.val = a i := by
  unfold cutoffExtension
  apply congrArg a
  apply Fin.ext
  change min i.val n = i.val
  have hi := i.isLt
  omega

theorem cutoffExtension_after (n : ℕ) (a : Fin (n + 1) → ℂ) (k : ℕ) (hk : n ≤ k) :
    cutoffExtension n a k = a (Fin.last n) := by
  unfold cutoffExtension
  apply congrArg a
  apply Fin.ext
  change min k n = n
  omega

def repeatTail (n m : ℕ) (a : Fin (n + 1) → ℂ) : Fin (m + 1) → ℂ :=
  fun i => cutoffExtension n a i.val

theorem repeatTail_self (n : ℕ) (a : Fin (n + 1) → ℂ) :
    repeatTail n n a = a :=
  funext (cutoffExtension_fin n a)

theorem cutoffExtension_repeatTail (n m : ℕ) (hnm : n ≤ m)
    (a : Fin (n + 1) → ℂ) (k : ℕ) :
    cutoffExtension m (repeatTail n m a) k = cutoffExtension n a k := by
  change a ⟨min (min k m) n, by omega⟩ = a ⟨min k n, by omega⟩
  apply congrArg a
  apply Fin.ext
  change min (min k m) n = min k n
  omega

theorem repeatTail_comp (n m l : ℕ) (hnm : n ≤ m) (a : Fin (n + 1) → ℂ) :
    repeatTail m l (repeatTail n m a) = repeatTail n l a :=
  funext (fun i => cutoffExtension_repeatTail n m hnm a i.val)

theorem repeatTail_injective (n m : ℕ) (hnm : n ≤ m) :
    Function.Injective (repeatTail n m) := by
  intro a b hab
  funext i
  let j : Fin (m + 1) := ⟨i.val, by have hi := i.isLt; omega⟩
  have he := congrFun hab j
  change cutoffExtension n a i.val = cutoffExtension n b i.val at he
  rw [cutoffExtension_fin n a i, cutoffExtension_fin n b i] at he
  exact he

theorem repeatTail_one (n m : ℕ) :
    repeatTail n m (1 : Fin (n + 1) → ℂ) = 1 := rfl

theorem repeatTail_add (n m : ℕ) (a b : Fin (n + 1) → ℂ) :
    repeatTail n m (a + b) = repeatTail n m a + repeatTail n m b := rfl

theorem repeatTail_mul (n m : ℕ) (a b : Fin (n + 1) → ℂ) :
    repeatTail n m (a * b) = repeatTail n m a * repeatTail n m b := rfl

theorem repeatTail_star (n m : ℕ) (a : Fin (n + 1) → ℂ) :
    repeatTail n m (star a) = star (repeatTail n m a) := rfl

theorem repeatTail_smul (n m : ℕ) (c : ℂ) (a : Fin (n + 1) → ℂ) :
    repeatTail n m (c • a) = c • repeatTail n m a := rfl

def finiteExpectation (q : ℝ) (n : ℕ) (a : Fin (n + 1) → ℂ) : ℂ :=
  ∑ i, (geometricWeight q n i : ℂ) * a i

theorem finiteExpectation_eq_trace (q : ℝ) (n : ℕ) (a : Fin (n + 1) → ℂ) :
    finiteExpectation q n a = (geometricDensity q n * Matrix.diagonal a).trace := by
  unfold finiteExpectation geometricDensity realDiagonal
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

theorem finiteExpectation_split (q : ℝ) (n : ℕ) (a : Fin (n + 1) → ℂ) :
    finiteExpectation q n a =
      (∑ k ∈ Finset.range n, (infiniteWeight q k : ℂ) * cutoffExtension n a k) +
        (q ^ n : ℝ) * cutoffExtension n a n := by
  unfold finiteExpectation
  rw [Fin.sum_univ_castSucc, geometricWeight_last]
  have hfirst :
      (∑ i : Fin n, (geometricWeight q n i.castSucc : ℂ) * a i.castSucc) =
        ∑ k ∈ Finset.range n, (infiniteWeight q k : ℂ) * cutoffExtension n a k := by
    calc
      (∑ i : Fin n, (geometricWeight q n i.castSucc : ℂ) * a i.castSucc) =
          ∑ i : Fin n, (infiniteWeight q i.val : ℂ) * cutoffExtension n a i.val := by
        apply Finset.sum_congr rfl
        intro i _
        have hc : cutoffExtension n a i.val = a i.castSucc := by
          have h := cutoffExtension_fin n a i.castSucc
          rwa [Fin.coe_castSucc] at h
        rw [geometricWeight_castSucc, hc, infiniteWeight]
      _ = ∑ k ∈ Finset.range n, (infiniteWeight q k : ℂ) * cutoffExtension n a k :=
        Fin.sum_univ_eq_sum_range
          (fun k => (infiniteWeight q k : ℂ) * cutoffExtension n a k) n
  have hl : cutoffExtension n a n = a (Fin.last n) := by
    have h := cutoffExtension_fin n a (Fin.last n)
    rwa [Fin.val_last] at h
  rw [hfirst, hl]

theorem finiteExpectation_step (q : ℝ) (n : ℕ) (a : Fin (n + 1) → ℂ) :
    finiteExpectation q (n + 1) (repeatTail n (n + 1) a) = finiteExpectation q n a := by
  rw [finiteExpectation_split q (n + 1) (repeatTail n (n + 1) a),
    finiteExpectation_split q n a]
  simp only [cutoffExtension_repeatTail n (n + 1) (show n ≤ n + 1 by omega) a]
  rw [Finset.sum_range_succ, cutoffExtension_after n a (n + 1) (by omega),
    cutoffExtension_after n a n le_rfl]
  simp only [infiniteWeight, pow_succ, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The same finite states are exactly compatible with the repeat-tail observable embeddings. -/
theorem finiteExpectation_repeatTail (q : ℝ) (n m : ℕ) (hnm : n ≤ m)
    (a : Fin (n + 1) → ℂ) :
    finiteExpectation q m (repeatTail n m a) = finiteExpectation q n a := by
  induction m generalizing n with
  | zero =>
      have hn0 : n = 0 := by omega
      subst n
      rw [repeatTail_self]
  | succ m ih =>
      by_cases he : n = m + 1
      · subst n
        rw [repeatTail_self]
      · have hm : n ≤ m := by omega
        rw [← repeatTail_comp n m (m + 1) hm a, finiteExpectation_step, ih n hm a]

theorem selectedExpectation_compatible (n m : ℕ) (hnm : n ≤ m)
    (a : Fin (n + 1) → ℂ) :
    (selectedDensity m * Matrix.diagonal (repeatTail n m a)).trace =
      (selectedDensity n * Matrix.diagonal a).trace := by
  change (geometricDensity (1 / 2) m * Matrix.diagonal (repeatTail n m a)).trace =
    (geometricDensity (1 / 2) n * Matrix.diagonal a).trace
  rw [← finiteExpectation_eq_trace, ← finiteExpectation_eq_trace]
  exact finiteExpectation_repeatTail (1 / 2) n m hnm a

theorem padVector_entropy_hasSum {n : ℕ} (p : Fin n → ℝ) :
    HasSum (fun k => Real.negMulLog (padVector p k)) (∑ i, Real.negMulLog (p i)) := by
  have he :
      (fun k => Real.negMulLog (padVector p k)) =
        padFunction (fun i => Real.negMulLog (p i)) := by
    funext k
    change Real.negMulLog (padFunction p k) = padFunction (fun i => Real.negMulLog (p i)) k
    by_cases hk : k < n
    · simp only [padFunction, dif_pos hk]
    · simp only [padFunction, dif_neg hk, Real.negMulLog_zero]
  rw [he]
  exact padFunction_hasSum (fun i => Real.negMulLog (p i))

theorem geometricEntropy_padding (q : ℝ) (n : ℕ) :
    (∑' k, Real.negMulLog (paddedGeometric q n k)) = entropy (geometricDensity q n) := by
  rw [geometricDensity_entropy]
  exact (padVector_entropy_hasSum (geometricWeight q n)).tsum_eq

theorem padVector_weighted_hasSum {n : ℕ} (p energy : Fin n → ℝ) :
    HasSum (fun k => padFunction energy k * padVector p k) (∑ i, energy i * p i) := by
  have he :
      (fun k => padFunction energy k * padVector p k) =
        padFunction (fun i => energy i * p i) := by
    funext k
    change padFunction energy k * padFunction p k = padFunction (fun i => energy i * p i) k
    by_cases hk : k < n
    · simp only [padFunction, dif_pos hk]
    · simp only [padFunction, dif_neg hk, zero_mul]
  rw [he]
  exact padFunction_hasSum (fun i => energy i * p i)

theorem geometricEnergy_padding (q r : ℝ) (n : ℕ) :
    (∑' k, padFunction (geometricEnergy r n) k * paddedGeometric q n k) =
      meanEnergy (geometricHamiltonian r n) (geometricDensity q n) := by
  change (∑' k, padFunction (geometricEnergy r n) k * padVector (geometricWeight q n) k) =
    meanEnergy (realDiagonal (geometricEnergy r n)) (realDiagonal (geometricWeight q n))
  rw [meanEnergy_realDiagonal]
  exact (padVector_weighted_hasSum (geometricWeight q n) (geometricEnergy r n)).tsum_eq

theorem geometricEnergy_interior {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) (i : Fin n) :
    geometricEnergy r n i.castSucc = infiniteEnergy r i.val :=
  geometricEnergy_castSucc hr0 hr1 n i

theorem geometricEnergy_last_offset (r : ℝ) (n : ℕ) :
    infiniteEnergy r n - geometricEnergy r n (Fin.last n) = -Real.log (1 - r) := by
  rw [geometricEnergy_last]
  unfold infiniteEnergy
  ring

theorem geometricEntropy_strict_step {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    entropy (geometricDensity q n) < entropy (geometricDensity q (n + 1)) := by
  have hb := Real.binEntropy_pos hq0 hq1
  have hp : 0 < q ^ n * Real.binEntropy q := by positivity
  rw [geometricDensity_entropy_succ]
  linarith

/-- The finite spike family has one head entry and an equal tail. -/
def spikeTailWeight (a : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val = 0 then 1 - a else a / (n : ℝ)

theorem spikeTailWeight_zero (a : ℝ) (n : ℕ) :
    spikeTailWeight a n 0 = 1 - a := by
  change (if 0 = 0 then 1 - a else a / (n : ℝ)) = 1 - a
  exact if_pos rfl

theorem spikeTailWeight_succ (a : ℝ) (n : ℕ) (i : Fin n) :
    spikeTailWeight a n i.succ = a / (n : ℝ) := by
  change (if i.val + 1 = 0 then 1 - a else a / (n : ℝ)) = a / (n : ℝ)
  exact if_neg (by omega)

theorem spikeTailWeight_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) : 0 < spikeTailWeight a n i := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold spikeTailWeight
  split_ifs
  · linarith
  · positivity

theorem spikeTailWeight_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (n : ℕ) (i : Fin (n + 1)) : 0 ≤ spikeTailWeight a n i := by
  unfold spikeTailWeight
  split_ifs
  · linarith
  · positivity

theorem spikeTailWeight_sum {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (∑ i, spikeTailWeight a n i) = 1 := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Fin.sum_univ_succ, spikeTailWeight_zero]
  simp only [spikeTailWeight_succ, Fin.sum_const, nsmul_eq_mul]
  field_simp [hnr.ne']

theorem spikeTailWeight_zero_parameter (n : ℕ) (i : Fin (n + 1)) :
    spikeTailWeight 0 n i = if i.val = 0 then 1 else 0 := by
  simp only [spikeTailWeight, sub_zero, zero_div]

theorem spikeTailWeight_zero_sum (n : ℕ) :
    (∑ i, spikeTailWeight 0 n i) = 1 := by
  rw [Fin.sum_univ_succ, spikeTailWeight_zero]
  simp only [spikeTailWeight_succ, zero_div, Fin.sum_const, nsmul_eq_mul,
    mul_zero, sub_zero, add_zero]

def spikeTailDensity (a : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  realDiagonal (spikeTailWeight a n)

theorem spikeTailDensity_entropy {n : ℕ} (hn : 0 < n) (a : ℝ) :
    entropy (spikeTailDensity a n) = Real.binEntropy a + a * Real.log (n : ℝ) := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have htail : (n : ℝ) * Real.negMulLog (a / (n : ℝ)) =
      Real.negMulLog a + a * Real.log (n : ℝ) := by
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    simp only [Real.negMulLog, Real.log_inv]
    field_simp [hnr.ne']
    ring
  change entropy (realDiagonal (spikeTailWeight a n)) = _
  rw [entropy_realDiagonal, Fin.sum_univ_succ]
  simp only [spikeTailWeight_zero, spikeTailWeight_succ, Fin.sum_const, nsmul_eq_mul]
  rw [htail, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

def pureDensity (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  realDiagonal (spikeTailWeight 0 n)

theorem pureDensity_density (n : ℕ) :
    (pureDensity n).PosSemidef ∧ (pureDensity n).trace = 1 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.zero_le_real.mpr
      (spikeTailWeight_nonneg (by norm_num) (by norm_num) n i)
  · change (realDiagonal (spikeTailWeight 0 n)).trace = 1
    rw [realDiagonal_trace, spikeTailWeight_zero_sum, Complex.ofReal_one]

theorem pureDensity_idempotent (n : ℕ) :
    pureDensity n * pureDensity n = pureDensity n := by
  unfold pureDensity realDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i.val = 0
  · simp only [spikeTailWeight, if_pos hi, sub_zero, Complex.ofReal_one, one_mul]
  · simp only [spikeTailWeight, if_neg hi, zero_div, Complex.ofReal_zero, zero_mul]

theorem pureDensity_entropy (n : ℕ) : entropy (pureDensity n) = 0 := by
  change entropy (realDiagonal (spikeTailWeight 0 n)) = 0
  rw [entropy_realDiagonal]
  apply Finset.sum_eq_zero
  intro i _
  unfold spikeTailWeight
  split_ifs
  · rw [sub_zero, Real.negMulLog_one]
  · rw [zero_div, Real.negMulLog_zero]

def pureState : DiagonalL1 :=
  padVector (spikeTailWeight 0 0)

theorem padSpikeZero_apply (n k : ℕ) :
    padVector (spikeTailWeight 0 n) k = if k = 0 then 1 else 0 := by
  change padFunction (spikeTailWeight 0 n) k = _
  by_cases hk : k < n + 1
  · rw [padFunction, dif_pos hk, spikeTailWeight_zero_parameter]
  · have hk0 : k ≠ 0 := by omega
    rw [padFunction, dif_neg hk, if_neg hk0]

theorem pureState_apply (k : ℕ) :
    pureState k = if k = 0 then 1 else 0 :=
  padSpikeZero_apply 0 k

theorem padSpikeZero (n : ℕ) : padVector (spikeTailWeight 0 n) = pureState := by
  apply lp.ext
  funext k
  rw [padSpikeZero_apply, pureState_apply]

theorem pureState_nonneg (k : ℕ) : 0 ≤ pureState k :=
  padVector_nonneg (spikeTailWeight 0 0)
    (spikeTailWeight_nonneg (by norm_num) (by norm_num) 0) k

theorem pureState_normalized : (∑' k, pureState k) = 1 :=
  padVector_normalized (spikeTailWeight 0 0) (spikeTailWeight_zero_sum 0)

theorem pureState_entropy : (∑' k, Real.negMulLog (pureState k)) = 0 := by
  change (∑' k, Real.negMulLog (padVector (spikeTailWeight 0 0) k)) = 0
  rw [(padVector_entropy_hasSum (spikeTailWeight 0 0)).tsum_eq, ← entropy_realDiagonal]
  exact pureDensity_entropy 0

theorem spikeTail_norm_error {a : ℝ} (ha0 : 0 ≤ a) {n : ℕ} (hn : 0 < n) :
    ‖padVector (spikeTailWeight a n) - pureState‖ = 2 * a := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have htail : 0 ≤ a / (n : ℝ) := by positivity
  have hhead : |(1 - a) - 1| = a := by
    have he : (1 - a) - 1 = -a := by ring
    rw [he, abs_neg, abs_of_nonneg ha0]
  rw [← padSpikeZero n, padVector_norm_sub, Fin.sum_univ_succ]
  simp only [spikeTailWeight_zero, spikeTailWeight_succ, zero_div, sub_zero]
  rw [hhead]
  simp only [abs_of_nonneg htail, Fin.sum_const, nsmul_eq_mul]
  field_simp [hnr.ne']
  ring

/-- The logarithmic family retains the exact head and tail eigenvalues from the roadmap. -/
def logarithmicTailWeight (n : ℕ) : Fin (n + 1) → ℝ :=
  spikeTailWeight (1 / Real.log (n : ℝ)) n

theorem logarithmicTailWeight_zero (n : ℕ) :
    logarithmicTailWeight n 0 = 1 - 1 / Real.log (n : ℝ) :=
  spikeTailWeight_zero (1 / Real.log (n : ℝ)) n

theorem logarithmicTailWeight_succ (n : ℕ) (i : Fin n) :
    logarithmicTailWeight n i.succ = 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  change spikeTailWeight (1 / Real.log (n : ℝ)) n i.succ = _
  rw [spikeTailWeight_succ, div_div, mul_comm (Real.log (n : ℝ)) (n : ℝ)]

theorem logarithmicTailWeight_pos {n : ℕ} (hn : 0 < n)
    (hlog : 1 < Real.log (n : ℝ)) (i : Fin (n + 1)) :
    0 < logarithmicTailWeight n i := by
  have hlog0 : 0 < Real.log (n : ℝ) := by linarith
  exact spikeTailWeight_pos (by positivity) ((div_lt_one hlog0).2 hlog) hn i

theorem logarithmicTailWeight_sum {n : ℕ} (hn : 0 < n) :
    (∑ i, logarithmicTailWeight n i) = 1 :=
  spikeTailWeight_sum hn (1 / Real.log (n : ℝ))

def logarithmicTailDensity (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  realDiagonal (logarithmicTailWeight n)

theorem logarithmicTailDensity_posDef {n : ℕ} (hn : 0 < n)
    (hlog : 1 < Real.log (n : ℝ)) : (logarithmicTailDensity n).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact Complex.zero_lt_real.mpr (logarithmicTailWeight_pos hn hlog i)

theorem logarithmicTailDensity_trace {n : ℕ} (hn : 0 < n) :
    (logarithmicTailDensity n).trace = 1 := by
  change (realDiagonal (logarithmicTailWeight n)).trace = 1
  rw [realDiagonal_trace, logarithmicTailWeight_sum hn, Complex.ofReal_one]

theorem logarithmicTailDensity_density {n : ℕ} (hn : 0 < n)
    (hlog : 1 < Real.log (n : ℝ)) :
    (logarithmicTailDensity n).PosSemidef ∧ (logarithmicTailDensity n).trace = 1 :=
  ⟨(logarithmicTailDensity_posDef hn hlog).posSemidef, logarithmicTailDensity_trace hn⟩

theorem logarithmicTailDensity_entropy {n : ℕ} (hn : 0 < n)
    (hlog : 0 < Real.log (n : ℝ)) :
    entropy (logarithmicTailDensity n) = 1 + Real.binEntropy (1 / Real.log (n : ℝ)) := by
  change entropy (spikeTailDensity (1 / Real.log (n : ℝ)) n) = _
  rw [spikeTailDensity_entropy hn]
  have hc : (1 / Real.log (n : ℝ)) * Real.log (n : ℝ) = 1 := by
    field_simp [hlog.ne']
  rw [hc]
  ring

def logarithmicTailState (n : ℕ) : DiagonalL1 :=
  padVector (logarithmicTailWeight n)

theorem logarithmicTailState_nonneg {n : ℕ} (hn : 0 < n)
    (hlog : 1 < Real.log (n : ℝ)) (k : ℕ) : 0 ≤ logarithmicTailState n k :=
  padVector_nonneg (logarithmicTailWeight n)
    (fun i => (logarithmicTailWeight_pos hn hlog i).le) k

theorem logarithmicTailState_normalized {n : ℕ} (hn : 0 < n) :
    (∑' k, logarithmicTailState n k) = 1 :=
  padVector_normalized (logarithmicTailWeight n) (logarithmicTailWeight_sum hn)

theorem logarithmicTailState_entropy (n : ℕ) :
    (∑' k, Real.negMulLog (logarithmicTailState n k)) =
      entropy (logarithmicTailDensity n) := by
  rw [logarithmicTailDensity, entropy_realDiagonal]
  exact (padVector_entropy_hasSum (logarithmicTailWeight n)).tsum_eq

theorem logarithmicTailState_norm_error {n : ℕ} (hn : 0 < n)
    (hlog : 0 < Real.log (n : ℝ)) :
    ‖logarithmicTailState n - pureState‖ = 2 / Real.log (n : ℝ) := by
  change ‖padVector (spikeTailWeight (1 / Real.log (n : ℝ)) n) - pureState‖ = _
  rw [spikeTail_norm_error (by positivity) hn]
  ring

theorem logarithmicLog_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem logarithmicParameter_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
  logarithmicLog_tendsto_atTop.const_div_atTop 1

theorem eventually_logarithmic_valid :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < n ∧ 1 < Real.log (n : ℝ) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ),
    logarithmicLog_tendsto_atTop.eventually (Filter.eventually_gt_atTop (1 : ℝ))]
    with n hn hlog
  exact ⟨hn, hlog⟩

theorem logarithmicTailDensity_eventually_positive :
    ∀ᶠ n : ℕ in Filter.atTop,
      (logarithmicTailDensity n).PosDef ∧ (logarithmicTailDensity n).trace = 1 := by
  filter_upwards [eventually_logarithmic_valid] with n hn
  exact ⟨logarithmicTailDensity_posDef hn.1 hn.2, logarithmicTailDensity_trace hn.1⟩

theorem logarithmicTailState_norm_tendsto :
    Filter.Tendsto (fun n => ‖logarithmicTailState n - pureState‖)
      Filter.atTop (nhds 0) := by
  apply (logarithmicLog_tendsto_atTop.const_div_atTop 2).congr'
  filter_upwards [eventually_logarithmic_valid] with n hn
  exact (logarithmicTailState_norm_error hn.1 (by linarith [hn.2])).symm

theorem logarithmicTailState_tendsto :
    Filter.Tendsto logarithmicTailState Filter.atTop (nhds pureState) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr logarithmicTailState_norm_tendsto

theorem logarithmicTailDensity_entropy_tendsto :
    Filter.Tendsto (fun n => entropy (logarithmicTailDensity n))
      Filter.atTop (nhds 1) := by
  have hbin :
      Filter.Tendsto (fun n : ℕ => Real.binEntropy (1 / Real.log (n : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [Real.binEntropy_zero] using
      (Real.binEntropy_continuous.tendsto 0).comp logarithmicParameter_tendsto_zero
  have hone :
      Filter.Tendsto (fun n : ℕ => 1 + Real.binEntropy (1 / Real.log (n : ℝ)))
        Filter.atTop (nhds 1) := by
    simpa only [add_zero] using hbin.const_add (1 : ℝ)
  apply hone.congr'
  filter_upwards [eventually_logarithmic_valid] with n hn
  exact (logarithmicTailDensity_entropy hn.1 (by linarith [hn.2])).symm

theorem logarithmicTailState_entropy_tendsto :
    Filter.Tendsto (fun n => ∑' k, Real.negMulLog (logarithmicTailState n k))
      Filter.atTop (nhds 1) := by
  have he :
      (fun n => ∑' k, Real.negMulLog (logarithmicTailState n k)) =
        (fun n => entropy (logarithmicTailDensity n)) :=
    funext logarithmicTailState_entropy
  rw [he]
  exact logarithmicTailDensity_entropy_tendsto

/-- The guarded sequence supplies density matrices at every index and the exact roadmap family eventually. -/
def controlledLogarithmicWeight (n : ℕ) : Fin (n + 1) → ℝ :=
  if 0 < n ∧ 1 < Real.log (n : ℝ) then logarithmicTailWeight n else spikeTailWeight 0 n

theorem controlledLogarithmicWeight_eq {n : ℕ}
    (hn : 0 < n ∧ 1 < Real.log (n : ℝ)) :
    controlledLogarithmicWeight n = logarithmicTailWeight n :=
  if_pos hn

theorem controlledLogarithmicWeight_nonneg (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ controlledLogarithmicWeight n i := by
  unfold controlledLogarithmicWeight
  split_ifs with hn
  · exact (logarithmicTailWeight_pos hn.1 hn.2 i).le
  · exact spikeTailWeight_nonneg (by norm_num) (by norm_num) n i

theorem controlledLogarithmicWeight_sum (n : ℕ) :
    (∑ i, controlledLogarithmicWeight n i) = 1 := by
  unfold controlledLogarithmicWeight
  split_ifs with hn
  · exact logarithmicTailWeight_sum hn.1
  · exact spikeTailWeight_zero_sum n

def controlledLogarithmicDensity (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  realDiagonal (controlledLogarithmicWeight n)

theorem controlledLogarithmicDensity_density (n : ℕ) :
    (controlledLogarithmicDensity n).PosSemidef ∧
      (controlledLogarithmicDensity n).trace = 1 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.zero_le_real.mpr (controlledLogarithmicWeight_nonneg n i)
  · change (realDiagonal (controlledLogarithmicWeight n)).trace = 1
    rw [realDiagonal_trace, controlledLogarithmicWeight_sum, Complex.ofReal_one]

theorem controlledLogarithmicDensity_eq {n : ℕ}
    (hn : 0 < n ∧ 1 < Real.log (n : ℝ)) :
    controlledLogarithmicDensity n = logarithmicTailDensity n := by
  unfold controlledLogarithmicDensity logarithmicTailDensity
  rw [controlledLogarithmicWeight_eq hn]

def controlledLogarithmicState (n : ℕ) : DiagonalL1 :=
  padVector (controlledLogarithmicWeight n)

theorem controlledLogarithmicState_nonneg (n k : ℕ) :
    0 ≤ controlledLogarithmicState n k :=
  padVector_nonneg (controlledLogarithmicWeight n) (controlledLogarithmicWeight_nonneg n) k

theorem controlledLogarithmicState_normalized (n : ℕ) :
    (∑' k, controlledLogarithmicState n k) = 1 :=
  padVector_normalized (controlledLogarithmicWeight n) (controlledLogarithmicWeight_sum n)

theorem controlledLogarithmicState_eq {n : ℕ}
    (hn : 0 < n ∧ 1 < Real.log (n : ℝ)) :
    controlledLogarithmicState n = logarithmicTailState n := by
  unfold controlledLogarithmicState logarithmicTailState
  rw [controlledLogarithmicWeight_eq hn]

theorem controlledLogarithmicState_norm_tendsto :
    Filter.Tendsto (fun n => ‖controlledLogarithmicState n - pureState‖)
      Filter.atTop (nhds 0) := by
  apply logarithmicTailState_norm_tendsto.congr'
  filter_upwards [eventually_logarithmic_valid] with n hn
  rw [controlledLogarithmicState_eq hn]

theorem controlledLogarithmicState_tendsto :
    Filter.Tendsto controlledLogarithmicState Filter.atTop (nhds pureState) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr controlledLogarithmicState_norm_tendsto

theorem controlledLogarithmicDensity_entropy_tendsto :
    Filter.Tendsto (fun n => entropy (controlledLogarithmicDensity n))
      Filter.atTop (nhds 1) := by
  apply logarithmicTailDensity_entropy_tendsto.congr'
  filter_upwards [eventually_logarithmic_valid] with n hn
  rw [controlledLogarithmicDensity_eq hn]

theorem controlledLogarithmicState_entropy (n : ℕ) :
    (∑' k, Real.negMulLog (controlledLogarithmicState n k)) =
      entropy (controlledLogarithmicDensity n) := by
  rw [controlledLogarithmicDensity, entropy_realDiagonal]
  exact (padVector_entropy_hasSum (controlledLogarithmicWeight n)).tsum_eq

theorem controlledLogarithmicState_entropy_tendsto :
    Filter.Tendsto (fun n => ∑' k, Real.negMulLog (controlledLogarithmicState n k))
      Filter.atTop (nhds 1) := by
  have he :
      (fun n => ∑' k, Real.negMulLog (controlledLogarithmicState n k)) =
        (fun n => entropy (controlledLogarithmicDensity n)) :=
    funext controlledLogarithmicState_entropy
  rw [he]
  exact controlledLogarithmicDensity_entropy_tendsto

theorem controlledLogarithmic_entropy_not_tendsto_pure :
    ¬Filter.Tendsto (fun n => entropy (controlledLogarithmicDensity n))
      Filter.atTop (nhds (∑' k, Real.negMulLog (pureState k))) := by
  rw [pureState_entropy]
  intro h
  have hbad : (1 : ℝ) = 0 :=
    tendsto_nhds_unique controlledLogarithmicDensity_entropy_tendsto h
  norm_num at hbad

/-- The counterexample combines normalized finite realizations, standard norm convergence and entropy failure. -/
theorem logarithmic_entropy_negative_control :
    (∀ n, (controlledLogarithmicDensity n).PosSemidef ∧
      (controlledLogarithmicDensity n).trace = 1) ∧
    (∀ᶠ n : ℕ in Filter.atTop, controlledLogarithmicWeight n = logarithmicTailWeight n) ∧
    Filter.Tendsto controlledLogarithmicState Filter.atTop (nhds pureState) ∧
    Filter.Tendsto (fun n => ∑' k, Real.negMulLog (controlledLogarithmicState n k))
      Filter.atTop (nhds 1) ∧
    (∑' k, Real.negMulLog (pureState k)) = 0 := by
  refine ⟨controlledLogarithmicDensity_density, ?_, controlledLogarithmicState_tendsto,
    controlledLogarithmicState_entropy_tendsto, pureState_entropy⟩
  filter_upwards [eventually_logarithmic_valid] with n hn
  exact controlledLogarithmicWeight_eq hn

theorem selectedState_tendsto :
    Filter.Tendsto (paddedGeometric (1 / 2)) Filter.atTop (nhds selectedState) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr selectedState_norm_limit

theorem infiniteEnergy_nonneg {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    0 ≤ infiniteEnergy r k := by
  have hhead : Real.log (1 - r) < 0 := Real.log_neg (by linarith) (by linarith)
  have hstep : Real.log r < 0 := Real.log_neg hr0 hr1
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hprod : 0 ≤ (k : ℝ) * (-Real.log r) := mul_nonneg hk (by linarith)
  unfold infiniteEnergy
  linarith

/-- The padded energy density uses the declared finite Hamiltonian and the same finite state. -/
def paddedEnergyDensity (q r : ℝ) (n k : ℕ) : ℝ :=
  padFunction (geometricEnergy r n) k * paddedGeometric q n k

theorem paddedEnergyDensity_before {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (q : ℝ) (n k : ℕ) (hk : k < n) :
    paddedEnergyDensity q r n k = infiniteEnergy r k * infiniteWeight q k := by
  rw [paddedEnergyDensity, paddedGeometric_before q n k hk,
    padFunction, dif_pos (show k < n + 1 by omega)]
  change geometricEnergy r n (Fin.castSucc ⟨k, hk⟩) * infiniteWeight q k = _
  rw [geometricEnergy_interior hr0 hr1]

theorem paddedEnergyDensity_at (q r : ℝ) (n : ℕ) :
    paddedEnergyDensity q r n n = (-(n : ℝ) * Real.log r) * q ^ n := by
  rw [paddedEnergyDensity, paddedGeometric_at, padFunction,
    dif_pos (show n < n + 1 by omega)]
  change geometricEnergy r n (Fin.last n) * q ^ n = _
  rw [geometricEnergy_last]

theorem paddedEnergyDensity_after (q r : ℝ) (n k : ℕ) (hk : n < k) :
    paddedEnergyDensity q r n k = 0 := by
  rw [paddedEnergyDensity, paddedGeometric_after q n k hk, mul_zero]

theorem paddedEnergyDensity_nonneg {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) (n k : ℕ) :
    0 ≤ paddedEnergyDensity q r n k := by
  by_cases hk : k < n
  · rw [paddedEnergyDensity_before hr0 hr1 q n k hk]
    exact mul_nonneg (infiniteEnergy_nonneg hr0 hr1 k) (infiniteWeight_nonneg hq0 hq1 k)
  · by_cases he : k = n
    · subst k
      rw [paddedEnergyDensity_at]
      have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
      have hn : 0 ≤ (n : ℝ) := by positivity
      have he : 0 ≤ -(n : ℝ) * Real.log r := by nlinarith
      exact mul_nonneg he (pow_nonneg hq0 n)
    · calc
        0 ≤ (0 : ℝ) := le_rfl
        _ = paddedEnergyDensity q r n k :=
          (paddedEnergyDensity_after q r n k (by omega)).symm

theorem paddedEnergyDensity_le {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) (n k : ℕ) :
    paddedEnergyDensity q r n k ≤
      (infiniteEnergy r k * infiniteWeight q k) / (1 - q) := by
  have hden : 0 < 1 - q := by linarith
  by_cases hk : k < n
  · rw [paddedEnergyDensity_before hr0 hr1 q n k hk]
    exact le_div_self
      (mul_nonneg (infiniteEnergy_nonneg hr0 hr1 k) (infiniteWeight_nonneg hq0 hq1 k))
      hden (by linarith)
  · by_cases he : k = n
    · subst k
      rw [paddedEnergyDensity_at, le_div_iff₀ hden]
      have hhead : 0 ≤ -Real.log (1 - r) := by
        have h := Real.log_neg (show 0 < 1 - r by linarith) (show 1 - r < 1 by linarith)
        linarith
      have hp : 0 ≤ (1 - q) * (-Real.log (1 - r)) * q ^ n := by positivity
      unfold infiniteEnergy infiniteWeight
      nlinarith
    · rw [paddedEnergyDensity_after q r n k (by omega)]
      have hn := mul_nonneg (infiniteEnergy_nonneg hr0 hr1 k)
        (infiniteWeight_nonneg hq0 hq1 k)
      positivity

theorem paddedEnergyDensity_entropy (q : ℝ) (n k : ℕ) :
    paddedEnergyDensity q q n k = Real.negMulLog (paddedGeometric q n k) := by
  change padFunction (geometricEnergy q n) k * padFunction (geometricWeight q n) k =
    Real.negMulLog (padFunction (geometricWeight q n) k)
  by_cases hk : k < n + 1
  · simp only [padFunction, dif_pos hk, geometricEnergy, logEnergy, Real.negMulLog]
    ring
  · simp only [padFunction, dif_neg hk, zero_mul, Real.negMulLog_zero]

theorem paddedEnergyDensity_summable (q r : ℝ) (n K : ℕ) :
    Summable (fun k => paddedEnergyDensity q r n (K + k)) := by
  have hs :
      HasSum (fun k => paddedEnergyDensity q r n (K + k))
        (∑ k ∈ Finset.range (n + 1), paddedEnergyDensity q r n (K + k)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hk' : ¬k < n + 1 := by simpa only [Finset.mem_range] using hk
    exact paddedEnergyDensity_after q r n (K + k) (by omega)
  exact hs.summable

def finiteEnergyTail (q r : ℝ) (n K : ℕ) : ℝ :=
  ∑' k, paddedEnergyDensity q r n (K + k)

def finiteEnergyTailBound (q r : ℝ) (K : ℕ) : ℝ :=
  energyTail q r K / (1 - q)

theorem finiteEnergyTailBound_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (r : ℝ) (K : ℕ) :
    finiteEnergyTailBound q r K =
      q ^ K * (geometricCrossEnergy q r - (K : ℝ) * Real.log r) / (1 - q) := by
  rw [finiteEnergyTailBound, energyTail_eq hq0 hq1]

theorem finiteEnergyTail_bound {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) (n K : ℕ) :
    0 ≤ finiteEnergyTail q r n K ∧
      finiteEnergyTail q r n K ≤ finiteEnergyTailBound q r K := by
  have hD :
      HasSum (fun k => infiniteEnergy r (K + k) * infiniteWeight q (K + k))
        (energyTail q r K) :=
    (energyTail_hasSum hq0 hq1 r K).summable.hasSum
  have hd :
      HasSum (fun k => (infiniteEnergy r (K + k) * infiniteWeight q (K + k)) / (1 - q))
        (finiteEnergyTailBound q r K) := by
    simpa only [finiteEnergyTailBound, div_eq_mul_inv] using hD.mul_right (1 - q)⁻¹
  constructor
  · exact tsum_nonneg (fun k => paddedEnergyDensity_nonneg hq0 hq1 hr0 hr1 n (K + k))
  · calc
      finiteEnergyTail q r n K ≤
          ∑' k, (infiniteEnergy r (K + k) * infiniteWeight q (K + k)) / (1 - q) :=
        Summable.tsum_le_tsum
          (fun k => paddedEnergyDensity_le hq0 hq1 hr0 hr1 n (K + k))
          (paddedEnergyDensity_summable q r n K) hd.summable
      _ = finiteEnergyTailBound q r K := hd.tsum_eq

theorem finiteEnergyTailBound_tendsto {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℝ) :
    Filter.Tendsto (finiteEnergyTailBound q r) Filter.atTop (nhds 0) := by
  simpa only [finiteEnergyTailBound, div_eq_mul_inv, zero_mul] using
    (energyTail_tendsto hq0 hq1 r).mul_const (1 - q)⁻¹

/-- Uniform tail control quantifies over all finite stages at each sufficiently large cutoff. -/
def UniformFiniteEnergyTailControl (q r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ K : ℕ in Filter.atTop, ∀ n : ℕ, finiteEnergyTail q r n K < ε

theorem geometric_uniform_energy_tails {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    UniformFiniteEnergyTailControl q r := by
  intro ε hε
  have h := (tendsto_order.mp (finiteEnergyTailBound_tendsto hq0 hq1 r)).2 ε hε
  filter_upwards [h] with K hK
  intro n
  exact lt_of_le_of_lt (finiteEnergyTail_bound hq0 hq1 hr0 hr1 n K).2 hK

def finiteEntropyTail (q : ℝ) (n K : ℕ) : ℝ :=
  ∑' k, Real.negMulLog (paddedGeometric q n (K + k))

theorem finiteEntropyTail_eq_energyTail (q : ℝ) (n K : ℕ) :
    finiteEntropyTail q n K = finiteEnergyTail q q n K := by
  have he :
      (fun k => Real.negMulLog (paddedGeometric q n (K + k))) =
        (fun k => paddedEnergyDensity q q n (K + k)) :=
    funext (fun k => (paddedEnergyDensity_entropy q n (K + k)).symm)
  unfold finiteEntropyTail finiteEnergyTail
  rw [he]

theorem finiteEntropyTail_bound {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (n K : ℕ) :
    0 ≤ finiteEntropyTail q n K ∧
      finiteEntropyTail q n K ≤
        q ^ K * (geometricEntropy q - (K : ℝ) * Real.log q) / (1 - q) := by
  rw [finiteEntropyTail_eq_energyTail]
  have h := finiteEnergyTail_bound hq0.le hq1 hq0 hq1 n K
  rw [finiteEnergyTailBound_eq hq0.le hq1, geometricCrossEnergy_self hq1] at h
  exact h

def UniformFiniteEntropyTailControl (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ K : ℕ in Filter.atTop, ∀ n : ℕ, finiteEntropyTail q n K < ε

theorem geometric_uniform_entropy_tails {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    UniformFiniteEntropyTailControl q := by
  intro ε hε
  filter_upwards [geometric_uniform_energy_tails hq0.le hq1 hq0 hq1 ε hε] with K hK
  intro n
  rw [finiteEntropyTail_eq_energyTail]
  exact hK n

theorem selected_finite_tail_control :
    UniformFiniteEntropyTailControl (1 / 2) ∧
      UniformFiniteEntropyTailControl (1 / 4) ∧
      UniformFiniteEnergyTailControl (1 / 2) (1 / 4) ∧
      UniformFiniteEnergyTailControl (1 / 4) (1 / 4) :=
  ⟨geometric_uniform_entropy_tails (by norm_num) (by norm_num),
    geometric_uniform_entropy_tails (by norm_num) (by norm_num),
    geometric_uniform_energy_tails (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    geometric_uniform_energy_tails (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

theorem selected_controlled_thermodynamic_limits :
    UniformFiniteEntropyTailControl (1 / 2) ∧
    UniformFiniteEnergyTailControl (1 / 2) (1 / 4) ∧
    UniformFiniteEnergyTailControl (1 / 4) (1 / 4) ∧
    Filter.Tendsto (paddedGeometric (1 / 2)) Filter.atTop (nhds selectedState) ∧
    Filter.Tendsto (fun n => entropy (selectedDensity n))
      Filter.atTop (nhds (2 * Real.log 2)) ∧
    Filter.Tendsto selectedHeat Filter.atTop (nhds ((2 / 3) * Real.log 4)) ∧
    LimitReportsGoal selectedReports selectedLimitReports :=
  ⟨selected_finite_tail_control.1, selected_finite_tail_control.2.2.1,
    selected_finite_tail_control.2.2.2, selectedState_tendsto, selectedEntropy_tendsto,
    selectedHeat_tendsto, LimitReportsGoal_proof⟩

theorem selectedCrossEnergy_value :
    geometricCrossEnergy (1 / 2) (1 / 4) = 2 * Real.log 4 - Real.log 3 := by
  have hhead : Real.log (1 - (1 : ℝ) / 4) = Real.log 3 - Real.log 4 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have htail : Real.log ((1 : ℝ) / 4) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  unfold geometricCrossEnergy
  rw [hhead, htail]
  norm_num
  ring

theorem selectedBathEntropy_value :
    geometricEntropy (1 / 4) = (4 / 3) * Real.log 4 - Real.log 3 := by
  have hhead : Real.log (1 - (1 : ℝ) / 4) = Real.log 3 - Real.log 4 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have htail : Real.log ((1 : ℝ) / 4) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  rw [geometricEntropy_eq (show (1 : ℝ) / 4 < 1 by norm_num), hhead, htail]
  norm_num
  ring

theorem selectedEntropy_closed (n : ℕ) :
    entropy (selectedDensity n) = (1 - ((1 : ℝ) / 2) ^ n) * (2 * Real.log 2) := by
  change entropy (geometricDensity (1 / 2) n) = _
  rw [geometricDensity_entropy_closed (show (1 : ℝ) / 2 < 1 by norm_num), selectedEntropy_value]

theorem selectedEntropy_error (n : ℕ) :
    |entropy (selectedDensity n) - 2 * Real.log 2| =
      ((1 : ℝ) / 2) ^ n * (2 * Real.log 2) := by
  have h := geometricEntropy_error
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num) n
  rw [selectedEntropy_value] at h
  exact h

theorem selectedHeat_closed (n : ℕ) :
    selectedHeat n =
      (1 - ((1 : ℝ) / 2) ^ n) * (2 * Real.log 4 - Real.log 3) -
        (1 - ((1 : ℝ) / 4) ^ n) * ((4 / 3) * Real.log 4 - Real.log 3) := by
  change geometricHeat (1 / 2) (1 / 4) n = _
  rw [geometricHeat_closed (show (1 : ℝ) / 2 < 1 by norm_num)
    (show (0 : ℝ) < 1 / 4 by norm_num) (show (1 : ℝ) / 4 < 1 by norm_num),
    selectedCrossEnergy_value, selectedBathEntropy_value]

theorem selectedHeat_error (n : ℕ) :
    |selectedHeat n - (2 / 3) * Real.log 4| ≤
      ((1 : ℝ) / 2) ^ n * (2 * Real.log 4 - Real.log 3) +
        ((1 : ℝ) / 4) ^ n * ((4 / 3) * Real.log 4 - Real.log 3) := by
  have h := geometricHeat_error
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)
    (show (0 : ℝ) < 1 / 4 by norm_num) (show (1 : ℝ) / 4 < 1 by norm_num) n
  rw [selectedCrossEnergy_value, selectedBathEntropy_value] at h
  have he :
      (2 * Real.log 4 - Real.log 3) - ((4 / 3) * Real.log 4 - Real.log 3) =
        (2 / 3) * Real.log 4 := by ring
  rw [he] at h
  exact h

theorem selectedHeat_one : selectedHeat 1 = (1 / 4) * Real.log 3 := by
  rw [selectedHeat_closed]
  norm_num
  ring

theorem selectedHeat_one_pos : 0 < selectedHeat 1 := by
  rw [selectedHeat_one]
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  positivity

theorem selectedEntropy_one : entropy (selectedDensity 1) = Real.log 2 := by
  rw [selectedEntropy_closed]
  norm_num
  ring

theorem selectedEntropy_one_pos : 0 < entropy (selectedDensity 1) := by
  rw [selectedEntropy_one]
  exact Real.log_pos (by norm_num)

/-! ### M5.7: a license for passing entropy and heat through the infinite limit

The license is a uniform smallness condition on the tails of the summands. With pointwise
convergence of the summands it gives convergence of the infinite sums. The geometric
family satisfies the condition for its entropy and for its reservoir energy, so its finite
entropies and heats converge to the infinite values. The logarithmic family converges in
trace norm to a pure state while its entropy converges to one nat, so it violates the
condition.
-/

/-- The tails of a family of sequences are uniformly small along the family. -/
def UniformTailControl (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in Filter.atTop, ∀ n : ℕ, |∑' k, f n (K + k)| < ε

/-- The tail of one sequence is eventually small, with no summability premise. -/
theorem tail_eventually_small (g : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in Filter.atTop, |∑' k, g (K + k)| < ε := by
  have h := (Metric.tendsto_nhds.mp (tendsto_sum_nat_add g)) ε hε
  filter_upwards [h] with K hK
  have he : (fun k => g (K + k)) = fun k => g (k + K) := by
    funext k
    rw [Nat.add_comm]
  rw [he]
  rw [Real.dist_eq, sub_zero] at hK
  exact hK

/-- Pointwise convergence and uniformly small tails pass an infinite sum to the limit. -/
theorem tendsto_tsum_of_uniformTailControl (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ n, Summable (f n)) (hg : Summable g)
    (hpt : ∀ k, Filter.Tendsto (fun n => f n k) Filter.atTop (nhds (g k)))
    (hunif : UniformTailControl f) :
    Filter.Tendsto (fun n => ∑' k, f n k) Filter.atTop (nhds (∑' k, g k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h3 : 0 < ε / 3 := by positivity
  obtain ⟨K, hKf, hKg⟩ := ((hunif (ε / 3) h3).and (tail_eventually_small g h3)).exists
  have hfin : Filter.Tendsto (fun n => ∑ k ∈ Finset.range K, f n k) Filter.atTop
      (nhds (∑ k ∈ Finset.range K, g k)) :=
    tendsto_finset_sum (Finset.range K) (fun k _ => hpt k)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hfin (ε / 3) h3
  refine ⟨N, fun n hn => ?_⟩
  have hsplitf := (hf n).sum_add_tsum_nat_add K
  have hsplitg := hg.sum_add_tsum_nat_add K
  have hcf : (fun k => f n (k + K)) = fun k => f n (K + k) := by
    funext k
    rw [Nat.add_comm]
  have hcg : (fun k => g (k + K)) = fun k => g (K + k) := by
    funext k
    rw [Nat.add_comm]
  rw [hcf] at hsplitf
  rw [hcg] at hsplitg
  have hfinn := hN n hn
  rw [Real.dist_eq] at hfinn ⊢
  rw [← hsplitf, ← hsplitg]
  have ha := abs_lt.mp hfinn
  have hb := abs_lt.mp (hKf n)
  have hc := abs_lt.mp hKg
  rw [abs_lt]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

/-- Entropy license: convergent probabilities with uniformly small entropy tails have
convergent entropies. -/
theorem entropy_tendsto_of_uniformTailControl (p : ℕ → ℕ → ℝ) (pinf : ℕ → ℝ)
    (hp : ∀ n, Summable (fun k => Real.negMulLog (p n k)))
    (hpinf : Summable (fun k => Real.negMulLog (pinf k)))
    (hpt : ∀ k, Filter.Tendsto (fun n => p n k) Filter.atTop (nhds (pinf k)))
    (hunif : UniformTailControl (fun n k => Real.negMulLog (p n k))) :
    Filter.Tendsto (fun n => ∑' k, Real.negMulLog (p n k)) Filter.atTop
      (nhds (∑' k, Real.negMulLog (pinf k))) :=
  tendsto_tsum_of_uniformTailControl (fun n k => Real.negMulLog (p n k))
    (fun k => Real.negMulLog (pinf k)) hp hpinf
    (fun k => (Real.continuous_negMulLog.tendsto (pinf k)).comp (hpt k)) hunif

/-- Energy license: convergent probabilities with uniformly small energy tails have
convergent mean energies. -/
theorem energy_tendsto_of_uniformTailControl (p : ℕ → ℕ → ℝ) (pinf : ℕ → ℝ)
    (E : ℕ → ℕ → ℝ) (Einf : ℕ → ℝ)
    (hp : ∀ n, Summable (fun k => E n k * p n k))
    (hpinf : Summable (fun k => Einf k * pinf k))
    (hpt : ∀ k, Filter.Tendsto (fun n => p n k) Filter.atTop (nhds (pinf k)))
    (hEt : ∀ k, Filter.Tendsto (fun n => E n k) Filter.atTop (nhds (Einf k)))
    (hunif : UniformTailControl (fun n k => E n k * p n k)) :
    Filter.Tendsto (fun n => ∑' k, E n k * p n k) Filter.atTop
      (nhds (∑' k, Einf k * pinf k)) :=
  tendsto_tsum_of_uniformTailControl (fun n k => E n k * p n k) (fun k => Einf k * pinf k)
    hp hpinf (fun k => (hEt k).mul (hpt k)) hunif

/-- Each coordinate of the geometric cutoff is eventually the infinite geometric weight. -/
theorem paddedGeometric_pointwise (q : ℝ) (k : ℕ) :
    Filter.Tendsto (fun n => paddedGeometric q n k) Filter.atTop
      (nhds (infiniteWeight q k)) := by
  apply tendsto_atTop_of_eventually_const (i₀ := k + 1)
  intro n hn
  exact paddedGeometric_before q n k (by omega)

theorem paddedGeometric_entropy_summable (q : ℝ) (n : ℕ) :
    Summable (fun k => Real.negMulLog (paddedGeometric q n k)) :=
  (padVector_entropy_hasSum (geometricWeight q n)).summable

/-- The geometric family satisfies the entropy license. -/
theorem geometric_entropy_uniformTailControl {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    UniformTailControl (fun n k => Real.negMulLog (paddedGeometric q n k)) := by
  intro ε hε
  filter_upwards [geometric_uniform_entropy_tails hq0 hq1 ε hε] with K hK
  intro n
  have hnn := (finiteEntropyTail_bound hq0 hq1 n K).1
  change |finiteEntropyTail q n K| < ε
  rw [abs_of_nonneg hnn]
  exact hK n

/-- The license derives the infinite entropy limit of the actual finite densities. -/
theorem geometricEntropy_limit_by_license {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Filter.Tendsto (fun n => entropy (geometricDensity q n)) Filter.atTop
      (nhds (infiniteEntropy q)) := by
  have h := entropy_tendsto_of_uniformTailControl (fun n k => paddedGeometric q n k)
    (infiniteWeight q) (paddedGeometric_entropy_summable q)
    (infiniteEntropy_hasSum hq0 hq1).summable (paddedGeometric_pointwise q)
    (geometric_entropy_uniformTailControl hq0 hq1)
  have he : (fun n => ∑' k, Real.negMulLog (paddedGeometric q n k)) =
      fun n => entropy (geometricDensity q n) :=
    funext (geometricEntropy_padding q)
  rw [he] at h
  exact h

/-- The geometric reservoir energy satisfies the energy license. -/
theorem geometric_energy_uniformTailControl {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    UniformTailControl (fun n k => padFunction (geometricEnergy r n) k * paddedGeometric q n k) := by
  intro ε hε
  filter_upwards [geometric_uniform_energy_tails hq0 hq1 hr0 hr1 ε hε] with K hK
  intro n
  have hnn := (finiteEnergyTail_bound hq0 hq1 hr0 hr1 n K).1
  change |finiteEnergyTail q r n K| < ε
  rw [abs_of_nonneg hnn]
  exact hK n

theorem paddedEnergy_summable (q r : ℝ) (n : ℕ) :
    Summable (fun k => padFunction (geometricEnergy r n) k * paddedGeometric q n k) :=
  (padVector_weighted_hasSum (geometricWeight q n) (geometricEnergy r n)).summable

/-- Each coordinate of the cutoff energy is eventually the infinite energy coordinate. -/
theorem paddedEnergy_pointwise {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    Filter.Tendsto (fun n => padFunction (geometricEnergy r n) k) Filter.atTop
      (nhds (infiniteEnergy r k)) := by
  apply tendsto_atTop_of_eventually_const (i₀ := k + 1)
  intro n hn
  have hk : k < n := by omega
  rw [padFunction, dif_pos (show k < n + 1 by omega)]
  change geometricEnergy r n (Fin.castSucc ⟨k, hk⟩) = infiniteEnergy r k
  exact geometricEnergy_interior hr0 hr1 n ⟨k, hk⟩

/-- The license derives the infinite mean-energy limit of the actual finite states. -/
theorem geometricMeanEnergy_limit_by_license {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => meanEnergy (geometricHamiltonian r n) (geometricDensity q n))
      Filter.atTop (nhds (infiniteMeanEnergy q r)) := by
  have h := energy_tendsto_of_uniformTailControl (fun n k => paddedGeometric q n k)
    (infiniteWeight q) (fun n k => padFunction (geometricEnergy r n) k) (infiniteEnergy r)
    (paddedEnergy_summable q r) (infiniteMeanEnergy_hasSum hq0 hq1 r).summable
    (paddedGeometric_pointwise q) (paddedEnergy_pointwise hr0 hr1)
    (geometric_energy_uniformTailControl hq0 hq1 hr0 hr1)
  have he : (fun n => ∑' k, padFunction (geometricEnergy r n) k * paddedGeometric q n k) =
      fun n => meanEnergy (geometricHamiltonian r n) (geometricDensity q n) :=
    funext (geometricEnergy_padding q r)
  rw [he] at h
  exact h

/-- The license derives the infinite heat limit of the native swap experiments. -/
theorem geometricHeat_limit_by_license {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => geometricHeat q r n) Filter.atTop (nhds (infiniteHeat q r)) := by
  have hq := geometricMeanEnergy_limit_by_license hq0 hq1 hr0 hr1
  have hr := geometricMeanEnergy_limit_by_license hr0.le hr1 hr0 hr1
  have he : (fun n => geometricHeat q r n) = fun n =>
      meanEnergy (geometricHamiltonian r n) (geometricDensity q n) -
        meanEnergy (geometricHamiltonian r n) (geometricDensity r n) := by
    funext n
    rw [geometricHeat_eq hr0 hr1]
    change _ = meanEnergy (realDiagonal (geometricEnergy r n)) (realDiagonal (geometricWeight q n)) -
      meanEnergy (realDiagonal (geometricEnergy r n)) (realDiagonal (geometricWeight r n))
    rw [meanEnergy_realDiagonal, meanEnergy_realDiagonal]
  rw [he]
  exact hq.sub hr

/-- The logarithmic coordinate states converge pointwise to the pure coordinate state. -/
theorem controlledLogarithmic_pointwise (k : ℕ) :
    Filter.Tendsto (fun n => controlledLogarithmicState n k) Filter.atTop
      (nhds (pureState k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _) _ controlledLogarithmicState_norm_tendsto
  intro n
  have h := lp.norm_apply_le_norm (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
    (controlledLogarithmicState n - pureState) k
  simpa only [lp.coeFn_sub, Pi.sub_apply] using h

theorem pureState_entropy_summable : Summable (fun k => Real.negMulLog (pureState k)) :=
  (padVector_entropy_hasSum (spikeTailWeight 0 0)).summable

theorem controlledLogarithmic_entropy_summable (n : ℕ) :
    Summable (fun k => Real.negMulLog (controlledLogarithmicState n k)) :=
  (padVector_entropy_hasSum (controlledLogarithmicWeight n)).summable

/-- The logarithmic counterexample violates the entropy license. -/
theorem controlledLogarithmic_not_uniformTailControl :
    ¬ UniformTailControl (fun n k => Real.negMulLog (controlledLogarithmicState n k)) := by
  intro h
  have hlim := entropy_tendsto_of_uniformTailControl (fun n k => controlledLogarithmicState n k)
    pureState controlledLogarithmic_entropy_summable pureState_entropy_summable
    controlledLogarithmic_pointwise h
  rw [pureState_entropy] at hlim
  have hbad : (1 : ℝ) = 0 :=
    tendsto_nhds_unique controlledLogarithmicState_entropy_tendsto hlim
  exact one_ne_zero hbad

/-- The thermodynamic limit license holds for the geometric family and fails sharply for
the logarithmic family, whose states nevertheless converge in trace norm. -/
def ThermodynamicLimitLicenseGoal : Prop :=
  (∀ (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ), (∀ n, Summable (f n)) → Summable g →
    (∀ k, Filter.Tendsto (fun n => f n k) Filter.atTop (nhds (g k))) →
    UniformTailControl f →
    Filter.Tendsto (fun n => ∑' k, f n k) Filter.atTop (nhds (∑' k, g k))) ∧
  (∀ q : ℝ, 0 < q → q < 1 →
    UniformTailControl (fun n k => Real.negMulLog (paddedGeometric q n k)) ∧
    Filter.Tendsto (fun n => entropy (geometricDensity q n)) Filter.atTop
      (nhds (infiniteEntropy q))) ∧
  (∀ q r : ℝ, 0 ≤ q → q < 1 → 0 < r → r < 1 →
    UniformTailControl
      (fun n k => padFunction (geometricEnergy r n) k * paddedGeometric q n k) ∧
    Filter.Tendsto (fun n => geometricHeat q r n) Filter.atTop (nhds (infiniteHeat q r))) ∧
  Filter.Tendsto controlledLogarithmicState Filter.atTop (nhds pureState) ∧
  (∀ k, Filter.Tendsto (fun n => controlledLogarithmicState n k) Filter.atTop
    (nhds (pureState k))) ∧
  ¬ UniformTailControl (fun n k => Real.negMulLog (controlledLogarithmicState n k))

theorem thermodynamicLimitLicenseGoal : ThermodynamicLimitLicenseGoal :=
  ⟨tendsto_tsum_of_uniformTailControl,
    fun _ hq0 hq1 => ⟨geometric_entropy_uniformTailControl hq0 hq1,
      geometricEntropy_limit_by_license hq0 hq1⟩,
    fun _ _ hq0 hq1 hr0 hr1 => ⟨geometric_energy_uniformTailControl hq0 hq1 hr0 hr1,
      geometricHeat_limit_by_license hq0 hq1 hr0 hr1⟩,
    controlledLogarithmicState_tendsto, controlledLogarithmic_pointwise,
    controlledLogarithmic_not_uniformTailControl⟩

end

end OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitThermodynamics
