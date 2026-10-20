import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularityQuantum
import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import OperatorKO7.Meta.BoundaryObserver.PairResolution
import OperatorKO7.Meta.ReverseBridge.BinEntropySharpBound
import Mathlib.Tactic

set_option autoImplicit false

/-!
M6-pair first production checkpoint. Exact goal types ported from BoundaryTheoremSpec.lean.
Source reviewer cleared first write under M6R-008. Supervisor runs all compiler and trust checks.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PairQubit

open scoped BigOperators Kronecker ComplexOrder
open OperatorKO7.Meta.BoundaryObserver

noncomputable section

/-- The label test of the pair: plus one at `false`, minus one at `true`. -/
def pairZ : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then -1 else 1)

/-- The invisible transposition of the pair, as a matrix. -/
def pairX : Matrix Bool Bool ℂ := fun i j => if i = j then 0 else 1

/-- The third complementary test of the pair. -/
def pairY : Matrix Bool Bool ℂ := fun i j =>
  if i = j then 0 else if i then Complex.I else -Complex.I

/-- M6.8(i): the label test, the transposition and their product obey the Pauli relations. -/
def PauliRelationsGoal : Prop :=
  pairZ * pairZ = 1 ∧ pairX * pairX = 1 ∧ pairY * pairY = 1 ∧
    pairZ * pairX = -(pairX * pairZ) ∧ pairX * pairY = -(pairY * pairX) ∧
    pairY * pairZ = -(pairZ * pairY) ∧ pairZ * pairX = Complex.I • pairY

/-- M6.8(ii): the four matrices span the whole algebra of the pair. -/
def PairSpanGoal : Prop :=
  ∀ a : Matrix Bool Bool ℂ, ∃ c₀ c₁ c₂ c₃ : ℂ,
    a = c₀ • (1 : Matrix Bool Bool ℂ) + c₁ • pairX + c₂ • pairY + c₃ • pairZ

/-- M6.8(iii): the fiber algebra of a merged pair is the whole matrix algebra of the pair. -/
def PairFiberAlgebraGoal : Prop :=
  ∀ a : BoundaryReconstruction.Mat 2, a ∈ BoundaryReconstruction.fiberAlgebra (fun _ : Fin 2 => ())

/-- The pure state `(|00⟩ + |11⟩) / √2` of two pairs, as a density matrix. -/
def bellState : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 / 2 else 0

/-- M6.10(iii): the fair pair is half of a pure state of two pairs. -/
def QuantumPurificationGoal : Prop :=
  BoundaryReconstruction.Thermal.marginalLeft bellState = BoundarySingularity.Thermal.fairPair ∧
    bellState * bellState = bellState ∧ bellState.trace = 1

/-- The real dimension of the space of unnormalized Hermitian N-by-N matrices over a
division algebra of real dimension d, with no trace-one condition. -/
def fieldStateDimension (d N : ℕ) : ℕ := N + d * (N * (N - 1) / 2)

/-- M6.10(vii): the composite dimension of two pairs equals the product of the pair dimensions for
d = 2 alone among d = 1, 2, 4. -/
def FieldDimensionGoal : Prop :=
  fieldStateDimension 1 4 ≠ fieldStateDimension 1 2 ^ 2 ∧
    fieldStateDimension 2 4 = fieldStateDimension 2 2 ^ 2 ∧
    fieldStateDimension 4 4 ≠ fieldStateDimension 4 2 ^ 2

/-! Checkpoint proof bodies; direct finite matrix equations, no assumed fields. -/

theorem pauli_relations : PauliRelationsGoal := by
  unfold PauliRelationsGoal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j
     cases i <;> cases j <;>
       norm_num [pairZ, pairX, pairY, Matrix.mul_apply, Fintype.sum_bool,
         Complex.I_mul_I, Complex.I_sq, Matrix.one_apply])

theorem pair_span : PairSpanGoal := by
  intro a
  refine ⟨(a false false + a true true) / 2,
    (a false true + a true false) / 2,
    Complex.I * (a false true - a true false) / 2,
    (a false false - a true true) / 2, ?_⟩
  ext i j
  cases i <;> cases j <;>
    simp [pairZ, pairX, pairY, Matrix.add_apply, Matrix.smul_apply] <;>
      ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem pair_fiber_algebra : PairFiberAlgebraGoal := by
  intro a
  change BoundaryReconstruction.FiberClosed (fun _ : Fin 2 => ()) a
  intro i j h
  exact (h rfl).elim

theorem quantum_purification : QuantumPurificationGoal := by
  unfold QuantumPurificationGoal
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    cases i <;> cases j <;>
      norm_num [bellState, BoundaryReconstruction.Thermal.marginalLeft,
        BoundarySingularity.Thermal.fairPair, BoundaryReconstruction.Thermal.realDiagonal,
        Fintype.sum_bool]
  · ext i j
    rcases i with ⟨a, b⟩
    rcases j with ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [bellState, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  · norm_num [bellState, Matrix.trace, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The Bell density matrix is positive semidefinite, independently of the purification clauses. -/
theorem bell_state_posSemidef : bellState.PosSemidef := by
  let s : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
  have hReal : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
    rw [← pow_two]
    exact Real.sq_sqrt (by norm_num)
  have hs : s * s = (1 / 2 : ℂ) := by
    change ((Real.sqrt (1 / 2 : ℝ) : ℂ) *
      (Real.sqrt (1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ)
    rw [← Complex.ofReal_mul, hReal]; norm_num
  have hstar : star s = s := by
    simp [s]
  have hstarRing : (starRingEnd ℂ) s = s := by
    simpa only [starRingEnd_apply] using hstar
  let V : Matrix (Bool × Bool) Bool ℂ := fun x k =>
    if k = false ∧ x.1 = x.2 then s else 0
  have hGram : bellState = V * Matrix.conjTranspose V := by
    ext x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [bellState, V, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_bool, hstarRing, hs]
  rw [hGram]
  exact Matrix.posSemidef_self_mul_conjTranspose V

theorem field_dimension : FieldDimensionGoal := by
  norm_num [FieldDimensionGoal, fieldStateDimension]


/-! ## M6.9: the dynamics clause, record projectors and invisible operations -/

/-- The projector onto the fiber of one record value. -/
def recordProjector {n : ℕ} {Q : Type} [DecidableEq Q] (q : Fin n → Q) (y : Q) :
    BoundaryReconstruction.Mat n :=
  Matrix.diagonal (fun i => if q i = y then 1 else 0)

/-- M6.9(i): a generator lies in the fiber algebra if and only if it commutes with every record
projector. -/
def GeneratorNoetherGoal : Prop :=
  ∀ (n : ℕ) (Q : Type) [DecidableEq Q] (q : Fin n → Q) (H : BoundaryReconstruction.Mat n),
    BoundaryReconstruction.FiberClosed q H ↔
      ∀ y, H * recordProjector q y = recordProjector q y * H

/-- G28. Fiber closure is the commutant of the record projectors. -/
theorem generatorNoetherGoal : GeneratorNoetherGoal := by
  intro n Q _ q H
  constructor
  · intro hH y
    ext i j
    unfold recordProjector
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : q i = q j
    · rw [hij]
      exact mul_comm _ _
    · rw [hH i j hij, zero_mul, mul_zero]
  · intro hc i j hij
    have h := congrFun (congrFun (hc (q j)) i) j
    unfold recordProjector at h
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, if_pos rfl, if_neg hij, mul_one,
      zero_mul] at h
    exact h

/-- M6.9(iii): a permutation matrix lies in the fiber algebra if and only if its permutation is
invisible to the observer. -/
def InvisiblePermutationGoal : Prop :=
  ∀ (n : ℕ) (Q : Type) (q : Fin n → Q) (s : Equiv.Perm (Fin n)),
    BoundaryReconstruction.FiberClosed q (BoundaryReconstruction.permutationMat s) ↔
      ∀ i, q (s i) = q i

/-- G30. A permutation matrix is fiber closed exactly when the permutation keeps every record. -/
theorem invisiblePermutationGoal : InvisiblePermutationGoal := by
  intro n Q q s
  constructor
  · intro hs i
    by_contra hne
    have h := hs (s i) i hne
    change (if s i = s i then (1 : ℂ) else 0) = 0 at h
    rw [if_pos rfl] at h
    exact one_ne_zero h
  · intro hs
    exact BoundaryReconstruction.fiberClosed_permutation s hs

/-- M6.9(iv): the fiber-adapted orthonormal frames form one free orbit of the invisible
unitaries, the quantum form of the place-coordinate orbit. -/
def FrameOrbitGoal : Prop :=
  ∀ (n : ℕ) (Q : Type) (q : Fin n → Q) (u v : Matrix.unitaryGroup (Fin n) ℂ),
    BoundaryReconstruction.FiberClosed q (u : BoundaryReconstruction.Mat n) →
    BoundaryReconstruction.FiberClosed q (v : BoundaryReconstruction.Mat n) →
      ∃ w : Matrix.unitaryGroup (Fin n) ℂ,
        BoundaryReconstruction.FiberClosed q (w : BoundaryReconstruction.Mat n) ∧ v = w * u ∧
          ∀ w' : Matrix.unitaryGroup (Fin n) ℂ, v = w' * u → w' = w

/-- G31. Two fiber-closed unitaries differ by exactly one fiber-closed unitary. -/
theorem frameOrbitGoal : FrameOrbitGoal := by
  intro n Q q u v hu hv
  refine ⟨v * u⁻¹, ?_, (inv_mul_cancel_right v u).symm,
    fun w' hw' => eq_mul_inv_of_mul_eq hw'.symm⟩
  have hinv : ((u⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : BoundaryReconstruction.Mat n) =
      BoundaryReconstruction.dagger (u : BoundaryReconstruction.Mat n) := by
    rw [← unitary.star_eq_inv]
    rfl
  have hcoe : ((v * u⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : BoundaryReconstruction.Mat n) =
      (v : BoundaryReconstruction.Mat n) *
        ((u⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : BoundaryReconstruction.Mat n) := rfl
  rw [hcoe, hinv]
  exact BoundaryReconstruction.fiberClosed_mul hv (BoundaryReconstruction.fiberClosed_adjoint hu)

/-- M6.9(ii): a unitary keeps the statistics of every record reading on every state if and only
if it lies in the fiber algebra. -/
def UnitaryNoetherGoal : Prop :=
  ∀ (n : ℕ) (Q : Type) [DecidableEq Q] (q : Fin n → Q) (u : Matrix.unitaryGroup (Fin n) ℂ),
    (∀ ρ : BoundaryReconstruction.Mat n, ρ.PosSemidef → ρ.trace = 1 → ∀ y,
      ((u : BoundaryReconstruction.Mat n) * ρ * star (u : BoundaryReconstruction.Mat n) *
          recordProjector q y).trace = (ρ * recordProjector q y).trace) ↔
      BoundaryReconstruction.FiberClosed q (u : BoundaryReconstruction.Mat n)

/-- G29. A unitary keeps the law of every record reading on every state exactly when it is
fiber closed. The forward direction tests the coordinate states: the weight of column j of u
on the fiber of another record is then zero. -/
theorem unitaryNoetherGoal : UnitaryNoetherGoal := by
  classical
  intro n Q _ q u
  constructor
  · intro h i j hij
    let d : Fin n → ℂ := fun l => if l = j then 1 else 0
    have hd0 : 0 ≤ d := by
      intro l
      change (0 : ℂ) ≤ if l = j then 1 else 0
      split_ifs
      · exact zero_le_one
      · exact le_refl 0
    have hpsd : (Matrix.diagonal d).PosSemidef := Matrix.PosSemidef.diagonal hd0
    have htr1 : (Matrix.diagonal d).trace = 1 := by
      rw [Matrix.trace_diagonal]
      simp [d]
    have hy := h (Matrix.diagonal d) hpsd htr1 (q i)
    have hR : (Matrix.diagonal d * recordProjector q (q i)).trace = 0 := by
      unfold recordProjector
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x = j
      · rw [hx]
        simp [d, Ne.symm hij]
      · simp [d, hx]
    have hL : ((u : BoundaryReconstruction.Mat n) * Matrix.diagonal d *
        star (u : BoundaryReconstruction.Mat n) * recordProjector q (q i)).trace =
        ((∑ k, Complex.normSq ((u : BoundaryReconstruction.Mat n) k j) *
          (if q k = q i then 1 else 0) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      unfold recordProjector
      rw [Matrix.trace]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
      simp only [Matrix.mul_diagonal, Matrix.star_apply]
      rw [Finset.sum_eq_single j]
      · by_cases hk : q k = q i
        · simp [hk, d, Complex.mul_conj]
        · simp [hk, d]
      · intro l _ hl
        simp [d, hl]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hL, hR] at hy
    have hsum := Complex.ofReal_eq_zero.mp hy
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg
      (Complex.normSq_nonneg _) (by split_ifs <;> norm_num))).mp hsum i (Finset.mem_univ i)
    rw [if_pos rfl, mul_one] at hterm
    exact Complex.normSq_eq_zero.mp hterm
  · intro hu ρ _ _ y
    have hc := (generatorNoetherGoal n Q q (u : BoundaryReconstruction.Mat n)).mp hu y
    have hsu : star (u : BoundaryReconstruction.Mat n) * (u : BoundaryReconstruction.Mat n) = 1 :=
      unitary.star_mul_self_of_mem u.2
    calc ((u : BoundaryReconstruction.Mat n) * ρ * star (u : BoundaryReconstruction.Mat n) *
          recordProjector q y).trace =
        ((star (u : BoundaryReconstruction.Mat n) * recordProjector q y) *
          ((u : BoundaryReconstruction.Mat n) * ρ)).trace := by
          rw [Matrix.mul_assoc ((u : BoundaryReconstruction.Mat n) * ρ), Matrix.trace_mul_comm]
      _ = (ρ * (star (u : BoundaryReconstruction.Mat n) * recordProjector q y *
          (u : BoundaryReconstruction.Mat n))).trace := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = (ρ * recordProjector q y).trace := by
          rw [Matrix.mul_assoc (star (u : BoundaryReconstruction.Mat n)), ← hc,
            ← Matrix.mul_assoc (star (u : BoundaryReconstruction.Mat n))
              (u : BoundaryReconstruction.Mat n), hsu, Matrix.one_mul]

/-! ## M6.12: the quantum form of the pole -/

/-- The trace of a positive semidefinite matrix has nonnegative real part. -/
private theorem trace_re_nonneg {m : Type} [Fintype m] [DecidableEq m] {M : Matrix m m ℂ}
    (hM : M.PosSemidef) : 0 ≤ M.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  have h := hM.re_dotProduct_nonneg (Pi.single i 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

/-- A positive test and a density give a nonnegative probability. -/
private theorem trace_mul_re_nonneg {m : Type} [Fintype m] [DecidableEq m]
    {ρ E : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef) : 0 ≤ (ρ * E).trace.re := by
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hE
  have hcyc : (ρ * E).trace = (B * ρ * B.conjTranspose).trace := by
    rw [hB, ← Matrix.mul_assoc, Matrix.trace_mul_comm (ρ * B.conjTranspose) B, Matrix.mul_assoc]
  rw [hcyc]
  exact trace_re_nonneg (hρ.mul_mul_conjTranspose_same B)

open ProtocolResolution in
/-- M6.12(i): a measurement turns two states of the pair into two rows to which M6.2 applies. -/
def MeasuredRowsGoal : Prop :=
  ∀ (Y : Type) [Fintype Y] (E : Y → Matrix Bool Bool ℂ) (ρ₀ ρ₁ : Matrix Bool Bool ℂ),
    (∀ y, (E y).PosSemidef) → ∑ y, E y = 1 → ρ₀.PosSemidef → ρ₁.PosSemidef →
    ρ₀.trace = 1 → ρ₁.trace = 1 →
      ∃ P Q : FiniteLaw Y, (∀ y, P.mass y = (ρ₀ * E y).trace.re) ∧
        ∀ y, Q.mass y = (ρ₁ * E y).trace.re

/-- G43. The Born rows of two densities under one positive measurement are finite laws. -/
theorem measuredRowsGoal : MeasuredRowsGoal := by
  intro Y _ E ρ₀ ρ₁ hE hsum h₀ h₁ t₀ t₁
  have hrow : ∀ ρ : Matrix Bool Bool ℂ, ρ.PosSemidef → ρ.trace = 1 →
      ∃ P : ProtocolResolution.FiniteLaw Y, ∀ y, P.mass y = (ρ * E y).trace.re := by
    intro ρ hρ ht
    refine ⟨{ mass := fun y => (ρ * E y).trace.re
              nonnegative := fun y => trace_mul_re_nonneg hρ (hE y)
              total := ?_ }, fun y => rfl⟩
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, hsum, Matrix.mul_one, ht,
      Complex.one_re]
  obtain ⟨P, hP⟩ := hrow ρ₀ h₀ t₀
  obtain ⟨Q, hQ⟩ := hrow ρ₁ h₁ t₁
  exact ⟨P, Q, hP, hQ⟩

/-- M6.12(ii): measurements built from record projectors cannot tell apart two states with one
record law. -/
def QuantumRecordPoleGoal : Prop :=
  ∀ (n : ℕ) (Q Y : Type) [DecidableEq Q] (q : Fin n → Q)
    (E : Y → BoundaryReconstruction.Mat n) (c : Y → Q → ℂ) (ρ₀ ρ₁ : BoundaryReconstruction.Mat n),
    (∀ y, E y = ∑ r ∈ Finset.univ.image q, c y r • recordProjector q r) →
    (∀ r, (ρ₀ * recordProjector q r).trace = (ρ₁ * recordProjector q r).trace) →
      ∀ y, (ρ₀ * E y).trace = (ρ₁ * E y).trace

/-- G44. Record-linear tests give equal traces on states with equal record traces. -/
theorem quantumRecordPoleGoal : QuantumRecordPoleGoal := by
  intro n Q Y _ q E c ρ₀ ρ₁ hE hρ y
  rw [hE y, Matrix.mul_sum, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, hρ r]

/-! ## M6.8: the bit of the pair across its three complementary readings -/

/-- The determinant of a matrix on the two labels. -/
private theorem qubit_det (ρ : Matrix Bool Bool ℂ) :
    ρ.det = ρ false false * ρ true true - ρ false true * ρ true false := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm ρ, Matrix.det_fin_two]
  simp [finTwoEquiv]

/-- Real coordinates of a density of the pair, with the positivity inequality. -/
private theorem qubit_coords (ρ : Matrix Bool Bool ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (ρ * pairX).trace = ρ false true + ρ true false ∧
    (ρ * pairY).trace = Complex.I * ρ false true - Complex.I * ρ true false ∧
    (ρ * pairZ).trace = ρ false false - ρ true true ∧
    (ρ * ρ).trace = ρ false false * ρ false false + ρ false true * ρ true false +
      (ρ true false * ρ false true + ρ true true * ρ true true) ∧
    ρ true false = star (ρ false true) ∧
    (ρ false false).im = 0 ∧ (ρ true true).im = 0 ∧
    (ρ false false).re + (ρ true true).re = 1 ∧
    (ρ false true).re ^ 2 + (ρ false true).im ^ 2 ≤ (ρ false false).re * (ρ true true).re := by
  have hH := hρ.1
  have h10 : ρ true false = star (ρ false true) := (hH.apply true false).symm
  have ha : (ρ false false).im = 0 := by
    have h := congrArg Complex.im (hH.apply false false)
    rw [Complex.star_def, Complex.conj_im] at h
    linarith
  have hd : (ρ true true).im = 0 := by
    have h := congrArg Complex.im (hH.apply true true)
    rw [Complex.star_def, Complex.conj_im] at h
    linarith
  have htr' : (ρ false false).re + (ρ true true).re = 1 := by
    have h := congrArg Complex.re htr
    simp [Matrix.trace] at h
    linarith
  have hdet : (ρ false true).re ^ 2 + (ρ false true).im ^ 2 ≤
      (ρ false false).re * (ρ true true).re := by
    have h0 := (Complex.nonneg_iff.mp hρ.det_nonneg).1
    rw [qubit_det, h10] at h0
    simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, ha, hd] at h0
    nlinarith [h0]
  refine ⟨?_, ?_, ?_, ?_, h10, ha, hd, htr', hdet⟩
  · simp [Matrix.trace, Matrix.mul_apply, pairX]
    ring
  · simp [Matrix.trace, Matrix.mul_apply, pairY]
    ring
  · simp [Matrix.trace, Matrix.mul_apply, pairZ]
    ring
  · simp [Matrix.trace, Matrix.mul_apply]
    ring

/-- M6.8(iv): the bit of the pair is conserved across its three complementary readings. -/
def BitConservationGoal : Prop :=
  ∀ ρ : Matrix Bool Bool ℂ, ρ.PosSemidef → ρ.trace = 1 →
    (ρ * pairX).trace.re ^ 2 + (ρ * pairY).trace.re ^ 2 + (ρ * pairZ).trace.re ^ 2 =
        2 * (ρ * ρ).trace.re - 1 ∧ 2 * (ρ * ρ).trace.re - 1 ≤ 1

/-- M6.8(v): the information the three readings take from the pair adds to at most one bit. -/
def ComplementaryBitsGoal : Prop :=
  ∀ ρ : Matrix Bool Bool ℂ, ρ.PosSemidef → ρ.trace = 1 →
    (1 - Real.binEntropy ((1 + (ρ * pairX).trace.re) / 2) / Real.log 2) +
      (1 - Real.binEntropy ((1 + (ρ * pairY).trace.re) / 2) / Real.log 2) +
      (1 - Real.binEntropy ((1 + (ρ * pairZ).trace.re) / 2) / Real.log 2) ≤ 1

/-- M6.8(vi): a state with a definite place has mean zero under the two other readings. -/
def ComplementaryLawGoal : Prop :=
  ∀ ρ : Matrix Bool Bool ℂ, ρ.PosSemidef → ρ.trace = 1 →
    ((ρ * pairZ).trace.re = 1 ∨ (ρ * pairZ).trace.re = -1) →
      (ρ * pairX).trace = 0 ∧ (ρ * pairY).trace = 0


/-- G25. The three Bloch coordinates square to twice the purity minus one, at most one. -/
theorem bitConservationGoal : BitConservationGoal := by
  intro ρ hρ htr
  obtain ⟨tX, tY, tZ, tρ, h10, ha, hd, htr', hdet⟩ := qubit_coords ρ hρ htr
  rw [tX, tY, tZ, tρ, h10]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, ha, hd]
  have hsq : ((ρ false false).re + (ρ true true).re) ^ 2 = 1 := by
    rw [htr']
    norm_num
  constructor
  · linear_combination (-((ρ false false).re + (ρ true true).re + 1)) * htr'
  · nlinarith [hdet, hsq]

/-- G26. The three entropy deficits of the complementary readings add to at most one bit. -/
theorem complementaryBitsGoal : ComplementaryBitsGoal := by
  intro ρ hρ htr
  obtain ⟨hid, hle⟩ := bitConservationGoal ρ hρ htr
  generalize (ρ * pairX).trace.re = rX at hid hle ⊢
  generalize (ρ * pairY).trace.re = rY at hid hle ⊢
  generalize (ρ * pairZ).trace.re = rZ at hid hle ⊢
  have hsum : rX ^ 2 + rY ^ 2 + rZ ^ 2 ≤ 1 := by linarith
  have hX : |rX| ≤ 1 :=
    (sq_le_one_iff_abs_le_one rX).mp (by nlinarith [sq_nonneg rY, sq_nonneg rZ])
  have hY : |rY| ≤ 1 :=
    (sq_le_one_iff_abs_le_one rY).mp (by nlinarith [sq_nonneg rX, sq_nonneg rZ])
  have hZ : |rZ| ≤ 1 :=
    (sq_le_one_iff_abs_le_one rZ).mp (by nlinarith [sq_nonneg rX, sq_nonneg rY])
  have bX := FourTestTables.one_sub_binEntropy_le_sq rX hX
  have bY := FourTestTables.one_sub_binEntropy_le_sq rY hY
  have bZ := FourTestTables.one_sub_binEntropy_le_sq rZ hZ
  linarith

/-- G27. A state with a definite label has zero complex mean under the two other readings. -/
theorem complementaryLawGoal : ComplementaryLawGoal := by
  intro ρ hρ htr hz
  obtain ⟨tX, tY, _tZ, _tρ, h10, _ha, _hd, _htr', _hdet⟩ := qubit_coords ρ hρ htr
  obtain ⟨hid, hle⟩ := bitConservationGoal ρ hρ htr
  have hZ2 : (ρ * pairZ).trace.re ^ 2 = 1 := by
    rcases hz with h | h <;> rw [h] <;> norm_num
  have hX2 : (ρ * pairX).trace.re ^ 2 = 0 := by
    nlinarith [sq_nonneg (ρ * pairX).trace.re, sq_nonneg (ρ * pairY).trace.re]
  have hY2 : (ρ * pairY).trace.re ^ 2 = 0 := by
    nlinarith [sq_nonneg (ρ * pairX).trace.re, sq_nonneg (ρ * pairY).trace.re]
  have hX0 := (pow_eq_zero_iff two_ne_zero).mp hX2
  have hY0 := (pow_eq_zero_iff two_ne_zero).mp hY2
  have hre : (ρ false true).re = 0 := by
    rw [tX, h10, Complex.add_re, Complex.star_def, Complex.conj_re] at hX0
    linarith
  have him : (ρ false true).im = 0 := by
    rw [tY, h10, Complex.sub_re, Complex.mul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im] at hY0
    linarith
  have hz0 : ρ false true = 0 := Complex.ext (by simpa using hre) (by simpa using him)
  constructor
  · rw [tX, h10, hz0, star_zero, add_zero]
  · rw [tY, h10, hz0, star_zero, mul_zero, sub_zero]

/-- Sharp X/Z entropic uncertainty for every actual positive trace-one qubit matrix.
The two probabilities are the Pauli positive-outcome Born probabilities. -/
theorem complementary_entropy_sharp (ρ : Matrix Bool Bool ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    Real.log 2 ≤
      Real.binEntropy ((1 + (ρ * pairX).trace.re) / 2) +
      Real.binEntropy ((1 + (ρ * pairZ).trace.re) / 2) := by
  obtain ⟨hid, hle⟩ := bitConservationGoal ρ hρ htr
  apply OperatorKO7.Meta.ReverseBridge.BinEntropySharpBound.bloch_entropic_floor_sharp
  nlinarith [sq_nonneg (ρ * pairY).trace.re]

/-- A positive trace-one Pauli eigenstate attains the sharp entropy floor. -/
theorem complementary_entropy_sharp_attained :
    let ρ : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then 0 else 1)
    ρ.PosSemidef ∧ ρ.trace = 1 ∧
      Real.binEntropy ((1 + (ρ * pairX).trace.re) / 2) +
        Real.binEntropy ((1 + (ρ * pairZ).trace.re) / 2) = Real.log 2 := by
  dsimp only
  refine ⟨Matrix.PosSemidef.diagonal ?_, ?_, ?_⟩
  · intro b
    cases b <;> norm_num
  · norm_num [Matrix.trace, Fintype.sum_bool]
  · simp [pairX, pairZ, Matrix.trace, Matrix.mul_apply]

#check @complementary_entropy_sharp
#print axioms complementary_entropy_sharp
#check @complementary_entropy_sharp_attained
#print axioms complementary_entropy_sharp_attained


end
end OperatorKO7.Meta.BoundaryObserver.PairQubit
