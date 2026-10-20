import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
import OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation
import OperatorKO7.QEC.Codes.KnillLaflamme

/-!
# M5.5 finite recorded Kraus realization

Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, M5_5.
Author: bt-m55. Compiler owner: claude-two-voids.
LASOT 2.3 read in full from OperatorKO7/LEAN_AGENT_AUDIT_SOURCE_OF_TRUTH.md.
Status: source candidate, not kernel validated.

The record is an explicit output index of the column-stacked Kraus isometry.
The selective matrix equality is valid for every matrix input and every record label.
The nonselective matrix equality discards precisely that index.
Abstract complete positivity to Kraus representation and Knill-Laflamme
recovery equivalence remain separate open M5.5 obligations.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators Classical ComplexOrder

namespace OperatorKO7.Meta.BoundaryObserver.ReconstructionRecovery

open OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation

/-- A retained record label selects its block from the enlarged output matrix. -/
def recordedOutcome {m : ℕ} {E : Type*} (e : E)
    (M : Matrix (Fin m × E) (Fin m × E) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => M (i, e) (j, e)

/-- Each recorded block of the Kraus isometry gives the matching selective operation. -/
theorem recordedOutcome_stinespring {n m : ℕ} {E : Type*} [Fintype E]
    (K : E → Matrix (Fin m) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ)
    (e : E) :
    recordedOutcome e (stinespringV K * ρ * (stinespringV K)ᴴ) =
      K e * ρ * (K e)ᴴ := by
  ext i j
  simp only [recordedOutcome, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, stinespringV_apply]

/-- Discarding the label sums every recorded block, with no outcome omitted. -/
theorem recordedOutcome_sum {m : ℕ} {E : Type*} [Fintype E]
    (M : Matrix (Fin m × E) (Fin m × E) ℂ) :
    (∑ e : E, recordedOutcome e M) = partialTraceAncilla M := by
  ext i j
  simp only [Matrix.sum_apply, recordedOutcome, partialTraceAncilla, Matrix.of_apply]

/-- Selective Kraus operations preserve positive semidefiniteness. -/
theorem recordedOutcome_posSemidef {n m : ℕ} {E : Type*} [Fintype E]
    (K : E → Matrix (Fin m) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.PosSemidef) (e : E) :
    (recordedOutcome e (stinespringV K * ρ * (stinespringV K)ᴴ)).PosSemidef := by
  rw [recordedOutcome_stinespring]
  exact hρ.mul_mul_conjTranspose_same (K e)

/-- Every trace-preserving finite Kraus instrument has one common isometric
dilation, exact selective outcome matrices and the exact nonselective channel. -/
theorem kraus_instrument_record_realization {n m : ℕ} {E : Type*} [Fintype E]
    (K : E → Matrix (Fin m) (Fin n) ℂ)
    (hTP : (∑ e : E, (K e)ᴴ * K e : Matrix (Fin n) (Fin n) ℂ) = 1) :
    ∃ V : Matrix (Fin m × E) (Fin n) ℂ,
      Vᴴ * V = 1 ∧
      (∀ (ρ : Matrix (Fin n) (Fin n) ℂ) (e : E),
        recordedOutcome e (V * ρ * Vᴴ) = K e * ρ * (K e)ᴴ) ∧
      ∀ ρ : Matrix (Fin n) (Fin n) ℂ,
        (∑ e : E, recordedOutcome e (V * ρ * Vᴴ)) = cpMapKraus K ρ := by
  refine ⟨stinespringV K, stinespring_isometry K hTP, ?_, ?_⟩
  · intro ρ e
    exact recordedOutcome_stinespring K ρ e
  · intro ρ
    calc
      (∑ e : E, recordedOutcome e
          (stinespringV K * ρ * (stinespringV K)ᴴ)) =
          partialTraceAncilla (stinespringV K * ρ * (stinespringV K)ᴴ) :=
        recordedOutcome_sum _
      _ = cpMapKraus K ρ := (stinespring_dilates K ρ).symm

/-- The Choi matrix fixes the input matrix-unit and output-entry convention. -/
def choiMatrix {n m : ℕ}
    (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Matrix.of fun p q => f (Matrix.single p.1 q.1 (1 : ℂ)) p.2 q.2

/-- Every matrix entry of a complex-linear operation is reconstructed from
the Choi coefficients, without a positivity or trace assumption. -/
theorem linearMap_entry_via_choi {n m : ℕ}
    (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) (r s : Fin m) :
    f a r s = ∑ i : Fin n, ∑ j : Fin n,
      a i j * choiMatrix f (i, r) (j, s) := by
  have hsingle (i j : Fin n) :
      Matrix.single i j (a i j) =
        a i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single]
    simp only [smul_eq_mul, mul_one]
  calc
    f a r s =
        f (∑ i : Fin n, ∑ j : Fin n, Matrix.single i j (a i j)) r s :=
      congrArg (fun b : Matrix (Fin n) (Fin n) ℂ => f b r s)
        (Matrix.matrix_eq_sum_single a)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        a i j * choiMatrix f (i, r) (j, s) := by
      simp only [hsingle, map_sum, map_smul, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, choiMatrix, Matrix.of_apply]

/-- Equality of Choi matrices implies equality of the complete linear maps. -/
theorem choiMatrix_injective {n m : ℕ} :
    Function.Injective
      (choiMatrix (n := n) (m := m)) := by
  intro f g h
  apply LinearMap.ext
  intro a
  ext r s
  calc
    f a r s = ∑ i : Fin n, ∑ j : Fin n,
        a i j * choiMatrix f (i, r) (j, s) :=
      linearMap_entry_via_choi f a r s
    _ = ∑ i : Fin n, ∑ j : Fin n,
        a i j * choiMatrix g (i, r) (j, s) := by rw [h]
    _ = g a r s := (linearMap_entry_via_choi g a r s).symm

/-- The exact finite matrix carrier from the reconstruction specification. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The exact trace notation from the reconstruction specification. -/
abbrev tr {n : ℕ} (a : Mat n) : ℂ := a.trace

/-- The exact dagger notation from the reconstruction specification. -/
abbrev dagger {n : ℕ} (a : Mat n) : Mat n := a.conjTranspose

/-- The specification's ancillary amplification uses the same input matrix
for every source and output coordinate. -/
noncomputable def amplify {n m : ℕ} (f : Mat n →ₗ[ℂ] Mat m) (r : ℕ)
    (a : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    Matrix (Fin r × Fin m) (Fin r × Fin m) ℂ :=
  fun i j => f (fun x y => a (i.1,x) (j.1,y)) i.2 j.2

/-- The specification's complex positive-semidefinite matrix predicate. -/
def GeneralPSD {I : Type} [Fintype I] (a : Matrix I I ℂ) : Prop :=
  (∀ i j, a i j = star (a j i)) ∧
  ∀ v : I → ℂ, 0 ≤ (∑ i, ∑ j, star (v i) * a i j * v j).re

/-- Ancillary positivity is required for every finite ancillary carrier. -/
def CompletelyPositive {n m : ℕ} (f : Mat n →ₗ[ℂ] Mat m) : Prop :=
  ∀ (r : ℕ) (a : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ),
    GeneralPSD a → GeneralPSD (amplify f r a)

/-- The double-sum convention is the native Hermitian quadratic form. -/
private theorem generalPSD_form_eq {I : Type} [Fintype I]
    (a : Matrix I I ℂ) (v : I → ℂ) :
    (∑ i, ∑ j, star (v i) * a i j * v j) =
      star v ⬝ᵥ (a *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, mul_assoc]

/-- A Hermitian matrix has a real-valued quadratic form. -/
private theorem generalPSD_hermitian_im_zero {I : Type} [Fintype I]
    {a : Matrix I I ℂ} (ha : a.IsHermitian) (v : I → ℂ) :
    (star v ⬝ᵥ (a *ᵥ v)).im = 0 := by
  have h : star (star v ⬝ᵥ (a *ᵥ v)) = star v ⬝ᵥ (a *ᵥ v) := by
    rw [← Matrix.star_dotProduct (a *ᵥ v) v, Matrix.star_mulVec,
      ha.eq, ← Matrix.dotProduct_mulVec]
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- The planning specification's quadratic-form positivity agrees with
native matrix positivity for every finite index type. -/
theorem generalPSD_iff_posSemidef {I : Type} [Fintype I]
    (a : Matrix I I ℂ) : GeneralPSD a ↔ a.PosSemidef := by
  constructor
  · rintro ⟨hh, hp⟩
    have hherm : a.IsHermitian := by
      change aᴴ = a
      ext i j
      change star (a j i) = a i j
      exact (hh i j).symm
    refine ⟨hherm, ?_⟩
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (generalPSD_hermitian_im_zero hherm v).symm⟩
    rw [← generalPSD_form_eq a v]
    exact hp v
  · intro ha
    refine ⟨?_, ?_⟩
    · intro i j
      exact (congrArg (fun b : Matrix I I ℂ => b i j) ha.1.eq).symm
    · intro v
      rw [generalPSD_form_eq a v]
      exact (Complex.nonneg_iff.mp (ha.2 v)).1

/-- The unnormalized maximally entangled vector is placed in a one-column matrix. -/
def entangledColumn {n : ℕ} : Matrix (Fin n × Fin n) (Fin 1) ℂ :=
  Matrix.of fun p _ => if p.1 = p.2 then 1 else 0

/-- Its rank-one Gram matrix is an actual positive ancillary input. -/
def entangledProjector {n : ℕ} :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  entangledColumn * entangledColumnᴴ

/-- The matrix entries pick out the two input indices of one matrix unit. -/
theorem entangledProjector_apply {n : ℕ} (i x j y : Fin n) :
    entangledProjector (i,x) (j,y) =
      if i = x ∧ j = y then (1 : ℂ) else 0 := by
  simp only [entangledProjector, Matrix.mul_apply, Fin.sum_univ_one,
    entangledColumn, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hix : i = x <;> by_cases hjy : j = y <;>
    simp [hix, hjy]

/-- Ancillary amplification of the entangled rank-one matrix is exactly
the Choi matrix, with the same input/output coordinate convention. -/
theorem amplify_entangled_eq_choi {n m : ℕ}
    (f : Mat n →ₗ[ℂ] Mat m) :
    amplify f n (entangledProjector (n := n)) = choiMatrix f := by
  ext ⟨i,r⟩ ⟨j,s⟩
  change f (fun x y => entangledProjector (i,x) (j,y)) r s =
      f (Matrix.single i j (1 : ℂ)) r s
  have hmatrix :
      (fun x y : Fin n => entangledProjector (i,x) (j,y)) =
        Matrix.single i j (1 : ℂ) := by
    ext x y
    rw [entangledProjector_apply]
    rfl
  rw [hmatrix]

/-- The exact ancillary-complete-positivity definition forces positivity
of the Choi matrix for every finite complex-linear operation. -/
theorem completelyPositive_choi_posSemidef {n m : ℕ}
    (f : Mat n →ₗ[ℂ] Mat m) (hf : CompletelyPositive f) :
    (choiMatrix f).PosSemidef := by
  have hinput : GeneralPSD (entangledProjector (n := n)) := by
    apply (generalPSD_iff_posSemidef _).2
    exact Matrix.posSemidef_self_mul_conjTranspose entangledColumn
  have houtput := hf n (entangledProjector (n := n)) hinput
  rw [amplify_entangled_eq_choi] at houtput
  exact (generalPSD_iff_posSemidef _).1 houtput

/-- The positive Choi matrix therefore has an actual finite Gram factor. -/
theorem completelyPositive_choi_gram {n m : ℕ}
    (f : Mat n →ₗ[ℂ] Mat m) (hf : CompletelyPositive f) :
    ∃ B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
      choiMatrix f = Bᴴ * B := by
  exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp
    (completelyPositive_choi_posSemidef f hf)

/-- Each row of a Choi Gram factor is reshaped into a Kraus operator.
The adjoint orientation agrees with the Choi convention used above. -/
def gramKraus {n m : ℕ}
    (B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (Fin n × Fin m) → Matrix (Fin m) (Fin n) ℂ :=
  fun e => Matrix.of fun r i => star (B e (i, r))

/-- Each entry of a finite Choi Gram matrix is a sum of Kraus coefficients. -/
theorem gramKraus_coeff {n m : ℕ}
    (B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
    (i j : Fin n) (r s : Fin m) :
    (Bᴴ * B) (i, r) (j, s) =
      ∑ e : Fin n × Fin m, gramKraus B e r i * star (gramKraus B e s j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, gramKraus,
    Matrix.of_apply, star_star]

/-- The all-input Kraus formula has the same four-index coefficient expansion
as the Choi reconstruction. No positivity or trace premise enters this identity. -/
theorem kraus_entry_by_choi {n m : ℕ} {E : Type*} [Fintype E]
    (K : E → Matrix (Fin m) (Fin n) ℂ)
    (a : Mat n) (r s : Fin m) :
    (cpMapKraus K a) r s =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j * ∑ e : E, K e r i * star (K e s j) := by
  have hswap :
      (∑ e : E, ∑ j : Fin n, ∑ i : Fin n,
        a i j * (K e r i * star (K e s j))) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ e : E,
        a i j * (K e r i * star (K e s j))) := by
    calc
      _ = ∑ e : E, ∑ i : Fin n, ∑ j : Fin n,
          a i j * (K e r i * star (K e s j)) := by
        apply Finset.sum_congr rfl
        intro e _
        exact Finset.sum_comm
      _ = ∑ i : Fin n, ∑ e : E, ∑ j : Fin n,
          a i j * (K e r i * star (K e s j)) := Finset.sum_comm
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ e : E,
          a i j * (K e r i * star (K e s j)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
  calc
    (cpMapKraus K a) r s =
        ∑ e : E, ∑ j : Fin n, ∑ i : Fin n,
          (K e r i * a i j) * star (K e s j) := by
      simp only [cpMapKraus, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Finset.sum_mul]
    _ = ∑ e : E, ∑ j : Fin n, ∑ i : Fin n,
        a i j * (K e r i * star (K e s j)) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ e : E,
        a i j * (K e r i * star (K e s j)) := hswap
    _ = ∑ i : Fin n, ∑ j : Fin n,
        a i j * ∑ e : E, K e r i * star (K e s j) := by
      simp only [Finset.mul_sum]

/-- Every completely positive finite complex-linear matrix map has a
constructively specified finite Kraus family, with equality on every matrix.
The family comes from the Gram factor of the map's actual Choi matrix. -/
theorem completelyPositive_kraus {n m : ℕ}
    (f : Mat n →ₗ[ℂ] Mat m) (hf : CompletelyPositive f) :
    ∃ K : (Fin n × Fin m) → Matrix (Fin m) (Fin n) ℂ,
      ∀ a : Mat n, f a = cpMapKraus K a := by
  obtain ⟨B, hB⟩ := completelyPositive_choi_gram f hf
  let K := gramKraus B
  refine ⟨K, ?_⟩
  intro a
  ext r s
  calc
    f a r s = ∑ i : Fin n, ∑ j : Fin n,
        a i j * choiMatrix f (i, r) (j, s) :=
      linearMap_entry_via_choi f a r s
    _ = ∑ i : Fin n, ∑ j : Fin n,
        a i j * ∑ e : Fin n × Fin m, K e r i * star (K e s j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hB, gramKraus_coeff]
    _ = (cpMapKraus K a) r s := (kraus_entry_by_choi K a r s).symm

/-- Matrix trace commutes with finite sums in the exact specification's notation. -/
private theorem tr_sum {n : ℕ} {E : Type*} [Fintype E]
    (g : E → Mat n) :
    tr (∑ e : E, g e) = ∑ e : E, tr (g e) := by
  simp only [tr, Matrix.trace, Matrix.diag_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- Cyclicity identifies the trace of every finite Kraus operation with
the trace paired against its summed Gram operator. -/
theorem kraus_trace_eq_gram_trace {n m : ℕ} {E : Type*} [Fintype E]
    (K : E → Matrix (Fin m) (Fin n) ℂ) (a : Mat n) :
    tr (cpMapKraus K a) =
      tr ((∑ e : E, (K e)ᴴ * K e) * a) := by
  calc
    tr (cpMapKraus K a) =
        ∑ e : E, tr (K e * a * (K e)ᴴ) := by
      simpa only [cpMapKraus] using
        (tr_sum (fun e : E => K e * a * (K e)ᴴ))
    _ = ∑ e : E, tr (((K e)ᴴ * K e) * a) := by
      apply Finset.sum_congr rfl
      intro e _
      exact Matrix.trace_mul_cycle (K e) a (K e)ᴴ
    _ = tr ((∑ e : E, (K e)ᴴ * K e) * a) := by
      rw [Finset.sum_mul]
      exact (tr_sum (fun e : E => ((K e)ᴴ * K e) * a)).symm

/-- Pairing with a matrix unit recovers the opposite matrix entry. -/
private theorem tr_mul_single {n : ℕ} (a : Mat n) (i j : Fin n) :
    tr (a * Matrix.single i j (1 : ℂ)) = a j i := by
  change (∑ k : Fin n, (a * Matrix.single i j (1 : ℂ)) k k) = a j i
  calc
    (∑ k : Fin n, (a * Matrix.single i j (1 : ℂ)) k k) =
        (a * Matrix.single i j (1 : ℂ)) j j := by
      apply Finset.sum_eq_single j
      · intro k _ hk
        exact Matrix.mul_single_apply_of_ne (1 : ℂ) i j k k hk a
      · intro h
        exact False.elim (h (Finset.mem_univ j))
    _ = a j i := by
      simp only [Matrix.mul_single_apply_same, mul_one]

/-- The full trace pairing distinguishes every matrix from the identity. -/
theorem matrix_eq_one_of_trace_pairing {n : ℕ} (a : Mat n)
    (h : ∀ b : Mat n, tr (a * b) = tr b) : a = 1 := by
  ext i j
  have hentry : a i j = tr (Matrix.single j i (1 : ℂ)) := by
    simpa only [tr_mul_single] using h (Matrix.single j i (1 : ℂ))
  by_cases hij : i = j
  · subst j
    simpa [tr, Matrix.one_apply] using hentry
  · have hzero : tr (Matrix.single j i (1 : ℂ)) = 0 :=
      Matrix.trace_single_eq_of_ne j i (1 : ℂ) (Ne.symm hij)
    rw [hzero] at hentry
    simpa [Matrix.one_apply, hij] using hentry

/-- Trace preservation of a finite Kraus family forces its full
completeness equation. This conclusion is derived from all input matrices. -/
theorem kraus_complete_of_trace_preserving {n m : ℕ} {E : Type*} [Fintype E]
    (K : E → Matrix (Fin m) (Fin n) ℂ)
    (hTP : ∀ a : Mat n, tr (cpMapKraus K a) = tr a) :
    (∑ e : E, (K e)ᴴ * K e : Mat n) = 1 := by
  apply matrix_eq_one_of_trace_pairing
  intro a
  exact (kraus_trace_eq_gram_trace K a).symm.trans (hTP a)

/-- Channel dilation retains the same linear map on every matrix input. -/
def ChannelDilationGoal : Prop :=
  ∀ (n m : ℕ), 0 < n → 0 < m → ∀ f : Mat n →ₗ[ℂ] Mat m,
    CompletelyPositive f → (∀ a, tr (f a) = tr a) →
    ∃ (r : ℕ) (u : Matrix (Fin m × Fin r) (Fin n) ℂ),
      0 < r ∧ u.conjTranspose * u = 1 ∧
      ∀ a i j, f a i j = ∑ k, (u * a * u.conjTranspose) (i,k) (j,k)

/-- Every finite trace-preserving completely positive linear map is the
partial trace of an explicitly constructed positive-size isometric dilation.
The statement is copied without an additional hypothesis from the specification. -/
theorem channelDilationGoal : ChannelDilationGoal := by
  intro n m hn hm f hCP hTP
  obtain ⟨K, hK⟩ := completelyPositive_kraus f hCP
  have hKTP : ∀ a : Mat n, tr (cpMapKraus K a) = tr a := by
    intro a
    rw [← hK a]
    exact hTP a
  have hKcomplete :
      (∑ e : Fin n × Fin m, (K e)ᴴ * K e : Mat n) = 1 :=
    kraus_complete_of_trace_preserving K hKTP
  let r : ℕ := Fintype.card (Fin n × Fin m)
  let ξ : Fin r ≃ (Fin n × Fin m) :=
    (Fintype.equivFin (Fin n × Fin m)).symm
  let L : Fin r → Matrix (Fin m) (Fin n) ℂ := fun k => K (ξ k)
  have hr : 0 < r := by
    dsimp [r]
    apply Fintype.card_pos_iff.mpr
    exact ⟨(⟨0, hn⟩, ⟨0, hm⟩)⟩
  have hLcomplete : (∑ k : Fin r, (L k)ᴴ * L k : Mat n) = 1 := by
    change (∑ k : Fin r, (K (ξ k))ᴴ * K (ξ k) : Mat n) = 1
    exact (Equiv.sum_comp ξ
      (fun e : Fin n × Fin m => (K e)ᴴ * K e)).trans hKcomplete
  refine ⟨r, stinespringV L, hr, stinespring_isometry L hLcomplete, ?_⟩
  intro a i j
  calc
    f a i j = (cpMapKraus K a) i j :=
      congrArg (fun b : Mat m => b i j) (hK a)
    _ = (cpMapKraus L a) i j := by
      simp only [cpMapKraus, Matrix.sum_apply]
      change (∑ e : Fin n × Fin m, (K e * a * (K e)ᴴ) i j) =
        (∑ k : Fin r, (K (ξ k) * a * (K (ξ k))ᴴ) i j)
      exact (Equiv.sum_comp ξ (fun e => (K e * a * (K e)ᴴ) i j)).symm
    _ = ∑ k : Fin r, (stinespringV L * a * (stinespringV L)ᴴ) (i,k) (j,k) := by
      simpa only [partialTraceAncilla, Matrix.of_apply] using
        congrArg (fun b : Mat m => b i j) (stinespring_dilates L a)

/-- Each outcome of an arbitrary finite completely positive instrument has
a finite Kraus family obtained from the actual operation's Choi matrix. -/
noncomputable def instrumentKraus {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y)) (y : Y) :
    (Fin n × Fin m) → Matrix (Fin m) (Fin n) ℂ :=
  Classical.choose (completelyPositive_kraus (branch y) (hCP y))

/-- The selected finite Kraus family agrees with the named instrument branch
for every input matrix, including arbitrary non-Hermitian matrices. -/
theorem instrumentKraus_realizes {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y)) (y : Y) (a : Mat n) :
    branch y a = cpMapKraus (instrumentKraus branch hCP y) a :=
  (Classical.choose_spec (completelyPositive_kraus (branch y) (hCP y))) a

/-- The retained classical outcome and the unobserved Kraus index share one
record register. No outcome-dependent environment is silently discarded. -/
def instrumentJointKraus {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y)) :
    (Y × (Fin n × Fin m)) → Matrix (Fin m) (Fin n) ℂ :=
  fun e => instrumentKraus branch hCP e.1 e.2

/-- Forgetting the complete outcome and Kraus record gives precisely the
nonselective sum of the original operations, on every matrix input. -/
theorem instrumentJointKraus_total {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y)) (a : Mat n) :
    cpMapKraus (instrumentJointKraus branch hCP) a =
      ∑ y : Y, branch y a := by
  unfold cpMapKraus
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  change cpMapKraus (instrumentKraus branch hCP y) a = branch y a
  exact (instrumentKraus_realizes branch hCP y a).symm

/-- Trace preservation of the total instrument yields completeness of its
one shared Kraus family, without a premise containing that completeness. -/
theorem instrumentJointKraus_complete {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (hTP : ∀ a : Mat n, tr (∑ y : Y, branch y a) = tr a) :
    (∑ e : Y × (Fin n × Fin m),
      (instrumentJointKraus branch hCP e)ᴴ * instrumentJointKraus branch hCP e :
      Mat n) = 1 := by
  apply kraus_complete_of_trace_preserving
  intro a
  rw [instrumentJointKraus_total]
  exact hTP a

/-- The shared, fully recorded dilation is an isometry by the original
instrument's trace-preserving law. -/
theorem instrumentJointKraus_isometry {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (hTP : ∀ a : Mat n, tr (∑ y : Y, branch y a) = tr a) :
    ((stinespringV (instrumentJointKraus branch hCP))ᴴ *
        stinespringV (instrumentJointKraus branch hCP) : Mat n) = 1 := by
  exact stinespring_isometry _ (instrumentJointKraus_complete branch hCP hTP)

/-- Measurement of a retained outcome label, followed by discarding only its
hidden Kraus coordinate, gives the original selective operation on every input. -/
theorem instrumentJointKraus_branch {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (a : Mat n) (y : Y) :
    (∑ z : Fin n × Fin m,
      recordedOutcome (y,z)
        (stinespringV (instrumentJointKraus branch hCP) * a *
          (stinespringV (instrumentJointKraus branch hCP))ᴴ)) =
        branch y a := by
  calc
    (∑ z : Fin n × Fin m,
      recordedOutcome (y,z)
        (stinespringV (instrumentJointKraus branch hCP) * a *
          (stinespringV (instrumentJointKraus branch hCP))ᴴ)) =
        ∑ z : Fin n × Fin m,
          instrumentJointKraus branch hCP (y,z) * a *
            (instrumentJointKraus branch hCP (y,z))ᴴ := by
      apply Finset.sum_congr rfl
      intro z _
      exact recordedOutcome_stinespring (instrumentJointKraus branch hCP) a (y,z)
    _ = branch y a := by
      change cpMapKraus (instrumentKraus branch hCP y) a = branch y a
      exact (instrumentKraus_realizes branch hCP y a).symm

/-- Every finite completely positive instrument with a trace-preserving
nonselective sum has a common isometric record dilation. Each selective output,
its retained label and the nonselective output agree with the given instrument
for every matrix input. The record index is explicitly in the enlarged output. -/
theorem generalInstrumentRecordedRealization {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (hTP : ∀ a : Mat n, tr (∑ y : Y, branch y a) = tr a) :
    ∃ V : Matrix (Fin m × (Y × (Fin n × Fin m))) (Fin n) ℂ,
      Vᴴ * V = 1 ∧
      (∀ (a : Mat n) (y : Y),
        (∑ z : Fin n × Fin m, recordedOutcome (y,z) (V * a * Vᴴ)) =
          branch y a) ∧
      ∀ a : Mat n,
        (∑ e : Y × (Fin n × Fin m), recordedOutcome e (V * a * Vᴴ)) =
          ∑ y : Y, branch y a := by
  let K := instrumentJointKraus branch hCP
  refine ⟨stinespringV K, instrumentJointKraus_isometry branch hCP hTP, ?_, ?_⟩
  · intro a y
    exact instrumentJointKraus_branch branch hCP a y
  · intro a
    calc
      (∑ e : Y × (Fin n × Fin m),
          recordedOutcome e (stinespringV K * a * (stinespringV K)ᴴ)) =
          partialTraceAncilla (stinespringV K * a * (stinespringV K)ᴴ) :=
        recordedOutcome_sum _
      _ = cpMapKraus K a := (stinespring_dilates K a).symm
      _ = ∑ y : Y, branch y a := instrumentJointKraus_total branch hCP a

/-- A normalized finite density matrix has native positive semidefiniteness
and complex trace one. This carrier matches the specification's density
conditions through the established positivity equivalence. -/
abbrev InstrumentDensity (n : ℕ) :=
  {ρ : Mat n // ρ.PosSemidef ∧ tr ρ = 1}

/-- Every positive semidefinite finite matrix has nonnegative real trace. -/
theorem posSemidef_trace_re_nonneg {n : ℕ} (a : Mat n)
    (ha : a.PosSemidef) : 0 ≤ (tr a).re := by
  have hdiag : ∀ i : Fin n, 0 ≤ (a i i).re := by
    intro i
    have hi := ha.re_dotProduct_nonneg (Pi.single i (1 : ℂ))
    simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
      single_one_dotProduct, Matrix.col_apply] using hi
  change 0 ≤ Complex.reAddGroupHom (∑ i : Fin n, a i i)
  rw [map_sum]
  exact Finset.sum_nonneg (fun i _ => hdiag i)

/-- A positive semidefinite matrix has a real complex trace. -/
theorem posSemidef_trace_eq_ofReal {n : ℕ} (a : Mat n)
    (ha : a.PosSemidef) : tr a = ((tr a).re : ℂ) := by
  have hstar : star (tr a) = tr a := by
    calc
      star (tr a) = tr aᴴ := (Matrix.trace_conjTranspose a).symm
      _ = tr a := congrArg tr ha.1.eq
  have him : (tr a).im = 0 := by
    have h := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simpa only [Complex.ofReal_im] using him

/-- The operational probability of a retained outcome is the real trace
of its actual unnormalized branch, for a normalized input density. -/
noncomputable def instrumentWeight {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m) (ρ : InstrumentDensity n)
    (y : Y) : ℝ :=
  (tr (branch y ρ.val)).re

/-- Every outcome weight is nonnegative, derived from the completely
positive branch rather than inserted as an outcome-probability premise. -/
theorem instrumentWeight_nonneg {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y) :
    0 ≤ instrumentWeight branch ρ y := by
  have ha : (branch y ρ.val).PosSemidef := by
    rw [instrumentKraus_realizes branch hCP y ρ.val]
    exact cpMapKraus_posSemidef _ ρ.property.1
  exact posSemidef_trace_re_nonneg _ ha

/-- The branch weights of every normalized input sum to one for any finite
instrument whose nonselective sum preserves trace on every matrix. -/
theorem instrumentWeight_total {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hTP : ∀ a : Mat n, tr (∑ y : Y, branch y a) = tr a)
    (ρ : InstrumentDensity n) :
    (∑ y : Y, instrumentWeight branch ρ y) = 1 := by
  calc
    (∑ y : Y, instrumentWeight branch ρ y) =
        (tr (∑ y : Y, branch y ρ.val)).re := by
      change (∑ y : Y, Complex.reAddGroupHom (tr (branch y ρ.val))) =
        Complex.reAddGroupHom (tr (∑ y : Y, branch y ρ.val))
      rw [tr_sum, map_sum]
    _ = 1 := by
      rw [hTP, ρ.property.2]
      rfl

/-- A selective branch with a strictly positive outcome weight has a
normalized positive semidefinite conditional output state. -/
noncomputable def instrumentConditionalState {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y)
    (hp : 0 < instrumentWeight branch ρ y) : InstrumentDensity m := by
  let p := instrumentWeight branch ρ y
  let a := branch y ρ.val
  have ha : a.PosSemidef := by
    dsimp [a]
    rw [instrumentKraus_realizes branch hCP y ρ.val]
    exact cpMapKraus_posSemidef _ ρ.property.1
  have hreal : tr a = (p : ℂ) := by
    simpa only [p, a, instrumentWeight] using posSemidef_trace_eq_ofReal a ha
  have hscaled : (((p⁻¹ : ℝ) : ℂ) • a).PosSemidef :=
    posSemidef_real_smul_gen ha (le_of_lt (inv_pos.mpr hp))
  have htrace : tr (((p⁻¹ : ℝ) : ℂ) • a) = 1 := by
    simp only [tr, Matrix.trace_smul]
    change (((p⁻¹ : ℝ) : ℂ) * tr a) = 1
    rw [hreal, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hp)]
    rfl
  exact ⟨((p⁻¹ : ℝ) : ℂ) • a, hscaled, htrace⟩

/-- Multiplying the normalized conditional state by the actual outcome
probability recovers precisely the unnormalized selective branch. -/
theorem instrumentConditionalState_unscaled {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y)
    (hp : 0 < instrumentWeight branch ρ y) :
    (instrumentWeight branch ρ y : ℂ) •
      (instrumentConditionalState branch hCP ρ y hp).val =
        branch y ρ.val := by
  let p := instrumentWeight branch ρ y
  change (p : ℂ) • (((p⁻¹ : ℝ) : ℂ) • branch y ρ.val) = branch y ρ.val
  rw [smul_smul]
  have hscalar : (p : ℂ) * ((p⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hp)]
    rfl
  rw [hscalar, one_smul]

/-- Measurement of the actual retained record yields the same probability
as the corresponding abstract instrument branch. -/
theorem instrumentRecordedWeight {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y) :
    (tr (∑ z : Fin n × Fin m,
      recordedOutcome (y,z)
        (stinespringV (instrumentJointKraus branch hCP) * ρ.val *
          (stinespringV (instrumentJointKraus branch hCP))ᴴ))).re =
      instrumentWeight branch ρ y := by
  rw [instrumentJointKraus_branch]
  rfl

/-- The normalized state after a positive-probability record agrees exactly
with the selective branch, even when the input contains coherence. -/
theorem instrumentRecordedPostState {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y)
    (hp : 0 < instrumentWeight branch ρ y) :
    (instrumentWeight branch ρ y : ℂ) •
      (instrumentConditionalState branch hCP ρ y hp).val =
        ∑ z : Fin n × Fin m,
          recordedOutcome (y,z)
            (stinespringV (instrumentJointKraus branch hCP) * ρ.val *
              (stinespringV (instrumentJointKraus branch hCP))ᴴ) := by
  rw [instrumentJointKraus_branch]
  exact instrumentConditionalState_unscaled branch hCP ρ y hp

/-- A finite isometry has an explicit square-unitary extension on the
direct sum of its input and output coordinates. The first summand is the
fixed input embedding; the second contains all output and record coordinates. -/
def halmosSquareUnitary {n : ℕ} {Ω : Type*} [Fintype Ω]
    (V : Matrix Ω (Fin n) ℂ) : Matrix (Fin n ⊕ Ω) (Fin n ⊕ Ω) ℂ :=
  Matrix.fromBlocks (0 : Mat n) Vᴴ V (1 - V * Vᴴ)

/-- The explicit block extension is Hermitian for every rectangular matrix. -/
theorem halmosSquareUnitary_selfadjoint {n : ℕ} {Ω : Type*} [Fintype Ω]
    (V : Matrix Ω (Fin n) ℂ) :
    (halmosSquareUnitary V)ᴴ = halmosSquareUnitary V := by
  unfold halmosSquareUnitary
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_mul]

/-- The explicit block extension squares to the identity whenever its
rectangular input map is isometric. No completion or donor unitary is assumed. -/
theorem halmosSquareUnitary_mul_self {n : ℕ} {Ω : Type*} [Fintype Ω]
    (V : Matrix Ω (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    halmosSquareUnitary V * halmosSquareUnitary V = 1 := by
  let P : Matrix Ω Ω ℂ := V * Vᴴ
  let D : Matrix Ω Ω ℂ := 1 - P
  have hP : P * P = P := by
    dsimp only [P]
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hD : D * D = D := by
    dsimp only [D]
    calc
      (1 - P) * (1 - P) = (1 - P) * 1 - (1 - P) * P := by
        rw [mul_sub]
      _ = (1 - P) - (P - P * P) := by
        rw [mul_one, sub_mul, one_mul]
      _ = (1 - P) - (P - P) := by rw [hP]
      _ = 1 - P := by rw [sub_self, sub_zero]
  have hVD : Vᴴ * D = 0 := by
    dsimp only [D, P]
    calc
      Vᴴ * (1 - V * Vᴴ) = Vᴴ - Vᴴ * (V * Vᴴ) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
      _ = Vᴴ - (Vᴴ * V) * Vᴴ := by
        rw [Matrix.mul_assoc]
      _ = Vᴴ - Vᴴ := by rw [hV, Matrix.one_mul]
      _ = 0 := sub_self _
  have hDV : D * V = 0 := by
    dsimp only [D, P]
    calc
      (1 - V * Vᴴ) * V = V - (V * Vᴴ) * V := by
        rw [Matrix.sub_mul, Matrix.one_mul]
      _ = V - V * (Vᴴ * V) := by
        rw [Matrix.mul_assoc]
      _ = V - V := by rw [hV, Matrix.mul_one]
      _ = 0 := sub_self _
  have hbottom : P + D * D = 1 := by
    rw [hD]
    dsimp only [D]
    abel
  calc
    halmosSquareUnitary V * halmosSquareUnitary V =
        Matrix.fromBlocks (Vᴴ * V) (Vᴴ * D) (D * V) (P + D * D) := by
      change Matrix.fromBlocks (0 : Mat n) Vᴴ V D *
          Matrix.fromBlocks (0 : Mat n) Vᴴ V D =
          Matrix.fromBlocks (Vᴴ * V) (Vᴴ * D) (D * V) (P + D * D)
      rw [Matrix.fromBlocks_multiply]
      dsimp only [P]
      simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
    _ = Matrix.fromBlocks 1 0 0 1 := by
      rw [hV, hVD, hDV, hbottom]
    _ = 1 := Matrix.fromBlocks_one

/-- The extension is a square unitary, not merely an isometry: both
adjoint equations hold on the entire direct-sum carrier. -/
theorem halmosSquareUnitary_unitary {n : ℕ} {Ω : Type*} [Fintype Ω]
    (V : Matrix Ω (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    (halmosSquareUnitary V)ᴴ * halmosSquareUnitary V = 1 ∧
      halmosSquareUnitary V * (halmosSquareUnitary V)ᴴ = 1 := by
  have hstar := halmosSquareUnitary_selfadjoint V
  have hsq := halmosSquareUnitary_mul_self V hV
  constructor
  · rw [hstar]
    exact hsq
  · rw [hstar]
    exact hsq

/-- A fixed input-basis column of the square unitary is the original
isometry column in the output-and-record block. -/
theorem halmosSquareUnitary_input_column {n : ℕ} {Ω : Type*} [Fintype Ω]
    (V : Matrix Ω (Fin n) ℂ) (i : Ω) (j : Fin n) :
    halmosSquareUnitary V (Sum.inr i) (Sum.inl j) = V i j := rfl

/-- An input matrix occupies only the fixed input summand of the square
unitary's carrier. All added output-and-record coordinates start at zero. -/
def squareUnitaryInputBlock {n : ℕ} {Ω : Type*} [Fintype Ω]
    (a : Mat n) : Matrix (Fin n ⊕ Ω) (Fin n ⊕ Ω) ℂ :=
  Matrix.fromBlocks a 0 0 0

/-- Unitary conjugation of the fixed input block has only one nonzero
block: the exact all-input isometric output including the record register. -/
theorem halmosSquareUnitary_input_sandwich {n : ℕ} {Ω : Type*} [Fintype Ω]
    (V : Matrix Ω (Fin n) ℂ) (a : Mat n) :
    halmosSquareUnitary V * squareUnitaryInputBlock (Ω := Ω) a *
        (halmosSquareUnitary V)ᴴ =
      Matrix.fromBlocks 0 0 0 (V * a * Vᴴ) := by
  have hfirst :
      halmosSquareUnitary V * squareUnitaryInputBlock (Ω := Ω) a =
        Matrix.fromBlocks 0 0 (V * a) 0 := by
    dsimp only [halmosSquareUnitary, squareUnitaryInputBlock]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  calc
    halmosSquareUnitary V * squareUnitaryInputBlock (Ω := Ω) a *
        (halmosSquareUnitary V)ᴴ =
        Matrix.fromBlocks 0 0 (V * a) 0 * halmosSquareUnitary V := by
      rw [halmosSquareUnitary_selfadjoint, hfirst]
    _ = Matrix.fromBlocks 0 0 0 (V * a * Vᴴ) := by
      dsimp only [halmosSquareUnitary]
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- Restricting the square-unitary output to its record-bearing summand
recovers the exact Stinespring output for every input matrix. -/
theorem halmosSquareUnitary_outputBlock {n : ℕ} {Ω : Type*} [Fintype Ω]
    (V : Matrix Ω (Fin n) ℂ) (a : Mat n) :
    (halmosSquareUnitary V * squareUnitaryInputBlock (Ω := Ω) a *
      (halmosSquareUnitary V)ᴴ).toBlocks₂₂ = V * a * Vᴴ := by
  rw [halmosSquareUnitary_input_sandwich]
  exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _

/-- Every completely positive finite instrument has one genuine square
unitary on a fixed input/output direct-sum enlargement. Measurement of
the record after applying that unitary gives every selective branch on
all matrix inputs, and forgetting every label gives exactly the total
operation. No separate output-matching premise is used. -/
theorem generalInstrumentSquareUnitaryRealization
    {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (hTP : ∀ a : Mat n, tr (∑ y : Y, branch y a) = tr a) :
    ∃ U : Matrix
        (Fin n ⊕ (Fin m × (Y × (Fin n × Fin m))))
        (Fin n ⊕ (Fin m × (Y × (Fin n × Fin m)))) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ (a : Mat n) (y : Y),
        (∑ z : Fin n × Fin m,
          recordedOutcome (y,z)
            (U * squareUnitaryInputBlock a * Uᴴ).toBlocks₂₂) = branch y a) ∧
      ∀ a : Mat n,
        (∑ e : Y × (Fin n × Fin m),
          recordedOutcome e
            (U * squareUnitaryInputBlock a * Uᴴ).toBlocks₂₂) =
          ∑ y : Y, branch y a := by
  let K := instrumentJointKraus branch hCP
  let V := stinespringV K
  have hV : Vᴴ * V = 1 :=
    instrumentJointKraus_isometry branch hCP hTP
  have hunitary := halmosSquareUnitary_unitary V hV
  refine ⟨halmosSquareUnitary V, ?_, ?_, ?_, ?_⟩
  · ext i j
    have he := congrFun (congrFun hunitary.1 i) j
    by_cases hij : i = j
    · simpa only [Matrix.one_apply, if_pos hij] using he
    · simpa only [Matrix.one_apply, if_neg hij] using he
  · ext i j
    have he := congrFun (congrFun hunitary.2 i) j
    by_cases hij : i = j
    · simpa only [Matrix.one_apply, if_pos hij] using he
    · simpa only [Matrix.one_apply, if_neg hij] using he
  · intro a y
    rw [halmosSquareUnitary_outputBlock]
    exact instrumentJointKraus_branch branch hCP a y
  · intro a
    rw [halmosSquareUnitary_outputBlock]
    calc
      (∑ e : Y × (Fin n × Fin m),
          recordedOutcome e (V * a * Vᴴ)) =
          partialTraceAncilla (V * a * Vᴴ) :=
        recordedOutcome_sum _
      _ = cpMapKraus K a := (stinespring_dilates K a).symm
      _ = ∑ y : Y, branch y a :=
        instrumentJointKraus_total branch hCP a

/-- The square unitary implementing a named instrument is constructed from
its actual Choi-derived joint Kraus isometry. -/
def instrumentSquareUnitary {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y)) :
    Matrix
      (Fin n ⊕ (Fin m × (Y × (Fin n × Fin m))))
      (Fin n ⊕ (Fin m × (Y × (Fin n × Fin m)))) ℂ :=
  halmosSquareUnitary (stinespringV (instrumentJointKraus branch hCP))

/-- The square implementation has both unitary laws whenever the total
instrument is trace preserving on every source matrix. -/
theorem instrumentSquareUnitary_unitary {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (hTP : ∀ a : Mat n, tr (∑ y : Y, branch y a) = tr a) :
    (instrumentSquareUnitary branch hCP)ᴴ *
        instrumentSquareUnitary branch hCP = 1 ∧
      instrumentSquareUnitary branch hCP *
        (instrumentSquareUnitary branch hCP)ᴴ = 1 := by
  unfold instrumentSquareUnitary
  have hunitary := halmosSquareUnitary_unitary _
    (instrumentJointKraus_isometry branch hCP hTP)
  constructor
  · ext i j
    have he := congrFun (congrFun hunitary.1 i) j
    by_cases hij : i = j
    · simpa only [Matrix.one_apply, if_pos hij] using he
    · simpa only [Matrix.one_apply, if_neg hij] using he
  · ext i j
    have he := congrFun (congrFun hunitary.2 i) j
    by_cases hij : i = j
    · simpa only [Matrix.one_apply, if_pos hij] using he
    · simpa only [Matrix.one_apply, if_neg hij] using he

/-- The square unitary followed by the record measurement has the original
selective outcome weight for every normalized input density. -/
theorem instrumentSquareUnitary_record_weight {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y) :
    (tr (∑ z : Fin n × Fin m,
      recordedOutcome (y,z)
        (instrumentSquareUnitary branch hCP *
          squareUnitaryInputBlock ρ.val *
          (instrumentSquareUnitary branch hCP)ᴴ).toBlocks₂₂)).re =
      instrumentWeight branch ρ y := by
  unfold instrumentSquareUnitary
  rw [halmosSquareUnitary_outputBlock]
  exact instrumentRecordedWeight branch hCP ρ y

/-- For every strictly positive outcome weight, the normalized conditional
state after the square unitary and record measurement equals the source
instrument's post-state. The zero-weight case is not falsely normalized. -/
theorem instrumentSquareUnitary_record_postState
    {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y)
    (hp : 0 < instrumentWeight branch ρ y) :
    (instrumentWeight branch ρ y : ℂ) •
        (instrumentConditionalState branch hCP ρ y hp).val =
      ∑ z : Fin n × Fin m, recordedOutcome (y,z)
        (instrumentSquareUnitary branch hCP *
          squareUnitaryInputBlock ρ.val *
          (instrumentSquareUnitary branch hCP)ᴴ).toBlocks₂₂ := by
  unfold instrumentSquareUnitary
  rw [halmosSquareUnitary_outputBlock]
  exact instrumentRecordedPostState branch hCP ρ y hp

/-- A finite positive semidefinite matrix with zero real trace is the
zero matrix. The full matrix, including off-diagonal entries, vanishes. -/
theorem posSemidef_eq_zero_of_trace_re_zero {n : ℕ} (a : Mat n)
    (ha : a.PosSemidef) (htrace : (tr a).re = 0) : a = 0 := by
  have hdiag : ∀ i : Fin n, 0 ≤ (a i i).re := by
    intro i
    have hi := ha.re_dotProduct_nonneg (Pi.single i (1 : ℂ))
    simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
      single_one_dotProduct, Matrix.col_apply] using hi
  have hsum : (∑ i : Fin n, (a i i).re) = 0 := by
    calc
      (∑ i : Fin n, (a i i).re) = (tr a).re := by
        change (∑ i : Fin n, Complex.reAddGroupHom (a i i)) =
          Complex.reAddGroupHom (∑ i : Fin n, a i i)
        rw [map_sum]
      _ = 0 := htrace
  have hdiag_zero (i : Fin n) : (a i i).re = 0 := by
    exact ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hdiag j)).mp hsum)
        i (Finset.mem_univ i)
  ext i j
  have hquadratic :
      star (Pi.single j (1 : ℂ)) ⬝ᵥ
        (a *ᵥ Pi.single j (1 : ℂ)) = 0 := by
    apply Complex.ext
    · simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
        single_one_dotProduct, Matrix.col_apply, Complex.zero_re] using hdiag_zero j
    · have him := generalPSD_hermitian_im_zero ha.1 (Pi.single j (1 : ℂ))
      simpa only [Complex.zero_im] using him
  have hcolumn := (ha.dotProduct_mulVec_zero_iff (Pi.single j (1 : ℂ))).mp
    hquadratic
  have hentry := congrFun hcolumn i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using hentry

/-- A branch of a finite completely positive instrument with zero outcome
weight yields the zero unnormalized output matrix, rather than a fabricated
conditional density. -/
theorem instrumentBranch_zero_of_weight_zero {n m : ℕ} {Y : Type*}
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y)
    (hzero : instrumentWeight branch ρ y = 0) :
    branch y ρ.val = 0 := by
  have hpositive : (branch y ρ.val).PosSemidef := by
    rw [instrumentKraus_realizes branch hCP y ρ.val]
    exact cpMapKraus_posSemidef _ ρ.property.1
  apply posSemidef_eq_zero_of_trace_re_zero _ hpositive
  exact hzero

/-- The explicit square unitary also assigns the zero unnormalized matrix
to an impossible recorded outcome, with its complete Kraus record summed. -/
theorem instrumentSquareUnitary_zeroWeight
    {n m : ℕ} {Y : Type*} [Fintype Y]
    (branch : Y → Mat n →ₗ[ℂ] Mat m)
    (hCP : ∀ y, CompletelyPositive (branch y))
    (ρ : InstrumentDensity n) (y : Y)
    (hzero : instrumentWeight branch ρ y = 0) :
    (∑ z : Fin n × Fin m,
      recordedOutcome (y,z)
        (instrumentSquareUnitary branch hCP *
          squareUnitaryInputBlock ρ.val *
          (instrumentSquareUnitary branch hCP)ᴴ).toBlocks₂₂) =
      (0 : Mat m) := by
  unfold instrumentSquareUnitary
  rw [halmosSquareUnitary_outputBlock]
  rw [instrumentJointKraus_branch]
  exact instrumentBranch_zero_of_weight_zero branch hCP ρ y hzero

end OperatorKO7.Meta.BoundaryObserver.ReconstructionRecovery
